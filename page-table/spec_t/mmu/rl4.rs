use vstd::prelude::*;
use crate::spec_t::mmu::common::*;
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::spec_t::hardware::{ Core, PageDirectoryEntry, GhostPageDirectoryEntry, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ aligned, Flags, MemRegion, PageTableEntry, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, bitmask_inc };

verus! {

// This file contains refinement layer 4 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.

pub struct State {
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<PTWalk>>,
    /// Translation caches
    pub cache: Map<Core, Set<CacheEntry>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
}

// TODO:
// invariant on walks and cache:
// - The PDEs stored in `Partial*` walks are always directories

// TODO: Probably add transition that arbitrarily changes dirty/accessed bits
// oh no
// this requires knowledge of which memory addresses might be used as paging structure
// and not just reachability from cr3 but from the translation caches and inflight walks too
//
// Problem with separating page table memory and other memory by construction:
// It could happen that we deallocate a frame but it's still used as paging structure (e.g.
// inflight walk or cached). That would mean the accessed and dirty bits can randomly change, if
// that memory was reused for something else. (not entirely true if we really have fully disjoint
// regions)

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0
    // .. evicts corresponding entries from the translation caches, ..
    // Note that per Intel Manual 3A, 4.10.4.1:
    // "INVLPG also invalidates all entries in all paging-structure caches associated with the
    // current PCID, regardless of the linear addresses to which they correspond."
    &&& pre.cache[core].is_empty()
    // .. and cancels inflight walks.
    &&& pre.walks[core].is_empty()
    // We assume that INVLPG has the same behavior on inflight walks as on paging-structure caches.
    // TODO: Is this a reasonable assumption? Maybe not.

    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
}


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial1 || walk is Partial2 || walk is Partial3

    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].insert(walk.as_cache_entry()))
}

pub open spec fn step_CacheUse(pre: State, post: State, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.cache[core].contains(e)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(e.as_ptwalk()))
}

pub open spec fn step_CacheEvict(pre: State, post: State, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.cache[core].contains(e)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].remove(e))
    &&& post.walks == pre.walks
}


// ---- Non-atomic page table walks ----

pub open spec fn step_Walk1(pre: State, post: State, core: Core, va: usize, lbl: Lbl) -> bool {
    let l0e = PageDirectoryEntry {
        entry: pre.pt_mem@[add(pre.pt_mem.pml4(), l0_bits!(va as u64) as usize)] as u64,
        layer: Ghost(0),
    };
    let flags = Flags::from_GPDE(l0e@);
    let walk = match l0e@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial1(va, l0e, flags),
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid(va),
        _                                         => arbitrary(), // No page mappings here
    };
    &&& lbl is Tau

    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
}

pub open spec fn step_Walk2(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    let PTWalk::Partial1(va, l0e, flags) = walk else { arbitrary() };
    let l1e = PageDirectoryEntry {
        entry: pre.pt_mem@[add(l0e@->Directory_addr, l1_bits!(va as u64) as usize)] as u64,
        layer: Ghost(1),
    };
    let new_walk = match l1e@ {
        GhostPageDirectoryEntry::Directory { .. } => {
            PTWalk::Partial2(va, l0e, l1e, flags.combine(Flags::from_GPDE(l1e@)))
        },
        GhostPageDirectoryEntry::Page { addr, .. } => {
            let pte = PageTableEntry {
                frame: MemRegion { base: addr as nat, size: L1_ENTRY_SIZE as nat },
                flags: flags.combine(Flags::from_GPDE(l1e@)),
            };
            PTWalk::Valid(va, pte)
        },
        GhostPageDirectoryEntry::Empty => PTWalk::Invalid(va),
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial1

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
}

pub open spec fn step_Walk3(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    let PTWalk::Partial2(va, l0e, l1e, flags) = walk else { arbitrary() };
    let l2e = PageDirectoryEntry {
        entry: pre.pt_mem@[add(l1e@->Directory_addr, l2_bits!(va as u64) as usize)] as u64,
        layer: Ghost(2),
    };
    let new_walk = match l2e@ {
        GhostPageDirectoryEntry::Directory { .. } => {
            PTWalk::Partial3(va, l0e, l1e, l2e, flags.combine(Flags::from_GPDE(l2e@)))
        },
        GhostPageDirectoryEntry::Page { addr, .. } => {
            let pte = PageTableEntry {
                frame: MemRegion { base: addr as nat, size: L2_ENTRY_SIZE as nat },
                flags: flags.combine(Flags::from_GPDE(l2e@)),
            };
            PTWalk::Valid(va, pte)
        },
        GhostPageDirectoryEntry::Empty => PTWalk::Invalid(va),
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial2

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
}

pub open spec fn step_Walk4(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    let PTWalk::Partial3(va, l0e, l1e, l2e, flags) = walk else { arbitrary() };
    let l3e = PageDirectoryEntry {
        entry: pre.pt_mem@[add(l2e@->Directory_addr, l3_bits!(va as u64) as usize)] as u64,
        layer: Ghost(3),
    };
    let new_walk = match l3e@ {
        GhostPageDirectoryEntry::Page { addr, .. } => {
            let pte = PageTableEntry {
                frame: MemRegion { base: addr as nat, size: L3_ENTRY_SIZE as nat },
                flags: flags.combine(Flags::from_GPDE(l3e@)),
            };
            PTWalk::Valid(va, pte)
        },
        GhostPageDirectoryEntry::Directory { .. }
        | GhostPageDirectoryEntry::Empty => PTWalk::Invalid(va),
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial3

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
}

pub open spec fn step_WalkCancel(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))
}

/// We model page table walks such that the result of a walk can be used multiple times, i.e.
/// "completing" the walk multiple times.
pub open spec fn step_Walk(pre: State, post: State, lbl: Lbl) -> bool {
    let walk = match lbl {
        Lbl::Walk(_, va, Some(pte)) => PTWalk::Valid(va, pte),
        Lbl::Walk(_, va, None) => PTWalk::Invalid(va),
        _ => arbitrary(),
    };
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& pre.walks[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
// TODO: Double-check to make sure it's a faithful adaptation
// TODO: we don't model atomics, so technically the user-space threads cannot synchronize
// TODO: max physical size?
/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& aligned(addr as nat, 8)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
}

pub open spec fn step_Writeback(pre: State, post: State, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem@ == pre.pt_mem@.insert(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
}

pub open spec fn get_first_aux<A,B>(s: Seq<(A, B)>, i: int, a: A) -> Option<B>
    decreases s.len() - i
{
    if i >= s.len() {
        None
    } else {
        if s[i].0 == a {
            Some(s[i].1)
        } else {
            get_first_aux(s, i + 1, a)
        }
    }
}

pub open spec fn get_first<A,B>(s: Seq<(A, B)>, a: A) -> Option<B> {
    get_first_aux(s, 0, a)
}

pub open spec fn step_Read(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& aligned(addr as nat, 8)
    &&& value == match get_first(pre.sbuf[core], addr) {
        Some(v) => v,
        None    => pre.pt_mem@[addr],
    }

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
}

pub enum Step {
    // Mixed
    Invlpg { },
    // Translation caching
    CacheFill { core: Core, walk: PTWalk },
    CacheUse { core: Core, e: CacheEntry },
    CacheEvict { core: Core, e: CacheEntry },
    // Non-atomic page table walks
    Walk1 { core: Core, va: usize },
    Walk2 { core: Core, walk: PTWalk },
    Walk3 { core: Core, walk: PTWalk },
    Walk4 { core: Core, walk: PTWalk },
    WalkCancel { core: Core, walk: PTWalk },
    Walk { },
    // TSO
    Write { },
    Writeback { core: Core },
    Read { },
    Barrier { },
}

pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg { }                => step_Invlpg(pre, post, lbl),
        Step::CacheFill { core, walk }  => step_CacheFill(pre, post, core, walk, lbl),
        Step::CacheUse { core, e }      => step_CacheUse(pre, post, core, e, lbl),
        Step::CacheEvict { core, e }    => step_CacheEvict(pre, post, core, e, lbl),
        Step::Walk1 { core, va }        => step_Walk1(pre, post, core, va, lbl),
        Step::Walk2 { core, walk }      => step_Walk2(pre, post, core, walk, lbl),
        Step::Walk3 { core, walk }      => step_Walk3(pre, post, core, walk, lbl),
        Step::Walk4 { core, walk }      => step_Walk4(pre, post, core, walk, lbl),
        Step::WalkCancel { core, walk } => step_WalkCancel(pre, post, core, walk, lbl),
        Step::Walk { }                  => step_Walk(pre, post, lbl),
        Step::Write { }                 => step_Write(pre, post, lbl),
        Step::Writeback { core }        => step_Writeback(pre, post, core, lbl),
        Step::Read { }                  => step_Read(pre, post, lbl),
        Step::Barrier { }               => step_Barrier(pre, post, lbl),
    }
}

} // verus!
