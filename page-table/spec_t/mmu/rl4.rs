use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::spec_t::hardware::{ Core, PageDirectoryEntry, GhostPageDirectoryEntry, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ aligned, bitmask_inc, bit };

verus! {

/// Bits 5 and 6 (dirty, access) set to 1
pub const MASK_DIRTY_ACCESS: usize = (bit!(5) | bit!(6)) as usize;

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
    /// Addresses that have been used in a page table walk
    /// TODO: This can probably be at least partially reset in invlpg.
    pub used_addrs: Set<usize>,
    /// History variables. These are not allowed to influence transitions in any way. Neither in
    /// enabling conditions nor in how the state is updated.
    pub hist: History,
}

pub struct History {
    /// All partial and complete page table walks since the last invlpg
    pub walks: Map<Core, Set<PTWalk>>,
    /// All writes that happened since the most recent invlpg.
    pub writes: Set<usize>,
}

impl State {
    /// This predicate is true whenever `value` is a value that might be read from the address
    /// `addr` on core `core`.
    ///
    /// We write this as a predicate rather than a function to specify the nondeterministic choice
    /// of the dirty and accessed bits. We could make an arbitrary choice for the bits in this
    /// function but that approach causes problems with the refinement, since the arbitrary choice
    /// must depend on the state, address and core.
    ///
    /// FIXME: I changed this to always keep dirty/accessed bits nondeterministic rather than
    /// making it depend on `used_addrs`. If we keep the assumption that page table memory and user
    /// memory are disjoint, this is fine, otherwise we need to change it.
    /// Changing it shouldn't be too hard but it's probably worth first thinking a bit more about
    /// whether or not to give up that assumption. If we keep it, we need to discuss what exactly
    /// things mean. Currently the idea of the MMU state machines is that they model accesses to
    /// physical memory. We'd have to think about how to link different labels. (might not actually
    /// be an issue but should think it through)
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, value: usize) -> bool {
        let val = match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem@[addr],
        };
        value & MASK_DIRTY_ACCESS == val & MASK_DIRTY_ACCESS
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn inv(self) -> bool {
        // TODO: something something valid cores
        forall|core| self.walks[core].subset_of(#[trigger] self.hist.walks[core])
    }
}

// TODO:
// invariant on walks and cache:
// - The PDEs stored in `Partial` walks are always directories
// - Length of paths in `Partial` walks in `walks` is always 1, 2 or 3
// - Length of paths in `Valid` walks in `walks` is always 2, 3 or 4
// - `Valid` walks always have a path made of directories, with a final page entry
// - Length of paths in cache entries in `cache` is always 1, 2 or 3

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
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks.insert(core, set![])
    &&& post.hist.writes === set![]
}


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial

    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].insert(walk.as_cache_entry()))
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_CacheUse(pre: State, post: State, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.cache[core].contains(e)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(e.as_ptwalk()))
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_CacheEvict(pre: State, post: State, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.cache[core].contains(e)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].remove(e))
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}


// ---- Non-atomic page table walks ----

pub open spec fn step_Walk1(pre: State, post: State, core: Core, va: usize, l0ev: usize, lbl: Lbl) -> bool {
    let addr = add(pre.pt_mem.pml4(), l0_bits!(va as u64) as usize);
    let l0e = (addr, PageDirectoryEntry { entry: l0ev as u64, layer: Ghost(0) });
    let walk = match l0e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va },
        _                                         => arbitrary(), // No page mappings here
    };
    &&& lbl is Tau

    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?
    &&& pre.read_from_mem_tso(core, addr, l0ev)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk))
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_Walk2(pre: State, post: State, core: Core, walk: PTWalk, l1ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0];
    let addr = add(l0e.1@->Directory_addr, l1_bits!(va as u64) as usize);
    let l1e = (addr, PageDirectoryEntry { entry: l1ev as u64, layer: Ghost(1) });
    let new_walk = match l1e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va },
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 1
    &&& pre.read_from_mem_tso(core, addr, l1ev)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_Walk3(pre: State, post: State, core: Core, walk: PTWalk, l2ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1];
    let addr = add(l1e.1@->Directory_addr, l2_bits!(va as u64) as usize);
    let l2e = (addr, PageDirectoryEntry { entry: l2ev as u64, layer: Ghost(2) });
    let new_walk = match l2e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va },
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 2
    &&& pre.read_from_mem_tso(core, addr, l2ev)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_Walk4(pre: State, post: State, core: Core, walk: PTWalk, l3ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1]; let l2e = path[2];
    let addr = add(l2e.1@->Directory_addr, l3_bits!(va as u64) as usize);
    let l3e = (addr, PageDirectoryEntry { entry: l3ev as u64, layer: Ghost(3) });
    let new_walk = match l3e.1@ {
        GhostPageDirectoryEntry::Page { .. } => PTWalk::Valid { va, path: seq![l0e, l1e, l2e, l3e] },
        GhostPageDirectoryEntry::Directory { .. }
        | GhostPageDirectoryEntry::Empty => PTWalk::Invalid { va },
    };
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 3
    &&& pre.read_from_mem_tso(core, addr, l3ev)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_WalkCancel(pre: State, post: State, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& pre.walks[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}

// FIXME: this should make sure the alignment of va fits with the PTE
pub open spec fn step_Walk(pre: State, post: State, path: Seq<(usize, PageDirectoryEntry)>, lbl: Lbl) -> bool {
    let walk = match lbl {
        Lbl::Walk(_, va, Some(pte)) => PTWalk::Valid { va, path },
        Lbl::Walk(_, va, None) => PTWalk::Invalid { va },
        _ => arbitrary(),
    };
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& pre.walks[core].contains(walk)
    &&& (pte matches Some(pte) ==> pte == walk.pte())

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
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
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes.insert(addr)
}

pub open spec fn step_Writeback(pre: State, post: State, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem@ == pre.pt_mem@.insert(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}

pub open spec fn step_Read(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
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
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
}

pub enum Step {
    // Mixed
    Invlpg,
    // Translation caching
    CacheFill { core: Core, walk: PTWalk },
    CacheUse { core: Core, e: CacheEntry },
    CacheEvict { core: Core, e: CacheEntry },
    // Non-atomic page table walks
    Walk1 { core: Core, va: usize, l0ev: usize },
    Walk2 { core: Core, walk: PTWalk, l1ev: usize },
    Walk3 { core: Core, walk: PTWalk, l2ev: usize },
    Walk4 { core: Core, walk: PTWalk, l3ev: usize },
    WalkCancel { core: Core, walk: PTWalk },
    Walk { path: Seq<(usize, PageDirectoryEntry)> },
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
}

pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                     => step_Invlpg(pre, post, lbl),
        Step::CacheFill { core, walk }   => step_CacheFill(pre, post, core, walk, lbl),
        Step::CacheUse { core, e }       => step_CacheUse(pre, post, core, e, lbl),
        Step::CacheEvict { core, e }     => step_CacheEvict(pre, post, core, e, lbl),
        Step::Walk1 { core, va, l0ev }   => step_Walk1(pre, post, core, va, l0ev, lbl),
        Step::Walk2 { core, walk, l1ev } => step_Walk2(pre, post, core, walk, l1ev, lbl),
        Step::Walk3 { core, walk, l2ev } => step_Walk3(pre, post, core, walk, l2ev, lbl),
        Step::Walk4 { core, walk, l3ev } => step_Walk4(pre, post, core, walk, l3ev, lbl),
        Step::WalkCancel { core, walk }  => step_WalkCancel(pre, post, core, walk, lbl),
        Step::Walk { path }              => step_Walk(pre, post, path, lbl),
        Step::Write                      => step_Write(pre, post, lbl),
        Step::Writeback { core }         => step_Writeback(pre, post, core, lbl),
        Step::Read                       => step_Read(pre, post, lbl),
        Step::Barrier                    => step_Barrier(pre, post, lbl),
    }
}

pub open spec fn next(pre: State, post: State, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, step, lbl)
}

proof fn init_implies_inv(pre: State)
    requires pre.init()
    ensures pre.inv()
{ admit(); }

proof fn next_step_preserves_inv(pre: State, post: State, step: Step, lbl: Lbl)
    requires
        pre.inv(),
        next_step(pre, post, step, lbl),
    ensures post.inv()
{
    // TODO: this needs the whole valid_core stuff to work.
    admit();
    //match step {
    //    Step::Invlpg                     => {
    //        admit();
    //        assert(post.inv());
    //        assert(post.inv());
    //    },
    //    Step::CacheFill { core, walk }   => assert(post.inv()),
    //    Step::CacheUse { core, e }       => assume(post.inv()),
    //    Step::CacheEvict { core, e }     => assert(post.inv()),
    //    Step::Walk1 { core, va, l0ev }   => assume(post.inv()),
    //    Step::Walk2 { core, walk, l1ev } => assume(post.inv()),
    //    Step::Walk3 { core, walk, l2ev } => assume(post.inv()),
    //    Step::Walk4 { core, walk, l3ev } => assume(post.inv()),
    //    Step::WalkCancel { core, walk }  => assume(post.inv()),
    //    Step::Walk { path }              => {
    //        let core = lbl->Walk_0;
    //        assert forall|core_| post.walks[core_].subset_of(#[trigger] post.hist.walks[core_]) by {
    //            if pre.walks.contains_key(core_) {
    //                assert(post.walks[core_].subset_of(post.hist.walks[core_]));
    //            } else {
    //                assert(post.walks[core_].subset_of(post.hist.walks[core_]));
    //            }
    //        };
    //        //assert(post.walks[core].subset_of(post.hist.walks[core]));
    //        //assert(forall|corep| corep != core ==> post.walks[corep] == pre.walks[corep]);
    //        assert(post.inv());
    //    },
    //    Step::Write                      => assert(post.inv()),
    //    Step::Writeback { core }         => assert(post.inv()),
    //    Step::Read                       => assert(post.inv()),
    //    Step::Barrier                    => assert(post.inv()),
    //}
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

} // verus!
