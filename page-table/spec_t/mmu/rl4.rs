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

pub struct Constants {
    pub cores: Set<Core>,
}

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<PTWalk>>,
    /// Translation caches
    pub cache: Map<Core, Set<CacheEntry>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    ///// Addresses that have been used in a page table walk
    ///// TODO: This can probably be at least partially reset in invlpg.
    //pub used_addrs: Set<usize>,
    /// History variables. These are not allowed to influence transitions in any way. Neither in
    /// enabling conditions nor in how the state is updated.
    pub hist: History,
    //pub proph: Prophecy,
}

pub struct History {
    /// All partial and complete page table walks since the last invlpg
    pub walks: Map<Core, Set<PTWalk>>,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
}

//pub struct Prophecy {
//    /// Prophesied memories after future writeback transitions
//    pub pt_mems: Seq<PTMem>,
//}

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

    /// Is true if only this core's store buffer is non-empty.
    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores() === set![] || self.writer_cores() === set![core] 
        //forall|core2| #[trigger] c.valid_core(core2) && self.sbuf[core2].len() > 0 ==> core2 == core1
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.hist.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.cache.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.walks.contains_key(core)
    }

    pub open spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].subset_of(self.hist.walks[core])
    }

    pub open spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core,e| c.valid_core(core) ==> #[trigger] self.cache[core].contains(e) ==> self.hist.walks[core].contains(e.as_ptwalk())
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        // TODO:
        // invariant on walks and cache:
        // - The PDEs stored in `Partial` walks are always directories
        // - Length of paths in `Partial` walks in `walks` is always 1, 2 or 3
        // - Length of paths in `Valid` walks in `walks` is always 2, 3 or 4
        // - `Valid` walks always have a path made of directories, with a final page entry
        // - Length of paths in cache entries in `cache` is always 1, 2 or 3
        &&& self.wf(c)
        &&& self.inv_walks_subset_of_hist_walks(c)
        &&& self.inv_cache_subset_of_hist_walks(c)
        }
    }
}

impl Constants {
    pub open spec fn valid_core(self, core: Core) -> bool {
        self.cores.contains(core)
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0
    // .. evicts corresponding entries from the translation caches, ..
    // Note that per Intel Manual 3A, 4.10.4.1:
    // "INVLPG also invalidates all entries in all paging-structure caches associated with the
    // current PCID, regardless of the linear addresses to which they correspond."
    &&& pre.cache[core].is_empty()
    // .. and waits for inflight walks to complete.
    &&& pre.walks[core].is_empty()

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks.insert(core, set![])
    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].insert(walk.as_cache_entry()))
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(e)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(e.as_ptwalk()))
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, e: CacheEntry, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(e)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].remove(e))
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}


// ---- Non-atomic page table walks ----

pub open spec fn step_Walk1(pre: State, post: State, c: Constants, core: Core, va: usize, l0ev: usize, lbl: Lbl) -> bool {
    let addr = add(pre.pt_mem.pml4(), l0_bits!(va as u64) as usize);
    let l0e = (addr, PageDirectoryEntry { entry: l0ev as u64, layer: Ghost(0) });
    let walk = match l0e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e] },
        _                                         => arbitrary(), // No page mappings here
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?
    &&& pre.read_from_mem_tso(core, addr, l0ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk))
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_Walk2(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l1ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0];
    let addr = add(l0e.1@->Directory_addr, l1_bits!(va as u64) as usize);
    let l1e = (addr, PageDirectoryEntry { entry: l1ev as u64, layer: Ghost(1) });
    let new_walk = match l1e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid   { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e, l1e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 1
    &&& pre.read_from_mem_tso(core, addr, l1ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_Walk3(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l2ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1];
    let addr = add(l1e.1@->Directory_addr, l2_bits!(va as u64) as usize);
    let l2e = (addr, PageDirectoryEntry { entry: l2ev as u64, layer: Ghost(2) });
    let new_walk = match l2e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid   { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e, l1e, l2e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 2
    &&& pre.read_from_mem_tso(core, addr, l2ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_Walk4(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l3ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1]; let l2e = path[2];
    let addr = add(l2e.1@->Directory_addr, l3_bits!(va as u64) as usize);
    let l3e = (addr, PageDirectoryEntry { entry: l3ev as u64, layer: Ghost(3) });
    let new_walk = match l3e.1@ {
        GhostPageDirectoryEntry::Page { .. } => PTWalk::Valid { va, path: seq![l0e, l1e, l2e, l3e] },
        GhostPageDirectoryEntry::Directory { .. }
        | GhostPageDirectoryEntry::Empty => PTWalk::Invalid { va, path: seq![l0e, l1e, l2e, l3e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 3
    &&& pre.read_from_mem_tso(core, addr, l3ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(new_walk))
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_WalkCancel(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

// FIXME: this should make sure the alignment of va fits with the PTE
pub open spec fn step_Walk(pre: State, post: State, c: Constants, path: Seq<(usize, PageDirectoryEntry)>, lbl: Lbl) -> bool {
    let walk = match lbl {
        Lbl::Walk(_, va, Some(pte)) => PTWalk::Valid { va, path },
        Lbl::Walk(_, va, None) => PTWalk::Invalid { va, path },
        _ => arbitrary(),
    };
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& (pte matches Some(pte) ==> pte == walk.pte())

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
// TODO: we don't model atomics, so technically the user-space threads cannot synchronize
// TODO: max physical size?
/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes.insert((core, addr))
    //&&& post.proph.pt_mems == pre.proph.pt_mems.push(proph)
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    //// Prophetic enabling condition
    //&&& pre.proph.pt_mems.len() >= 1
    //&&& post.pt_mem == pre.proph.pt_mems[0]

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems.drop_first()
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                     => step_Invlpg(pre, post, c, lbl),
        Step::CacheFill { core, walk }   => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, e }       => step_CacheUse(pre, post, c, core, e, lbl),
        Step::CacheEvict { core, e }     => step_CacheEvict(pre, post, c, core, e, lbl),
        Step::Walk1 { core, va, l0ev }   => step_Walk1(pre, post, c, core, va, l0ev, lbl),
        Step::Walk2 { core, walk, l1ev } => step_Walk2(pre, post, c, core, walk, l1ev, lbl),
        Step::Walk3 { core, walk, l2ev } => step_Walk3(pre, post, c, core, walk, l2ev, lbl),
        Step::Walk4 { core, walk, l3ev } => step_Walk4(pre, post, c, core, walk, l3ev, lbl),
        Step::WalkCancel { core, walk }  => step_WalkCancel(pre, post, c, core, walk, lbl),
        Step::Walk { path }              => step_Walk(pre, post, c, path, lbl),
        Step::Write                      => step_Write(pre, post, c, lbl),
        Step::Writeback { core }         => step_Writeback(pre, post, c, core, lbl),
        Step::Read                       => step_Read(pre, post, c, lbl),
        Step::Barrier                    => step_Barrier(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants) -> bool {
    pre.happy ==> exists|step, lbl| next_step(pre, post, c, step, lbl)
}

proof fn init_implies_inv(pre: State, c: Constants)
    requires pre.init()
    ensures pre.inv(c)
{ admit(); }

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv(c)
{
    match step {
        Step::Invlpg                     => {
            let core = lbl->Invlpg_0;
            assert(c.valid_core(core));
            assert(post.walks[core].is_empty());
            // TODO: Verus sets have some serious problems. How do I not know that a set with len 0
            // is the empty set..?
            // Really don't want to add finiteness invariants everywhere.
            assume(post.walks[core].finite());
            assume(post.cache[core].finite());
            assert(post.walks[core] === set![]);
            assert(post.hist.walks[core] =~= set![]);
            assert(post.inv(c))
        },
        Step::CacheFill { core, walk }   => assert(post.inv(c)),
        Step::CacheUse { core, e }       => {
            assume(post.walks[core].finite());
            assert(post.inv(c))
        },
        Step::CacheEvict { core, e }     => assert(post.inv(c)),
        Step::Walk1 { core, va, l0ev }   => assert(post.inv(c)),
        Step::Walk2 { core, walk, l1ev } => assert(post.inv(c)),
        Step::Walk3 { core, walk, l2ev } => assert(post.inv(c)),
        Step::Walk4 { core, walk, l3ev } => assert(post.inv(c)),
        Step::WalkCancel { core, walk }  => assert(post.inv(c)),
        Step::Walk { path }              => assert(post.inv(c)),
        Step::Write                      => assert(post.inv(c)),
        Step::Writeback { core }         => assert(post.inv(c)),
        Step::Read                       => assert(post.inv(c)),
        Step::Barrier                    => assert(post.inv(c)),
    }
}





mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl4;

    impl rl4::State {
        pub open spec fn interp(self) -> rl3::State {
            rl3::State {
                happy: self.happy,
                pt_mem: self.pt_mem,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                //used_addrs: self.used_addrs,
                hist: rl3::History { writes: self.hist.writes },
                //proph: rl3::Prophecy { pt_mems: self.proph.pt_mems },
            }
        }
    }

    impl rl4::Constants {
        pub open spec fn interp(self) -> rl3::Constants {
            rl3::Constants {
                cores: self.cores,
            }
        }
    }

    impl rl4::Step {
        pub open spec fn interp(self) -> rl3::Step {
            match self {
                rl4::Step::Invlpg                     => rl3::Step::Invlpg,
                rl4::Step::CacheFill { core, walk }   => rl3::Step::Stutter,
                rl4::Step::CacheUse { core, e }       => rl3::Step::Stutter,
                rl4::Step::CacheEvict { core, e }     => rl3::Step::Stutter,
                rl4::Step::Walk1 { core, va, l0ev }   => rl3::Step::Walk1 { core, va, l0ev },
                rl4::Step::Walk2 { core, walk, l1ev } => rl3::Step::Walk2 { core, walk, l1ev },
                rl4::Step::Walk3 { core, walk, l2ev } => rl3::Step::Walk3 { core, walk, l2ev },
                rl4::Step::Walk4 { core, walk, l3ev } => rl3::Step::Walk4 { core, walk, l3ev },
                rl4::Step::WalkCancel { core, walk }  => rl3::Step::Stutter,
                rl4::Step::Walk { path }              => rl3::Step::Walk { path },
                rl4::Step::Write                      => rl3::Step::Write,
                rl4::Step::Writeback { core }         => rl3::Step::Writeback { core },
                rl4::Step::Read                       => rl3::Step::Read,
                rl4::Step::Barrier                    => rl3::Step::Barrier,
            }
        }
    }

    proof fn next_step_refines(pre: rl4::State, post: rl4::State, c: rl4::Constants, step: rl4::Step, lbl: Lbl)
        requires
            pre.happy,
            pre.inv(c),
            rl4::next_step(pre, post, c, step, lbl),
        ensures rl3::next_step(pre.interp(), post.interp(), c.interp(), step.interp(), lbl)
    {
        match step {
            rl4::Step::Invlpg => {
                assert(rl3::step_Invlpg(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheFill { core, walk }  => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheUse { core, e }      => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheEvict { core, e }    => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::Walk1 { core, va, l0ev }        => {
                assert(rl3::step_Walk1(pre.interp(), post.interp(), c.interp(), core, va, l0ev, lbl));
            },
            rl4::Step::Walk2 { core, walk, l1ev }      => {
                assert(c.valid_core(core));
                assert(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk2(pre.interp(), post.interp(), c.interp(), core, walk, l1ev, lbl));
            },
            rl4::Step::Walk3 { core, walk, l2ev }      => {
                assert(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk3(pre.interp(), post.interp(), c.interp(), core, walk, l2ev, lbl));
            },
            rl4::Step::Walk4 { core, walk, l3ev }      => {
                assert(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk4(pre.interp(), post.interp(), c.interp(), core, walk, l3ev, lbl));
            },
            rl4::Step::WalkCancel { core, walk } => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));

            },
            rl4::Step::Walk { path } => {
                let core = lbl->Walk_0;
                assert(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk(pre.interp(), post.interp(), c.interp(), path, lbl));
            },
            rl4::Step::Write                     => {
                let core = lbl->Write_0;
                if pre.no_other_writers(core) {
                    //assert forall|core2| c.valid_core(core2) && #[trigger] pre.interp().sbuf[core2].len() > 0 ==> core2 == core by { };
                    assert(pre.interp().no_other_writers(core));
                    assert(rl3::step_Write(pre.interp(), post.interp(), c.interp(), lbl));
                } else {
                    assert(rl3::step_Write(pre.interp(), post.interp(), c.interp(), lbl));
                }
            },
            rl4::Step::Writeback { core }        => {
                assert(rl3::step_Writeback(pre.interp(), post.interp(), c.interp(), core, lbl));
            },
            rl4::Step::Read                      => {
                assert(rl3::step_Read(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::Barrier                   => {
                assert(rl3::step_Barrier(pre.interp(), post.interp(), c.interp(), lbl));
            },
        }
    }

    proof fn next_refines(pre: rl4::State, post: rl4::State, c: rl4::Constants)
        requires
            pre.inv(c),
            rl4::next(pre, post, c),
        ensures
            rl3::next(pre.interp(), post.interp(), c.interp()),
    {
        if pre.happy {
            // TODO: ...
            assume(exists|x:(rl4::Step, Lbl)| #[trigger] rl4::next_step(pre, post, c, x.0, x.1));
            let (step, lbl) = choose|x:(rl4::Step, Lbl)| #[trigger] rl4::next_step(pre, post, c, x.0, x.1);
            next_step_refines(pre, post, c, step, lbl);
        }
    }
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
