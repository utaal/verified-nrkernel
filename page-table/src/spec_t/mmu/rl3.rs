#![verus::trusted]
// Trusted: This file defines the assumed semantics of the memory translation hardware as a state
// machine.

use vstd::prelude::*;
use crate::spec_t::mem::word_index_spec;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::spec_t::mmu::defs::{ aligned, bit, Core, bitmask_inc, MemOp, LoadResult, PTE };
use crate::spec_t::mmu::translation::{ l0_bits, l1_bits, l2_bits, l3_bits, MASK_DIRTY_ACCESS };

verus! {

// TODO: Should prove some basic liveness stuff, like: We can always make progress on an inflight
// partial walk.
// (forall walk in pre.walks. exists post. step_WalkStep(pre, post, walk, ..)

// This file contains refinement layer 3 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.
//
// Most of the definitions in this file are `closed`. We reason about the behavior of this state
// machine exclusively in terms of the more abstract MMU models it refines.

pub struct State {
    /// Word-indexed physical (non-page-table) memory
    phys_mem: Seq<nat>,
    /// Page table memory
    pt_mem: PTMem,
    /// Per-node state (TLBs)
    tlbs: Map<Core, Map<usize, PTE>>,
    /// In-progress page table walks
    walks: Map<Core, Set<Walk>>,
    /// Translation caches
    cache: Map<Core, Set<Walk>>,
    /// Store buffers
    sbuf: Map<Core, Seq<(usize, usize)>>,
    /// History variables. These do not influence the transitions in any way. Neither in enabling
    /// conditions nor in state updates. We only use these during the refinement.
    hist: History,
}

pub struct History {
    pub happy: bool,
    /// All partial walks since the last invlpg
    pub walks: Map<Core, Set<Walk>>,
    pub writes: Writes,
    pub pending_maps: Map<usize, PTE>,
    ///// Current polarity: Are we doing only positive writes or only negative writes? Polarity can be
    ///// flipped when neg and writes are all empty.
    ///// A non-flipping write with the wrong polarity sets happy to false.
    ///// Additionally tracks the current writer core.
    ///// Technically we could probably infer the polarity from the write tracking but this is easier.
    //pub polarity: Polarity,
}

pub struct Writes {
    /// Current writer core. If `all` is non-empty, all those writes were done by this core.
    pub core: Core,
    /// Tracks *all* writes. Set of addresses. Gets cleared when the corresponding core drains its
    /// store buffer. These writes can cause TSO staleness.
    pub all: Set<usize>,
    ///// Tracks negative writes (to both page and directory mappings). Cleared for a particular core
    ///// when it executes an invlpg.
    ///// These writes can cause staleness due to partial translation caching or non-atomicity of
    ///// walks.
    //pub neg: Map<Core, Set<usize>>,
}

//pub enum Polarity {
//    Pos(Core),
//    Neg(Core),
//}
//
//impl Polarity {
//    pub open spec fn core(self) -> Core {
//        match self {
//            Polarity::Pos(c) => c,
//            Polarity::Neg(c) => c,
//        }
//    }
//}

/// Any transition that reads from page table memory takes an arbitrary usize `r`, which is used to
/// non-deterministically flip the accessed and dirty bits.
/// A seemingly easier way to specify this would be:
/// `result & MASK_NEG_DIRTY_ACCESS = read(addr) & MASK_NEG_DIRTY_ACCESS`
/// But this makes specifying the page table walks very awkward because read is now specified as a
/// predicate. Instead we explicitly xor with an arbitrary value. At higher refinement layers we do
/// use the predicate approach because we can prove in the refinement that the value of `r` is
/// irrelevant for page table walks, so the read predicate only shows up in `step_Read`.
pub enum Step {
    Invlpg,
    // Faulting memory op due to failed translation
    MemOpNoTr { walk: Walk, r: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk, r: usize },
    TLBFill { core: Core, walk: Walk, r: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // TSO, operations on page table memory
    Write,
    Writeback { core: Core },
    Read { r: usize },
    Barrier,
    Stutter,
}


impl State {
    pub closed spec fn read_from_mem_tso(self, core: Core, addr: usize, r: usize) -> usize {
        self.core_mem(core).read(addr) ^ (r & MASK_DIRTY_ACCESS)
    }

    /// The memory as seen by the given core. I.e. taking into consideration the core's store
    /// buffers.
    pub closed spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    /// The view of the memory from the writer core's perspective.
    pub closed spec fn writer_mem(self) -> PTMem {
        self.core_mem(self.hist.writes.core)
    }

    pub closed spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize, c: Constants) -> bool {
        &&& !self.hist.writes.all.is_empty() ==> core == self.hist.writes.core
        &&& self.writer_mem().is_nonneg_write(addr, value)
    }
}



// State machine transitions

pub closed spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
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

    &&& post == State {
        hist: History {
            walks: pre.hist.walks.insert(core, set![]),
            writes: Writes {
                all: if core == pre.hist.writes.core { set![] } else { pre.hist.writes.all },
                //neg: pre.hist.writes.neg.insert(core, set![]),
                core: pre.hist.writes.core,
            },
            pending_maps: if core == pre.hist.writes.core { map![] } else { pre.hist.pending_maps },
            ..pre.hist
        },
        ..pre
    }
}

// We only allow aligned accesses. Can think of unaligned accesses as two aligned accesses. When we
// get to concurrency we may have to change that.
// TODO: Is this a problem now?
pub closed spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    r: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)

    &&& {
    let walk_next = walk_next(pre, core, walk, r);
    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk.vaddr == memop_vaddr
    &&& walk_next.complete
    &&& walk_next.result() is Invalid
    &&& memop.is_pagefault()
    }

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].remove(walk)),
        ..pre
    }
}

pub closed spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)

    &&& {
    let pte = pre.tlbs[core][tlb_va];
    let pmem_idx = word_index_spec(pte.frame.base + (memop_vaddr - tlb_va) as nat);
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, 8)
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& tlb_va <= memop_vaddr < tlb_va + pte.frame.size
    &&& match memop {
        MemOp::Store { new_value, result } => {
            if pmem_idx < pre.phys_mem.len() && !pte.flags.is_supervisor && pte.flags.is_writable {
                &&& result is Ok
                &&& post.phys_mem === pre.phys_mem.update(pmem_idx as int, new_value as nat)
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
        MemOp::Load { is_exec, result } => {
            if pmem_idx < pre.phys_mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                &&& result == LoadResult::Value(pre.phys_mem[pmem_idx as int])
                &&& post.phys_mem === pre.phys_mem
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
    }
    }

    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.walks == pre.walks
    &&& post.cache == pre.cache
    &&& post.sbuf == pre.sbuf
    &&& post.hist == pre.hist
}



// ---- Translation caching ----

pub closed spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)

    &&& post == State {
        cache: pre.cache.insert(core, pre.walks[core].insert(walk)),
        ..pre
    }
}

pub closed spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].insert(walk)),
        ..pre
    }
}

pub closed spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post == State {
        cache: pre.cache.insert(core, pre.cache[core].remove(walk)),
        ..pre
    }
}


// ---- Non-atomic page table walks ----

// FIXME: this should make sure the alignment of va fits with the PTE
pub closed spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& aligned(vaddr as nat, 8)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    //&&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].insert(walk)),
        hist: History {
            walks: pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk)),
            ..pre.hist
        },
        ..pre
    }
}

pub closed spec fn walk_next(state: State, core: Core, walk: Walk, r: usize) -> Walk {
    let Walk { vaddr, path, .. } = walk;
    let mem = state.pt_mem;
    let addr = if path.len() == 0 {
        add(mem.pml4, mul(l0_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
    } else { arbitrary() };
    let value = state.read_from_mem_tso(core, addr, r);
    let entry = PDE { entry: value, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory)
    };
    walk
}

pub closed spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    r: usize,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre, core, walk, r);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].remove(walk).insert(walk_next)),
        hist: History {
            walks: pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk_next)),
            ..pre.hist
        },
        ..pre
    }
}

/// Completes a (valid) page table walk and caches the resulting translation in the TLB.
///
/// Note: A valid walk's result is a region whose base and size depend on the path taken. E.g. a
/// huge page mapping results in a 2M-sized region. Invalid walks are always for a 4K-sized region.
pub closed spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, r: usize, lbl: Lbl) -> bool {
    let walk_next = walk_next(pre, core, walk, r);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.complete
    &&& walk_next.result() matches WalkResult::Valid { vbase, pte }

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].remove(walk)),
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vbase, pte)),
        ..pre
    }
}

pub closed spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.tlbs[core].contains_key(tlb_va)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].remove(tlb_va)),
        ..pre
    }
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
// TODO: we don't model atomics, so technically the user-space threads cannot synchronize
// TODO: max physical size?
/// Write to core's local store buffer.
pub closed spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.happy == (pre.hist.happy && pre.is_this_write_happy(core, addr, value, c))
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all == pre.hist.writes.all.insert(addr)
    //&&& post.hist.writes.neg == if !pre.writer_mem().is_nonneg_write(addr, value) {
    //        pre.hist.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
    //    } else { pre.hist.writes.neg }
    &&& post.hist.writes.core == core
    &&& post.hist.pending_maps == pre.hist.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.writer_mem()@.contains_key(vbase)
                    && !pre.writer_mem()@.contains_key(vbase),
            |vbase| post.writer_mem()@[vbase]
        ))
    // Whenever this causes polarity to change and happy isn't set to false, the
    // conditions for polarity to change are satisfied (`can_change_polarity`)
    //&&& post.hist.polarity == if pre.writer_mem().is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
}

pub closed spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post == State {
        pt_mem: pre.pt_mem.write(addr, value),
        sbuf: pre.sbuf.insert(core, pre.sbuf[core].drop_first()),
        ..pre
    }
}

pub closed spec fn step_Read(pre: State, post: State, c: Constants, r: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value == pre.read_from_mem_tso(core, addr, r)

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub closed spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        hist: History {
            writes: Writes {
                all: if core == pre.hist.writes.core { set![] } else { pre.hist.writes.all },
                ..pre.hist.writes
            },
            pending_maps: if core == pre.hist.writes.core { map![] } else { pre.hist.pending_maps },
            ..pre.hist
        },
        ..pre
    }
}

pub closed spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        //Step::ReadWrite { paddr, wr }    => step_ReadWrite(pre, post, c, paddr, wr, lbl),
        Step::Invlpg                       => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr { walk, r }        => step_MemOpNoTr(pre, post, c, walk, r, lbl),
        Step::MemOpTLB { tlb_va }          => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::CacheFill { core, walk }     => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }      => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, walk }    => step_CacheEvict(pre, post, c, core, walk, lbl),
        Step::WalkInit { core, vaddr }     => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, r }   => step_WalkStep(pre, post, c, core, walk, r, lbl),
        Step::TLBFill { core, walk, r }    => step_TLBFill(pre, post, c, core, walk, r, lbl),
        Step::TLBEvict { core, tlb_va }     => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        //Step::WalkDone { core, walk, r } => step_WalkDone(pre, post, c, core, walk, r, lbl),
        Step::Write                        => step_Write(pre, post, c, lbl),
        Step::Writeback { core }           => step_Writeback(pre, post, c, core, lbl),
        Step::Read { r }                   => step_Read(pre, post, c, r, lbl),
        Step::Barrier                      => step_Barrier(pre, post, c, lbl),
        Step::Stutter                      => step_Stutter(pre, post, c, lbl),
    }
}

pub closed spec fn init(pre: State, c: Constants) -> bool {
    // TODO: init conditions for the two memories. Can we require here that they are disjoint?
    //&&& pre.pt_mem == ..
    &&& pre.tlbs  === Map::new(|core| c.valid_core(core), |core| Map::empty())
    &&& pre.walks === Map::new(|core| c.valid_core(core), |core| set![])
    &&& pre.cache === Map::new(|core| c.valid_core(core), |core| set![])
    &&& pre.sbuf  === Map::new(|core| c.valid_core(core), |core| seq![])
    &&& pre.hist.happy == true
    &&& pre.hist.walks === Map::new(|core| c.valid_core(core), |core| set![])
    //&&& pre.hist.writes.core == ..
    &&& pre.hist.writes.all === set![]
    &&& pre.hist.pending_maps === map![]

    &&& c.valid_core(pre.hist.writes.core)
    &&& forall|va| aligned(va as nat, 8) ==> #[trigger] pre.pt_mem.mem.contains_key(va)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& pre.pt_mem.pml4 <= u64::MAX - 4096
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}





// Invariants for this state machine

impl State {
    pub closed spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.cache.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.walks.contains_key(core)
        //&&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].finite()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.cache[core].finite()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.walks[core].finite()
        //&&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.writes.neg[core].finite()
    }

    pub closed spec fn inv_inflight_walks(self, c: Constants) -> bool {
        &&& forall|core, walk| c.valid_core(core) && #[trigger] self.walks[core].contains(walk) ==> {
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
        }
        &&& forall|core, walk| c.valid_core(core) && #[trigger] self.cache[core].contains(walk) ==> {
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
        }
    }

    pub closed spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].subset_of(self.hist.walks[core])
    }

    pub closed spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core, walk|
            c.valid_core(core) && #[trigger] self.cache[core].contains(walk)
            ==> self.hist.walks[core].contains(walk)
    }

    pub closed spec fn inv(self, c: Constants) -> bool {
        self.hist.happy ==> {
        &&& self.wf(c)
        &&& self.inv_inflight_walks(c)
        &&& self.inv_walks_subset_of_hist_walks(c)
        &&& self.inv_cache_subset_of_hist_walks(c)
        }
    }
} // impl State


pub proof fn init_implies_inv(pre: State, c: Constants)
    requires init(pre, c)
    ensures pre.inv(c)
{}

pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.inv(c),
        next(pre, post, c, lbl),
    ensures post.inv(c)
{}





pub mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl3::bit;
    use crate::spec_t::mmu::translation::{ MASK_DIRTY_ACCESS, MASK_NEG_DIRTY_ACCESS };

    impl rl3::State {
        pub closed spec fn interp(self) -> rl2::State {
            rl2::State {
                happy: self.hist.happy,
                phys_mem: self.phys_mem,
                pt_mem: self.pt_mem,
                tlbs: self.tlbs,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                writes: self.hist.writes,
                hist: rl2::History { pending_maps: self.hist.pending_maps },
                //polarity: self.hist.polarity,
            }
        }
    }

    impl rl3::Step {
        pub closed spec fn interp(self, pre: rl3::State, lbl: Lbl) -> rl2::Step {
            if pre.hist.happy {
                match self {
                    rl3::Step::Invlpg                     => rl2::Step::Invlpg,
                    rl3::Step::MemOpNoTr { walk, r }      => rl2::Step::MemOpNoTr { walk },
                    rl3::Step::MemOpTLB { tlb_va }        => rl2::Step::MemOpTLB { tlb_va },
                    rl3::Step::CacheFill { core, walk }   => rl2::Step::Stutter,
                    rl3::Step::CacheUse { core, walk }    => rl2::Step::Stutter,
                    rl3::Step::CacheEvict { core, walk }  => rl2::Step::Stutter,
                    rl3::Step::WalkInit { core, vaddr }   => rl2::Step::WalkInit { core, vaddr },
                    rl3::Step::WalkStep { core, walk, r } => rl2::Step::WalkStep { core, walk },
                    rl3::Step::TLBFill { core, walk, r }  => rl2::Step::TLBFill { core, walk },
                    rl3::Step::TLBEvict { core, tlb_va }   => rl2::Step::TLBEvict { core, tlb_va },
                    rl3::Step::Write                      => {
                        let (core, addr, value) =
                            if let Lbl::Write(core, addr, value) = lbl {
                                (core, addr, value)
                            } else { arbitrary() };
                        if pre.interp().is_this_write_happy(core, addr, value) {
                            rl2::Step::Write
                        } else {
                            rl2::Step::SadWrite
                        }
                    },
                    rl3::Step::Writeback { core } => rl2::Step::Writeback { core },
                    rl3::Step::Read { r }         => rl2::Step::Read,
                    rl3::Step::Barrier            => rl2::Step::Barrier,
                    rl3::Step::Stutter            => rl2::Step::Stutter,
                }
            } else {
                rl2::Step::Sadness
            }
        }
    }

    broadcast proof fn lemma_mask_dirty_access_after_xor(v: usize, r: usize)
        ensures
            #[trigger] (v ^ (r & MASK_DIRTY_ACCESS)) & MASK_NEG_DIRTY_ACCESS
                            == v & MASK_NEG_DIRTY_ACCESS
    {
        assert((v ^ (r & ((bit!(5) | bit!(6))))) & (!(bit!(5) | bit!(6)))
                == v & (!(bit!(5) | bit!(6)))) by (bit_vector);
    }

    /// The value of r is irrelevant, so we can just ignore it.
    broadcast proof fn rl3_walk_next_is_rl2_walk_next(state: rl3::State, core: Core, walk: Walk, r: usize)
        requires walk.path.len() <= 3
        ensures
        #[trigger] rl3::walk_next(state, core, walk, r)
                == rl2::walk_next(state.interp().core_mem(core), walk)
    {
        reveal(rl2::walk_next);
        state.pt_mem.lemma_write_seq(state.interp().sbuf[core]);
        broadcast use
            lemma_mask_dirty_access_after_xor,
            PDE::lemma_view_unchanged_dirty_access;
    }

    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: Constants, step: rl3::Step, lbl: Lbl)
        requires
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        if pre.hist.happy {
            match step {
                rl3::Step::Invlpg => {
                    assert(rl2::step_Invlpg(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::MemOpNoTr { walk, r } => {
                    let core = lbl->MemOp_0;
                    rl3_walk_next_is_rl2_walk_next(pre, core, walk, r);
                    assert(rl2::step_MemOpNoTr(pre.interp(), post.interp(), c, walk, lbl));
                },
                rl3::Step::MemOpTLB { tlb_va } => {
                    assert(rl2::step_MemOpTLB(pre.interp(), post.interp(), c, tlb_va, lbl));
                },
                rl3::Step::CacheFill { core, walk } => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheUse { core, walk } => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheEvict { core, walk } => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::WalkInit { core, vaddr } => {
                    assert(rl2::step_WalkInit(pre.interp(), post.interp(), c, core, vaddr, lbl))
                },
                rl3::Step::WalkStep { core, walk, r } => {
                    rl3_walk_next_is_rl2_walk_next(pre, core, walk, r);
                    assert(rl2::step_WalkStep(pre.interp(), post.interp(), c, core, walk, lbl));
                },
                rl3::Step::TLBFill { core, walk, r } => {
                    rl3_walk_next_is_rl2_walk_next(pre, core, walk, r);
                    assert(rl2::step_TLBFill(pre.interp(), post.interp(), c, core, walk, lbl));
                },
                rl3::Step::TLBEvict { core, tlb_va } => {
                    assert(rl2::step_TLBEvict(pre.interp(), post.interp(), c, core, tlb_va, lbl));
                },
                rl3::Step::Write => {
                    let (core, addr, value) =
                        if let Lbl::Write(core, addr, value) = lbl {
                            (core, addr, value)
                        } else { arbitrary() };
                    if pre.interp().is_this_write_happy(core, addr, value) {
                        assert(rl2::step_Write(pre.interp(), post.interp(), c, lbl));
                    } else {
                        assert(rl2::step_SadWrite(pre.interp(), post.interp(), c, lbl));
                    }
                },
                rl3::Step::Writeback { core } => {
                    assert(rl2::step_Writeback(pre.interp(), post.interp(), c, core, lbl));
                },
                rl3::Step::Read { r } => {
                    broadcast use lemma_mask_dirty_access_after_xor;
                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::Barrier => {
                    assert(rl2::step_Barrier(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::Stutter => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
            }
        } else {
            assert(rl2::step_Sadness(pre.interp(), post.interp(), c, lbl));
        }
    }

    proof fn init_refines(pre: rl3::State, c: Constants)
        requires rl3::init(pre, c),
        ensures rl2::init(pre.interp(), c),
    {}

    proof fn next_refines(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
        requires
            pre.inv(c),
            rl3::next(pre, post, c, lbl),
        ensures
            rl2::next(pre.interp(), post.interp(), c, lbl),
    {
        let step = choose|step: rl3::Step| rl3::next_step(pre, post, c, step, lbl);
        next_step_refines(pre, post, c, step, lbl);
    }

    pub mod to_rl1 {
        //! Machinery to lift rl3 semantics to rl1 (interp twice and corresponding lemmas), which we use for
        //! reasoning about the OS state machine.

        use crate::spec_t::mmu::*;
        use crate::spec_t::mmu::rl3;
        use crate::spec_t::mmu::rl1;

        impl rl3::State {
            pub open spec fn view(self) -> rl1::State {
                self.interp().interp()
            }
        }

        pub proof fn init_implies_inv(pre: rl3::State, c: Constants)
            requires rl3::init(pre, c),
            ensures
                pre.inv(c),
                pre.interp().inv(c),
        {}

        pub broadcast proof fn next_preserves_inv(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
            requires
                pre.inv(c),
                pre.interp().inv(c),
                #[trigger] rl3::next(pre, post, c, lbl),
            ensures
                post.inv(c),
                post.interp().inv(c),
        {
            rl3::next_preserves_inv(pre, post, c, lbl);
            rl3::refinement::next_refines(pre, post, c, lbl);
            rl2::next_preserves_inv(pre.interp(), post.interp(), c, lbl);
        }

        pub proof fn init_refines(pre: rl3::State, c: Constants)
            requires rl3::init(pre, c),
            ensures rl1::init(pre@, c),
        {}

        pub broadcast proof fn next_refines(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
            requires
                pre.inv(c),
                pre.interp().inv(c),
                #[trigger] rl3::next(pre, post, c, lbl),
            ensures
                rl1::next(pre@, post@, c, lbl),
        {
            rl3::refinement::next_refines(pre, post, c, lbl);
            rl2::refinement::next_refines(pre.interp(), post.interp(), c, lbl);
        }
    }
}


/// The axiomatized interface to execute the actions specified in this state machine.
pub mod code {
    use vstd::prelude::*;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::{ self, Core };

    #[verifier(external_body)]
    pub tracked struct Token {}

    #[verifier(external_body)]
    pub tracked struct Stub {}

    impl Token {
        pub spec fn consts(self) -> mmu::Constants;
        pub spec fn core(self) -> Core;
        pub spec fn pre(self) -> rl3::State;
        pub spec fn post(self) -> rl3::State;
        pub spec fn lbl(self) -> mmu::Lbl;
        pub spec fn validated(self) -> bool;

        pub open spec fn set_valid(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.post() == self.post()
            &&& new.lbl() == self.lbl()
            &&& new.validated()
        }

        pub open spec fn prophesied_step(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.validated() == self.validated()
            &&& rl3::next(new.pre(), new.post(), new.consts(), new.lbl())
        }

        pub proof fn prophesy_read(tracked &mut self, addr: usize)
            requires
                !old(self).validated(),
            ensures
                self.lbl()->Read_0 == self.core(),
                self.lbl()->Read_1 == addr,
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_write(tracked &mut self, addr: usize, value: usize)
            requires
                !old(self).validated(),
            ensures
                self.lbl() == mmu::Lbl::Write(self.core(), addr, value),
                old(self).prophesied_step(*self),
        { 
            admit();
        }

        pub proof fn prophesy_barrier(tracked &mut self)
            requires
                !old(self).validated(),
            ensures
                self.lbl() == mmu::Lbl::Barrier(self.core()),
                old(self).prophesied_step(*self),
        { 
            admit();
        }

        pub proof fn prophesy_invlpg(tracked &mut self, addr: usize)
            requires
                !old(self).validated(),
            ensures
                self.lbl() == mmu::Lbl::Invlpg(self.core(), addr),
                old(self).prophesied_step(*self),
        { 
            admit();
        }
    }

    #[verifier(external_body)]
    pub exec fn read(Tracked(tok): Tracked<Token>, addr: usize) -> (res: (Tracked<Stub>, usize))
        requires
            tok.validated(),
            tok.lbl() matches mmu::Lbl::Read(lbl_core, lbl_addr, _) && lbl_core == tok.core() && lbl_addr == addr,
        ensures
            tok.lbl()->Read_2 == res.1
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn write(Tracked(tok): Tracked<Token>, addr: usize, value: usize) -> Tracked<Stub>
        requires
            tok.validated(),
            tok.lbl() == mmu::Lbl::Write(tok.core(), addr, value),
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn barrier(Tracked(tok): Tracked<Token>) -> Tracked<Stub>
        requires
            tok.validated(),
            tok.lbl() == mmu::Lbl::Barrier(tok.core()),
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn invlpg(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
        requires
            tok.validated(),
            tok.lbl() == mmu::Lbl::Invlpg(tok.core(), vaddr),
    {
        unimplemented!() // TODO:
    }

    // TODO: need transitions to allocate/deallocate pages i guess
    // TODO: add a transition to read pml4?
    //#[verifier(external_body)]
    //pub exec fn get_pml4(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
    //    ensures ..
    //{
    //    unimplemented!()
    //}

}



} // verus!
