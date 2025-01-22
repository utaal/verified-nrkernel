use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, bit, Core };
use crate::spec_t::hardware::{ MASK_DIRTY_ACCESS };

verus! {

// TODO: Should prove some basic liveness stuff, like: We can always make progress on an inflight
// partial walk.
// (forall walk in pre.walks. exists post. step_WalkStep(pre, post, walk, ..)

// This file contains refinement layer 4 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.

pub struct State {
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Translation caches
    pub cache: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    /// History variables. These are not allowed to influence transitions in any way. Neither in
    /// enabling conditions nor in how the state is updated.
    pub hist: History,
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

impl State {
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, r: usize) -> usize {
        self.core_mem(core).read(addr) ^ (r & MASK_DIRTY_ACCESS)
    }

    /// The memory as seen by the given core. I.e. taking into consideration the core's store
    /// buffers.
    pub open spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    /// The view of the memory from the writer core's perspective.
    pub open spec fn writer_mem(self) -> PTMem {
        self.core_mem(self.hist.writes.core)
    }

    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize, c: Constants) -> bool {
        &&& !self.hist.writes.all.is_empty() ==> core == self.hist.writes.core
        &&& self.writer_mem().is_nonneg_write(addr, value)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
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

    pub open spec fn inv_inflight_walks(self, c: Constants) -> bool {
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

    pub open spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].subset_of(self.hist.walks[core])
    }

    pub open spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core, walk|
            c.valid_core(core) && #[trigger] self.cache[core].contains(walk)
            ==> self.hist.walks[core].contains(walk)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.hist.happy ==> {
        &&& self.wf(c)
        &&& self.inv_inflight_walks(c)
        &&& self.inv_walks_subset_of_hist_walks(c)
        &&& self.inv_cache_subset_of_hist_walks(c)
        }
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


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)

    &&& post == State {
        cache: pre.cache.insert(core, pre.walks[core].insert(walk)),
        ..pre
    }
}

pub open spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].insert(walk)),
        ..pre
    }
}

pub open spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
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
pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
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

pub open spec fn walk_next(state: State, core: Core, walk: Walk, r: usize) -> Walk {
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

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    value: usize,
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

/// Note: A valid walk's result is a region whose base and size depend on the path taken. E.g. a
/// huge page mapping results in a 2M-sized region. Invalid walks are always for a 4K-sized region.
pub open spec fn step_WalkDone(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    value: usize,
    r: usize,
    lbl: Lbl
    ) -> bool
{
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& {
    let walk_next = walk_next(pre, core, walk, r);
    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.result() == walk_result
    &&& walk_next.complete
    }

    &&& post == State {
        walks: pre.walks.insert(core, pre.walks[core].remove(walk)),
        ..pre
    }
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

    &&& post.pt_mem == pre.pt_mem
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

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
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

pub open spec fn step_Read(pre: State, post: State, c: Constants, r: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value == pre.read_from_mem_tso(core, addr, r)

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
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

/// Any transition that reads from memory takes an arbitrary usize `r`, which is used to
/// non-deterministically flip the accessed and dirty bits.
pub enum Step {
    // Mixed
    Invlpg,
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk, value: usize, r: usize },
    WalkDone { walk: Walk, value: usize, r: usize },
    // TSO
    Write,
    Writeback { core: Core },
    Read { r: usize },
    Barrier,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                            => step_Invlpg(pre, post, c, lbl),
        Step::CacheFill { core, walk }          => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }           => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, walk }         => step_CacheEvict(pre, post, c, core, walk, lbl),
        Step::WalkInit { core, vaddr }          => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, value, r } => step_WalkStep(pre, post, c, core, walk, value, r, lbl),
        Step::WalkDone { walk, value, r }       => step_WalkDone(pre, post, c, walk, value, r, lbl),
        Step::Write                             => step_Write(pre, post, c, lbl),
        Step::Writeback { core }                => step_Writeback(pre, post, c, core, lbl),
        Step::Read { r }                        => step_Read(pre, post, c, r, lbl),
        Step::Barrier                           => step_Barrier(pre, post, c, lbl),
    }
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    //&&& pre.pt_mem == ..
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

proof fn init_implies_inv(pre: State, c: Constants)
    requires init(pre, c)
    ensures pre.inv(c)
{
}

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv(c)
{}



mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl3::bit;
    use crate::spec_t::hardware::{ MASK_DIRTY_ACCESS, MASK_NEG_DIRTY_ACCESS };

    impl rl3::State {
        pub open spec fn interp(self) -> rl2::State {
            rl2::State {
                happy: self.hist.happy,
                pt_mem: self.pt_mem,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                writes: self.hist.writes,
                hist: rl2::History { pending_maps: self.hist.pending_maps },
                //polarity: self.hist.polarity,
            }
        }
    }

    impl rl3::Step {
        pub open spec fn interp(self, pre: rl3::State, post: rl3::State, lbl: Lbl) -> rl2::Step {
            if pre.hist.happy {
                match self {
                    rl3::Step::Invlpg                            => rl2::Step::Invlpg,
                    rl3::Step::CacheFill { core, walk }          => rl2::Step::Stutter,
                    rl3::Step::CacheUse { core, walk }           => rl2::Step::Stutter,
                    rl3::Step::CacheEvict { core, walk }         => rl2::Step::Stutter,
                    rl3::Step::WalkInit { core, vaddr }          => rl2::Step::WalkInit { core, vaddr },
                    rl3::Step::WalkStep { core, walk, value, r } => rl2::Step::WalkStep { core, walk },
                    rl3::Step::WalkDone { walk, value, r }       => rl2::Step::WalkDone { walk },
                    rl3::Step::Write                             => {
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
                    rl3::Step::Writeback { core }                => rl2::Step::Writeback { core },
                    rl3::Step::Read { r }                        => rl2::Step::Read,
                    rl3::Step::Barrier                           => rl2::Step::Barrier,
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
        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(pre, post, lbl), lbl)
    {
        if pre.hist.happy {
            match step {
                rl3::Step::Invlpg => {
                    assert(rl2::step_Invlpg(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheFill { core, walk }  => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheUse { core, walk }      => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::CacheEvict { core, walk }    => {
                    assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::WalkInit { core, vaddr } => {
                    assert(rl2::step_WalkInit(pre.interp(), post.interp(), c, core, vaddr, lbl))
                },
                rl3::Step::WalkStep { core, walk, value, r } => {
                    rl3_walk_next_is_rl2_walk_next(pre, core, walk, r);
                    assert(rl2::step_WalkStep(pre.interp(), post.interp(), c, core, walk, lbl));
                },
                rl3::Step::WalkDone { walk, value, r } => {
                    let core = lbl->Walk_0;
                    rl3_walk_next_is_rl2_walk_next(pre, core, walk, r);
                    assert(rl2::step_WalkDone(pre.interp(), post.interp(), c, walk, lbl));
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
                rl3::Step::Writeback { core }        => {
                    assert(rl2::step_Writeback(pre.interp(), post.interp(), c, core, lbl));
                },
                rl3::Step::Read { r }                => {
                    broadcast use lemma_mask_dirty_access_after_xor;
                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
                },
                rl3::Step::Barrier                   => {
                    assert(rl2::step_Barrier(pre.interp(), post.interp(), c, lbl));
                },
            }
        } else {
            assert(rl2::step_Sadness(pre.interp(), post.interp(), c, lbl));
        }
    }

    proof fn init_refines(pre: rl3::State, post: rl3::State, c: Constants, lbl: Lbl)
        requires
            //pre.inv(c),
            rl3::init(pre, c),
        ensures
            rl2::init(pre.interp(), c),
    {
    }

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
}


} // verus!
