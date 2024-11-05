use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, Core };
use crate::spec_t::mmu::rl4::{ Writes, Polarity, MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 3 of the MMU. Compared to layer 4, it expresses translation
// caching and non-atomic walks as a single concept, and it doesn't explicitly consider the values
// of dirty/accessed bits.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    pub writes: Writes,
    /// Current polarity: Are we doing only positive writes or only negative writes? Polarity can be
    /// flipped when neg and writes are all empty.
    /// A non-flipping write with the wrong polarity sets happy to false.
    /// Additionally tracks the current writer core.
    /// Technically we could probably infer the polarity from the write tracking but this is easier.
    pub polarity: Polarity,
}


impl State {
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize) -> usize {
        let val = match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem.read(addr),
        };
        val
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    /// The view of the memory from the writer core's perspective.
    pub open spec fn writer_mem(self) -> PTMem {
        let core = self.polarity.core();
        self.sbuf[core].fold_left(self.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    }

    pub open spec fn is_neg_write(self, addr: usize) -> bool {
        self.writer_mem().is_neg_write(addr)
    }

    pub open spec fn is_pos_write(self, addr: usize) -> bool {
        self.writer_mem().is_pos_write(addr)
    }

    // TODO: I may want/need to add these conditions as well:
    // - when unmapping directory, it must be empty
    // - the location corresponds to *exactly* one leaf entry in the page table
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, c: Constants) -> bool {
        &&& !self.can_change_polarity(c) ==> {
            // If we're not at the start of an operation, the writer must stay the same
            &&& self.polarity.core() == core
            // and the polarity must match
            &&& if self.polarity is Pos { self.is_pos_write(addr) } else { self.is_neg_write(addr) }
        }
        // The write must be to a location that's currently a leaf of the page table.
        // FIXME: i'm not sure this is doing what i want it to do.
        // TODO: maybe bad trigger
        &&& exists|path, i| #![auto]
            self.writer_mem().page_table_paths().contains(path)
            && 0 <= i < path.len() && path[i].0 == addr
    }

    pub open spec fn can_change_polarity(self, c: Constants) -> bool {
        &&& self.writes.all.is_empty()
        &&& forall|core| #![auto] c.valid_core(core) ==> self.writes.neg[core].is_empty()
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] self.walks.contains_key(core) ==> self.walks[core].finite()
        &&& forall|core| #[trigger] self.writes.neg.contains_key(core) ==> self.writes.neg[core].finite()
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.sbuf == pre.sbuf
    &&& post.writes.all === pre.writes.all.filter(|e:(Core, usize)| e.0 != core)
    &&& post.writes.neg == pre.writes.neg.insert(core, set![])
    &&& post.polarity == pre.polarity
}


// ---- Non-atomic page table walks ----

pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vbase: usize, lbl: Lbl) -> bool {
    let walk = Walk { vbase, path: seq![], complete: false };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& aligned(vbase as nat, L3_ENTRY_SIZE as nat)
    &&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
}

pub open spec fn walk_next(state: State, core: Core, walk: Walk) -> Walk {
    let vbase = walk.vbase; let path = walk.path;
    // TODO: do this better
    let addr = if path.len() == 0 {
        add(state.pt_mem.pml4, l0_bits!(vbase as u64) as usize)
    } else if path.len() == 1 {
        add(path.last().0, l1_bits!(vbase as u64) as usize)
    } else if path.len() == 2 {
        add(path.last().0, l2_bits!(vbase as u64) as usize)
    } else if path.len() == 3 {
        add(path.last().0, l3_bits!(vbase as u64) as usize)
    } else { arbitrary() };
    let value = state.read_from_mem_tso(core, addr);

    let entry = PDE { entry: value as u64, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vbase,
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
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre, core, walk);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk_next))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
}

pub open spec fn step_WalkDone(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    value: usize,
    lbl: Lbl
    ) -> bool
{
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& {
    let walk_next = walk_next(pre, core, walk);
    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.result() == walk_result
    &&& walk_next.complete
    }

    &&& post == pre
}


// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.is_this_write_happy(core, addr, c)
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.all === pre.writes.all.insert((core, addr))
    &&& post.writes.neg == if pre.is_neg_write(addr) {
            pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.writes.neg }
    // Whenever this causes polarity to change and happy isn't set to false, the
    // conditions for polarity to change are satisfied (`can_change_polarity`)
    &&& post.polarity == if pre.is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value & MASK_NEG_DIRTY_ACCESS == pre.read_from_mem_tso(core, addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    &&& post.writes.all === pre.writes.all.filter(|e:(Core, usize)| e.0 != core)
    &&& post.writes.neg == pre.writes.neg
    &&& post.polarity == pre.polarity
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Non-atomic page table walks
    WalkInit { core: Core, vbase: usize },
    WalkStep { core: Core, walk: Walk, value: usize },
    WalkDone { walk: Walk, value: usize },
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                         => step_Invlpg(pre, post, c, lbl),
        Step::WalkInit { core, vbase }       => step_WalkInit(pre, post, c, core, vbase, lbl),
        Step::WalkStep { core, walk, value } => step_WalkStep(pre, post, c, core, walk, value, lbl),
        Step::WalkDone { walk, value }       => step_WalkDone(pre, post, c, walk, value, lbl),
        Step::Write                          => step_Write(pre, post, c, lbl),
        Step::Writeback { core }             => step_Writeback(pre, post, c, core, lbl),
        Step::Read                           => step_Read(pre, post, c, lbl),
        Step::Barrier                        => step_Barrier(pre, post, c, lbl),
        Step::Stutter                        => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    if pre.happy {
        exists|step| next_step(pre, post, c, step, lbl)
    } else {
        post.happy == pre.happy
    }
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
    //if pre.happy {
    //    match step {
    //        Step::Invlpg                         => assert(post.inv(c)),
    //        Step::WalkInit { core, vbase }       => assert(post.inv(c)),
    //        Step::WalkStep { core, walk, value } => assert(post.inv(c)),
    //        Step::WalkDone { walk, value }       => assert(post.inv(c)),
    //        Step::Write                          => assert(post.inv(c)),
    //        Step::Writeback { core }             => assert(post.inv(c)),
    //        Step::Read                           => assert(post.inv(c)),
    //        Step::Barrier                        => assert(post.inv(c)),
    //        Step::Stutter                        => assert(post.inv(c)),
    //    }
    //}
}

//mod refinement {
//    use crate::spec_t::mmu::*;
//    use crate::spec_t::mmu::pt_mem::{ PTMem };
//    use crate::spec_t::mmu::rl2;
//    use crate::spec_t::mmu::rl3;
//    use crate::spec_t::mmu::rl4::{ get_first };
//
//    impl rl3::State {
//        pub open spec fn interp_pt_mem(self) -> PTMem {
//            let writers = self.writer_cores();
//            if writers.len() == 0 {
//                self.pt_mem
//            } else if writers.len() == 1 {
//                let wcore = writers.choose();
//                self.sbuf[wcore].fold_left(self.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
//            } else {
//                // implies !self.happy
//                arbitrary()
//            }
//        }
//
//        pub open spec fn interp(self) -> rl2::State {
//            rl2::State {
//                happy: self.happy,
//                pt_mem: self.interp_pt_mem(),
//                walks: self.walks,
//                writes: self.hist.writes,
//                hist: rl2::History { neg_writes: self.hist.neg_writes },
//            }
//        }
//    }
//
//    impl rl3::Step {
//        pub open spec fn interp(self) -> rl2::Step {
//            match self {
//                rl3::Step::Invlpg                         => rl2::Step::Invlpg,
//                rl3::Step::WalkInit { core, vbase }       => rl2::Step::WalkInit { core, vbase },
//                rl3::Step::WalkStep { core, walk, value } => rl2::Step::WalkStep { core, walk, value },
//                rl3::Step::WalkDone { walk, value }       => rl2::Step::WalkDone { walk, value },
//                rl3::Step::Write                          => rl2::Step::Write,
//                rl3::Step::Writeback { core }             => rl2::Step::Stutter,
//                rl3::Step::Read                           => rl2::Step::Read,
//                rl3::Step::Barrier                        => rl2::Step::Barrier,
//                rl3::Step::Stutter                        => rl2::Step::Stutter,
//            }
//        }
//    }
//
//    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
//        requires
//            pre.happy,
//            pre.inv(c),
//            rl3::next_step(pre, post, c, step, lbl),
//        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(), lbl)
//    {
//        match step {
//            rl3::Step::Invlpg => {
//                admit(); // XXX
//                assert(rl2::step_Invlpg(pre.interp(), post.interp(), c, lbl));
//            },
//            rl3::Step::WalkInit { core, vbase } => {
//                assert(rl2::step_WalkInit(pre.interp(), post.interp(), c, core, vbase, lbl));
//            },
//            rl3::Step::WalkStep { core, walk, value } => {
//                admit();
//                assert(rl2::step_WalkStep(pre.interp(), post.interp(), c, core, walk, value, lbl));
//            },
//            rl3::Step::WalkDone { walk, value } => {
//                admit();
//                assert(rl2::step_WalkDone(pre.interp(), post.interp(), c, walk, value, lbl));
//            },
//            rl3::Step::Write => {
//                // TODO: This doesn't refine in the case where (pre.happy && !post.happy)
//                admit();
//                assert(rl2::step_Write(pre.interp(), post.interp(), c, lbl));
//            },
//            rl3::Step::Writeback { core } => {
//                admit();
//                assert(pre.no_other_writers(core));
//                lemma_pt_mem_fold_writeback(pre, post, c, core);
//                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
//            },
//            rl3::Step::Read => {
//                admit(); // XXX
//                let Lbl::Read(core, addr, value) = lbl else { arbitrary() };
//                if pre.no_other_writers(core) {
//                    assert(pre.interp().no_other_writers(core));
//                    lemma_rl3_read_from_mem_tso_conditions2(pre, c, core, addr);
//                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
//                } else if !pre.write_addrs().contains(addr) {
//                    lemma_rl3_read_from_mem_tso_conditions1(pre, c, core, addr);
//                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
//                }
//                assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
//            },
//            rl3::Step::Barrier                   => {
//                admit(); // XXX
//                assert(rl2::step_Barrier(pre.interp(), post.interp(), c, lbl));
//            },
//            rl3::Step::Stutter                   => {
//                assert(post.pt_mem == pre.pt_mem);
//                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
//            },
//        }
//    }
//
//    proof fn next_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, lbl: Lbl)
//        requires
//            pre.inv(c),
//            rl3::next(pre, post, c, lbl),
//        ensures
//            rl2::next(pre.interp(), post.interp(), c, lbl),
//    {
//        if pre.happy {
//            let step = choose|step: rl3::Step| rl3::next_step(pre, post, c, step, lbl);
//            next_step_refines(pre, post, c, step, lbl);
//        }
//    }
//
//
//    proof fn lemma_pt_mem_fold_writeback(pre: rl3::State, post: rl3::State, c: rl3::Constants, core: Core)
//        requires
//            pre.happy,
//            pre.inv(c),
//            c.valid_core(core),
//            pre.sbuf[core].len() > 0,
//            pre.no_other_writers(core),
//            post.pt_mem == pre.pt_mem.write(pre.sbuf[core][0].0, pre.sbuf[core][0].1),
//            post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first()),
//        ensures
//            post.sbuf[core].fold_left(pre.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
//                == pre.sbuf[core].fold_left(post.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
//    {
//        admit();
//    }
//
//    proof fn lemma_rl3_read_from_mem_tso_conditions1(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
//        requires
//            state.happy,
//            state.inv(c),
//            !state.write_addrs().contains(addr),
//            c.valid_core(core),
//        ensures get_first(state.sbuf[core], addr) is None
//    {
//        admit();
//        assert(get_first(state.sbuf[core], addr) is None);
//    }
//
//    proof fn lemma_rl3_read_from_mem_tso_conditions2(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
//        requires
//            state.happy,
//            state.inv(c),
//            state.no_other_writers(core),
//            c.valid_core(core),
//        ensures
//            match get_first(state.sbuf[core], addr) {
//                Some(v) => v,
//                None    => state.pt_mem.read(addr),
//            } == state.interp().pt_mem.read(addr)
//    {
//        let wcore = state.writer_cores().choose();
//        assume(wcore == core);
//        assume(state.writer_cores().len() == 1);
//        // Should follow trivially from previous two
//        assume(state.interp().pt_mem == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1)));
//        //match get_first(state.sbuf[core], addr) {
//        //    Some(v) => v,
//        //    None    => state.pt_mem[addr],
//        //} == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))@[addr]
//        admit();
//        assert(get_first(state.sbuf[core], addr) is None);
//    }
//
//}


} // verus!
