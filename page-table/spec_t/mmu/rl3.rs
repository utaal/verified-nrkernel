use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ get_first, MASK_DIRTY_ACCESS };
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::definitions_t::{ aligned, Core };

verus! {

// This file contains refinement layer 3 of the MMU, which expresses translation caching and
// non-atomicity of page walks as a single concept.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    /// History variables
    pub hist: History,
    //pub proph: Prophecy,
}

pub struct History {
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    pub neg_writes: Map<Core, Set<usize>>,
}

//pub struct Prophecy {
//    /// Prophesied memories after future writeback transitions
//    pub pt_mems: Seq<PTMem>,
//}

impl State {
    /// This predicate is true whenever `value` is a value that might be read from the address
    /// `addr` on core `core`. See rl4.rs for explanation.
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, value: usize) -> bool {
        let val = match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem.read(addr),
        };
        value & MASK_DIRTY_ACCESS == val & MASK_DIRTY_ACCESS
    }

    /// The page table walker behaves the same no matter what the dirty and accessed bits are set
    /// to. Thus we can use this more convenient read function where we simply mask away those two
    /// bits.
    pub open spec fn read_from_mem_tso_mask(self, core: Core, addr: usize) -> usize {
        (match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem.read(addr),
        }) & MASK_DIRTY_ACCESS
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    /// Is true if only this core's store buffer is non-empty.
    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores().subset_of(set![core])
    }

    pub open spec fn is_neg_write(self, addr: usize) -> bool {
        &&& self.pt_mem.page_addrs().contains_key(addr)
        &&& !(self.pt_mem.page_addrs()[addr] is Empty)
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.hist.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn write_addrs(self) -> Set<usize> {
        self.hist.writes.map(|x:(_,_)| x.1)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core,value| #[trigger] self.hist.writes.contains((core,value)) ==> c.valid_core(core)
    }

    pub open spec fn inv_sbuf_subset_writes(self, c: Constants) -> bool {
        forall|core: Core, addr: usize, value: usize|
            !self.hist.writes.contains((core, addr)) ==> !self.sbuf[core].to_set().contains((addr, value))
    }

    pub open spec fn inv_writer_cores(self, c: Constants) -> bool {
        &&& self.writer_cores().len() <= 1
        &&& forall|core| #[trigger] c.valid_core(core) && self.sbuf[core].len() > 0 ==> self.writer_cores().contains(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        //&&& self.inv_unchanged_walks_match_memory(c)
        &&& self.inv_sbuf_subset_writes(c)
        &&& self.inv_writer_cores(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    // .. and cancels inflight walks.
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf

    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.neg_writes == pre.hist.neg_writes.insert(core, set![])
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}


// ---- Non-atomic page table walks ----

// FIXME: this should make sure the alignment of va fits with the PTE
pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, va: usize, lbl: Lbl) -> bool {
    let walk = Walk { va, path: seq![] };
    &&& lbl is Tau

    &&& c.valid_core(core)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
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
    let (res, addr) = walk.next(pre.pt_mem.pml4, value);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& res is Incomplete

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(res.walk()))

    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
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
    let (res, addr) = walk.next(pre.pt_mem.pml4, value);
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk.pte() == walk_result
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& !(res is Incomplete)

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks

    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".

pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks

    &&& post.hist.writes == pre.hist.writes.insert((core, addr))
    &&& post.hist.neg_writes == if pre.is_neg_write(addr) {
            pre.hist.neg_writes.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.hist.neg_writes }
    //&&& post.proph.pt_mems == pre.proph.pt_mems.push(proph)
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    //// Prophetic enabling condition
    //&&& pre.proph.pt_mems.len() >= 1
    //&&& post.pt_mem == pre.proph.pt_mems[0]

    &&& post.happy == pre.happy
    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks

    &&& post.hist.writes == pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems.drop_first()
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks

    &&& post.hist.writes == pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks

    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.neg_writes == pre.hist.neg_writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Non-atomic page table walks
    WalkInit { core: Core, va: usize },
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
        Step::WalkInit { core, va }          => step_WalkInit(pre, post, c, core, va, lbl),
        Step::WalkStep { core, walk, value } => step_WalkStep(pre, post, c, core, walk, value, lbl),
        Step::WalkDone { walk, value }       => step_WalkDone(pre, post, c, walk, value, lbl),
        Step::Write                          => step_Write(pre, post, c, lbl),
        Step::Writeback { core }             => step_Writeback(pre, post, c, core, lbl),
        Step::Read                           => step_Read(pre, post, c, lbl),
        Step::Barrier                        => step_Barrier(pre, post, c, lbl),
        Step::Stutter                        => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants) -> bool {
    pre.happy ==> exists|step, lbl| next_step(pre, post, c, step, lbl)
}

proof fn init_implies_inv(pre: State, c: Constants)
    requires pre.init()
    ensures pre.inv(c)
{ admit(); }

proof fn next_step_preserves_inv_sbuf_subset_writes(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_sbuf_subset_writes(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_sbuf_subset_writes(c)
{
    match step {
        Step::Invlpg => assert(post.inv_sbuf_subset_writes(c)),
        Step::WalkInit { core, va } => assert(post.inv_sbuf_subset_writes(c)),
        Step::WalkStep { core, walk, value } => assert(post.inv_sbuf_subset_writes(c)),
        Step::WalkDone { walk, value } => assert(post.inv_sbuf_subset_writes(c)),
        Step::Write => {
            let core = lbl->Write_0;
            let addr = lbl->Write_1;
            //assert forall|core2: Core, addr: usize, value: usize| #![auto]
            //    c.valid_core(core2) && post.sbuf[core2].to_set().contains((addr, value))
            //        implies post.hist.writes.contains((core2, addr))
            //by {
            //    if core2 == core && pre.sbuf[core].to_set().contains((addr, value)) { }
            //};
            assert forall|core2: Core, addr2: usize, value: usize|
                !post.hist.writes.contains((core2, addr2))
                implies !post.sbuf[core2].to_set().contains((addr2, value))
            by {
                admit();
                assert(c.valid_core(core2));
                if core2 == core && addr2 == addr {
                } else {
                    assert(!post.hist.writes.contains((core2, addr2)));
                }
            };
            assert(post.inv_sbuf_subset_writes(c))
        },
        Step::Writeback { core } => {
            // should be easy
            assume(post.inv_sbuf_subset_writes(c));
        },
        Step::Read => {
            assert(post.inv_sbuf_subset_writes(c));
        },
        Step::Barrier => {
            assert(post.inv_sbuf_subset_writes(c));
        },
        Step::Stutter => {
            assert(post.inv_sbuf_subset_writes(c));
        },
    }
}

proof fn next_step_preserves_inv_writer_cores(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.happy ==> post.inv_writer_cores(c)
{
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            assert(pre.writer_cores().len() <= 1);
            lemma_writer_cores_filter(pre.hist.writes, core);
            assert(post.writer_cores().len() <= pre.writer_cores().len());

            // Conjunct 1
            assert(post.writer_cores().len() <= 1);

            admit();
            // Conjunct 2
            assert forall|core| #[trigger] c.valid_core(core) && post.sbuf[core].len() > 0
                implies post.writer_cores().contains(core)
            by {
                assert(forall|core| #[trigger] c.valid_core(core) && post.sbuf[core].len() > 0 ==> pre.sbuf[core].len() > 0);
                assert(forall|core| post.writer_cores().contains(core) ==> pre.writer_cores().contains(core));
                assert(pre.writer_cores().contains(core));
            };
            assert(post.inv_writer_cores(c));
        },
        Step::WalkInit { core, va } => assert(post.inv_writer_cores(c)),
        Step::WalkStep { core, walk, value } => assert(post.inv_writer_cores(c)),
        Step::WalkDone { walk, value } => assert(post.inv_writer_cores(c)),
        Step::Write => {
            let core = lbl->Write_0;
            broadcast use lemma_writer_cores_insert;
            assert(pre.writer_cores() === set![] || pre.writer_cores() === set![core]);
            assert(post.inv_writer_cores(c));
            //if pre.no_other_writers(core) {
            //    if pre.writer_cores() === set![] {
            //        assert(post.inv_writer_cores(c))
            //    } else {
            //        assert(pre.writer_cores() === set![core]);
            //        assert(post.inv_writer_cores(c))
            //    }
            //} else {
            //    assert(post.inv_writer_cores(c))
            //}
        },
        Step::Writeback { core } => {
            assert(post.inv_writer_cores(c));
        },
        Step::Read => {
            assert(post.inv_writer_cores(c));
        },
        Step::Barrier => {
            let core = lbl->Barrier_0;
            assert(pre.writer_cores().len() <= 1);
            lemma_writer_cores_filter(pre.hist.writes, core);
            assert(post.writer_cores().len() <= pre.writer_cores().len());
            admit();
            assert(post.inv_writer_cores(c));
        },
        Step::Stutter => {
            assert(post.inv_writer_cores(c));
        },
    }
}

// TODO: Any way to reasonably broadcast this?
proof fn lemma_writer_cores_filter(s: Set<(Core, usize)>, core: Core)
    ensures
        s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).subset_of(s.map(|x:(_,_)| x.0)),
        s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).len() <= s.map(|x:(_,_)| x.0).len()
{
    assert(s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).subset_of(s.map(|x:(_,_)| x.0)));
    admit();
}

broadcast proof fn lemma_writer_cores_insert(s: Set<(Core, usize)>, core: Core, addr: usize)
    // probably need finite
    //requires s.finite()
    ensures (#[trigger] s.insert((core, addr))).map(|x:(_,_)| x.0) == s.map(|x:(_,_)| x.0).insert(core)
{
    admit();
}


mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::pt_mem::{ PTMem };
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl4::{ get_first };

    impl rl3::State {
        pub open spec fn interp_pt_mem(self) -> PTMem {
            let writers = self.writer_cores();
            if writers.len() == 0 {
                self.pt_mem
            } else if writers.len() == 1 {
                let wcore = writers.choose();
                self.sbuf[wcore].fold_left(self.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
            } else {
                // implies !self.happy
                arbitrary()
            }
        }

        pub open spec fn interp(self) -> rl2::State {
            rl2::State {
                happy: self.happy,
                pt_mem: self.interp_pt_mem(),
                walks: self.walks,
                writes: self.hist.writes,
                hist: rl2::History { neg_writes: self.hist.neg_writes },
            }
        }
    }

    impl rl3::Step {
        pub open spec fn interp(self) -> rl2::Step {
            match self {
                rl3::Step::Invlpg                         => rl2::Step::Invlpg,
                rl3::Step::WalkInit { core, va }          => rl2::Step::WalkInit { core, va },
                rl3::Step::WalkStep { core, walk, value } => rl2::Step::WalkStep { core, walk, value },
                rl3::Step::WalkDone { walk, value }       => rl2::Step::WalkDone { walk, value },
                rl3::Step::Write                          => rl2::Step::Write,
                rl3::Step::Writeback { core }             => rl2::Step::Stutter,
                rl3::Step::Read                           => rl2::Step::Read,
                rl3::Step::Barrier                        => rl2::Step::Barrier,
                rl3::Step::Stutter                        => rl2::Step::Stutter,
            }
        }
    }

    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
        requires
            pre.happy,
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(), lbl)
    {
        match step {
            rl3::Step::Invlpg => {
                admit(); // XXX
                assert(rl2::step_Invlpg(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::WalkInit { core, va } => {
                assert(rl2::step_WalkInit(pre.interp(), post.interp(), c, core, va, lbl));
            },
            rl3::Step::WalkStep { core, walk, value } => {
                admit();
                assert(rl2::step_WalkStep(pre.interp(), post.interp(), c, core, walk, value, lbl));
            },
            rl3::Step::WalkDone { walk, value } => {
                admit();
                assert(rl2::step_WalkDone(pre.interp(), post.interp(), c, walk, value, lbl));
            },
            rl3::Step::Write => {
                // TODO: This doesn't refine in the case where (pre.happy && !post.happy)
                admit();
                assert(rl2::step_Write(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Writeback { core } => {
                admit();
                assert(pre.no_other_writers(core));
                lemma_pt_mem_fold_writeback(pre, post, c, core);
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Read => {
                admit(); // XXX
                let Lbl::Read(core, addr, value) = lbl else { arbitrary() };
                if pre.no_other_writers(core) {
                    assert(pre.interp().no_other_writers(core));
                    lemma_rl3_read_from_mem_tso_conditions2(pre, c, core, addr);
                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
                } else if !pre.write_addrs().contains(addr) {
                    lemma_rl3_read_from_mem_tso_conditions1(pre, c, core, addr);
                    assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
                }
                assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Barrier                   => {
                admit(); // XXX
                assert(rl2::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Stutter                   => {
                assert(post.pt_mem == pre.pt_mem);
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    proof fn next_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants)
        requires
            pre.inv(c),
            rl3::next(pre, post, c),
        ensures
            rl2::next(pre.interp(), post.interp(), c),
    {
        if pre.happy {
            // TODO: ...
            assume(exists|x:(rl3::Step, Lbl)| #[trigger] rl3::next_step(pre, post, c, x.0, x.1));
            let (step, lbl) = choose|x:(rl3::Step, Lbl)| #[trigger] rl3::next_step(pre, post, c, x.0, x.1);
            next_step_refines(pre, post, c, step, lbl);
        }
    }


    proof fn lemma_pt_mem_fold_writeback(pre: rl3::State, post: rl3::State, c: rl3::Constants, core: Core)
        requires
            pre.happy,
            pre.inv(c),
            c.valid_core(core),
            pre.sbuf[core].len() > 0,
            pre.no_other_writers(core),
            post.pt_mem == pre.pt_mem.write(pre.sbuf[core][0].0, pre.sbuf[core][0].1),
            post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first()),
        ensures
            post.sbuf[core].fold_left(pre.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
                == pre.sbuf[core].fold_left(post.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    {
        admit();
    }

    proof fn lemma_rl3_read_from_mem_tso_conditions1(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
        requires
            state.happy,
            state.inv(c),
            !state.write_addrs().contains(addr),
            c.valid_core(core),
        ensures get_first(state.sbuf[core], addr) is None
    {
        admit();
        assert(get_first(state.sbuf[core], addr) is None);
    }

    proof fn lemma_rl3_read_from_mem_tso_conditions2(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
        requires
            state.happy,
            state.inv(c),
            state.no_other_writers(core),
            c.valid_core(core),
        ensures
            match get_first(state.sbuf[core], addr) {
                Some(v) => v,
                None    => state.pt_mem.read(addr),
            } == state.interp().pt_mem.read(addr)
    {
        let wcore = state.writer_cores().choose();
        assume(wcore == core);
        assume(state.writer_cores().len() == 1);
        // Should follow trivially from previous two
        assume(state.interp().pt_mem == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1)));
        //match get_first(state.sbuf[core], addr) {
        //    Some(v) => v,
        //    None    => state.pt_mem[addr],
        //} == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))@[addr]
        admit();
        assert(get_first(state.sbuf[core], addr) is None);
    }

}


} // verus!
