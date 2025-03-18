use vstd::prelude::*;

use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu;
use crate::spec_t::os_ext;
use crate::spec_t::mmu::defs::{ PageTableEntryExec, Core, MemRegionExec };
use crate::theorem::RLbl;
use crate::spec_t::mmu::rl3::refinement::to_rl1;

verus! {

// TODO: This is from the verus test suite. Can we have it in vstd?
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub tracked struct Prophecy<T> { _t: core::marker::PhantomData<T> }

impl<T> Prophecy<T> {
    #[verifier::prophetic]
    pub open spec fn value(&self) -> T;

    pub open spec fn may_resolve(&self) -> bool;

    #[verifier::external_body]
    pub proof fn new() -> (tracked s: Self)
        ensures s.may_resolve()
    { unimplemented!() }

    #[verifier::external_body]
    pub proof fn resolve(tracked &mut self, value: T)
        requires old(self).may_resolve(),
        ensures !self.may_resolve(),
            self.value() == old(self).value(),
            self.value() == value,
    { unimplemented!() }
}

pub enum Progress {
    Unready,
    Ready,
    TokenWithdrawn
}

#[verifier(external_body)]
pub tracked struct Token {}

impl os::Step {
    pub open spec fn is_actor_step(self, c: Core) -> bool {
        match self {
            os::Step::MMU => false,
            os::Step::MemOp { core, .. } |
            os::Step::ReadPTMem { core, .. } |
            os::Step::Barrier { core, .. } |
            os::Step::Invlpg { core, .. } |
            os::Step::MapStart { core, .. } |
            os::Step::MapOpStart { core, .. } |
            os::Step::Allocate { core, .. } |
            os::Step::MapOpStutter { core, .. } |
            os::Step::MapOpChange { core, .. } |
            os::Step::MapNoOp { core, .. } |
            os::Step::MapEnd { core, .. } |
            os::Step::UnmapStart { core, .. } |
            os::Step::UnmapOpStart { core, .. } |
            os::Step::Deallocate { core, .. } |
            os::Step::UnmapOpChange { core, .. } |
            os::Step::UnmapOpStutter { core, .. } |
            os::Step::UnmapOpEnd { core, .. } |
            os::Step::UnmapInitiateShootdown { core, .. } |
            os::Step::AckShootdownIPI { core, .. } |
            os::Step::UnmapEnd { core, .. } => core == c,
        }
    }
}


pub open spec fn concurrent_trs(pre: os::State, post: os::State, c: os::Constants, core: Core, pidx: nat) -> bool
    decreases pidx
{
    if pidx == 0 {
        post == pre
    } else {
        exists|state: os::State, step, lbl| {
            &&& concurrent_trs(pre, state, c, core, sub(pidx, 1)) 
            &&& os::next_step(c, state, post, step, lbl)
            &&& !step.is_actor_step(core)
        }
    }
}

// We'll use `concurrent_trs` as an inductive-ish predicate, so let's prove the corresponding intro
// and induction rules:

proof fn lemma_concurrent_trs_eq_intro(pre: os::State, c: os::Constants, core: Core)
    ensures concurrent_trs(pre, pre, c, core, 0)
{}

proof fn lemma_concurrent_trs_step_intro(pre: os::State, mid: os::State, c: os::Constants, core: Core, pidx: nat, step: os::Step, lbl: RLbl, post: os::State)
    requires
        concurrent_trs(pre, mid, c, core, pidx),
        os::next_step(c, mid, post, step, lbl),
        !step.is_actor_step(core),
    ensures
        concurrent_trs(pre, post, c, core, pidx + 1)
{}

proof fn lemma_concurrent_trs_induct(pre: os::State, post: os::State, c: os::Constants, core: Core, pidx: nat, pred: spec_fn(os::State, os::State) -> bool)
    requires
        concurrent_trs(pre, post, c, core, pidx),
        forall|s| #[trigger] pred(s, s),
        forall|pre, mid, pidx, step, lbl, post|
            pred(pre, mid)
            && concurrent_trs(pre, mid, c, core, pidx)
            && os::next_step(c, mid, post, step, lbl)
            && !step.is_actor_step(core)
            ==> pred(pre, post)
    ensures pred(pre, post)
    decreases pidx
{
    if pre == post {
    } else {
        let (state, step, lbl): (os::State, os::Step, RLbl) = choose|state: os::State, step, lbl| {
            &&& concurrent_trs(pre, state, c, core, sub(pidx, 1)) 
            &&& os::next_step(c, state, post, step, lbl)
            &&& !step.is_actor_step(core)
        };
        lemma_concurrent_trs_induct(pre, state, c, core, sub(pidx, 1), pred);
    }
}

/// "What do we know about how concurrent transitions can change the state if we're holding the
/// lock?"
pub proof fn lemma_concurrent_trs(pre: os::State, post: os::State, c: os::Constants, core: Core, pidx: nat)
    requires
        concurrent_trs(pre, post, c, core, pidx),
        pre.inv(c),
        pre.os_ext.lock == Some(core),
        //c.valid_core(core),
    ensures
        unchanged_state_during_concurrent_trs(pre, post),
        post.core_states[core] == pre.core_states[core],
        post.inv(c),
{
    let pred = |pre: os::State, post: os::State|
        pre.inv(c) && pre.os_ext.lock == Some(core) ==> {
            &&& unchanged_state_during_concurrent_trs(pre, post)
            &&& post.core_states[core] == pre.core_states[core]
            &&& post.os_ext.lock == pre.os_ext.lock
            &&& post.inv(c)
        };
    assert forall|s| #[trigger] pred(s, s) by {};
    assert forall|pre, mid, pidx, step, lbl, post|
        pred(pre, mid)
        && concurrent_trs(pre, mid, c, core, pidx)
        && os::next_step(c, mid, post, step, lbl)
        && !step.is_actor_step(core)
        implies pred(pre, post)
    by {
        if pre.inv(c) && pre.os_ext.lock == Some(core) {
            os_invariant::next_preserves_inv(c, mid, post, lbl);
            broadcast use to_rl1::next_refines;
            assert(unchanged_state_during_concurrent_trs(pre, mid));
            match step {
                //os::Step::MMU                                          => admit(),
                //os::Step::MemOp { core }                               => admit(),
                //os::Step::ReadPTMem { core, paddr, value }             => admit(),
                os::Step::Barrier { core }                             => {
                    // TODO: needs invariant that ties writes/pending_maps to lock
                    assume(post.mmu@.writes       == mid.mmu@.writes);
                    assume(post.mmu@.pending_maps == mid.mmu@.pending_maps);
                },
                os::Step::Invlpg { core, vaddr }                       => {
                    // TODO: needs invariant that ties writes/pending_maps to lock
                    assume(post.mmu@.writes       == mid.mmu@.writes);
                    assume(post.mmu@.pending_maps == mid.mmu@.pending_maps);
                },
                //os::Step::MapStart { core }                            => admit(),
                //os::Step::MapOpStart { core }                          => admit(),
                //os::Step::Allocate { core, res }                       => admit(),
                //os::Step::MapOpStutter { core, paddr, value }          => admit(),
                //os::Step::MapOpEnd { core, paddr, value, result }      => admit(),
                //os::Step::MapEnd { core }                              => admit(),
                //os::Step::UnmapStart { core }                          => admit(),
                //os::Step::UnmapOpStart { core }                        => admit(),
                //os::Step::Deallocate { core, reg }                     => admit(),
                //os::Step::UnmapOpChange { core, paddr, value, result } => admit(),
                //os::Step::UnmapOpStutter { core, paddr, value }        => admit(),
                //os::Step::UnmapOpEnd { core }                          => admit(),
                //os::Step::UnmapInitiateShootdown { core }              => admit(),
                //os::Step::AckShootdownIPI { core }                     => admit(),
                //os::Step::UnmapEnd { core }                            => admit(),
                _ => {},
            }
        }
    };
    lemma_concurrent_trs_induct(pre, post, c, core, pidx, pred);
}


impl Token {
    // User-space thread
    pub spec fn thread(self) -> nat;
    pub spec fn consts(self) -> os::Constants;
    pub spec fn st(self) -> os::State;
    pub spec fn steps(self) -> Seq<RLbl>;
    pub spec fn progress(self) -> Progress;
    pub spec fn on_first_step(self) -> bool;

    pub open spec fn core(self) -> Core {
        self.consts().ult2core[self.thread()]
    }

    pub open spec fn withdraw_token(self, new: Token) -> bool {
        &&& new.consts() == self.consts()
        &&& new.thread() == self.thread()
        &&& new.st() == self.st()
        &&& new.steps() == self.steps()
        &&& new.progress() is TokenWithdrawn
        &&& new.on_first_step() == self.on_first_step()
    }


    pub proof fn do_concurrent_trs(tracked &mut self) -> (pidx: nat)
        requires
            old(self).progress() is Unready,
        ensures
            self.progress() is Ready,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.steps() == old(self).steps(),
            self.on_first_step() == old(self).on_first_step(),
            concurrent_trs(old(self).st(), self.st(), old(self).consts(), old(self).core(), pidx),
    { admit(); arbitrary() } // axiom



    // Take MMU steps

    #[verifier(external_body)] // axiom
    pub proof fn get_mmu_token(tracked &mut self) -> (tracked tok: mmu::rl3::code::Token)
        requires
            !old(self).on_first_step(),
            old(self).steps().len() > 0,
            old(self).progress() is Ready,
        ensures
            old(self).withdraw_token(*self),
            tok.pre() == old(self).st().mmu,
            tok.consts() == old(self).consts().mmu,
            tok.core() == old(self).core(),
            tok.tstate() is Init,
    { unimplemented!() }

    pub proof fn register_internal_step_mmu(
        tracked &mut self,
        tracked tok: &mut mmu::rl3::code::Token,
        post: os::State
    )
        requires
            old(tok).tstate() is ProphecyMade,
            os::next(old(self).consts(), old(self).st(), post, RLbl::Tau),
            post.os_ext == old(self).st().os_ext,
            post.mmu == old(tok).post(),
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps(),
            self.progress() == old(self).progress(),
            old(tok).set_validated(*tok),
    { admit(); } // axiom

    pub proof fn register_external_step_mmu(
        tracked &mut self,
        tracked tok: &mut mmu::rl3::code::Token,
        post: os::State
    )
        requires
            old(tok).tstate() is ProphecyMade,
            os::next(old(self).consts(), old(self).st(), post, old(self).steps().first()),
            post.os_ext == old(self).st().os_ext,
            post.mmu == old(tok).post(),
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.progress() == old(self).progress(),
            old(tok).set_validated(*tok),
    { admit(); } // axiom

    pub proof fn return_mmu_token(tracked &mut self, tracked tok: mmu::rl3::code::Token)
        requires tok.tstate() is Spent,
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.thread() == old(self).thread(),
            self.consts() == old(self).consts(),
            self.st() == old(self).st(),
            self.steps() == old(self).steps(),
            self.progress() is Unready,
    { admit(); } // axiom



    // Take os_ext steps

    #[verifier(external_body)]
    pub proof fn get_osext_token(tracked &mut self) -> (tracked tok: os_ext::code::Token)
        requires
            !old(self).on_first_step(),
            old(self).steps().len() > 0,
            old(self).progress() is Ready,
        ensures
            old(self).withdraw_token(*self),
            tok.consts() == old(self).consts().os_ext(),
            tok.pre() == old(self).st().os_ext,
            tok.core() == old(self).core(),
            tok.tstate() is Init,
    { unimplemented!() } // axiom

    pub proof fn register_internal_step_osext(
        tracked &mut self,
        tracked tok: &mut os_ext::code::Token,
        post: os::State
    )
        requires
            old(tok).tstate() is ProphecyMade,
            os::next(old(self).consts(), old(self).st(), post, RLbl::Tau),
            post.mmu == old(self).st().mmu,
            post.os_ext == old(tok).post(),
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps(),
            self.progress() == old(self).progress(),
            old(tok).set_valid(*tok),
    { admit(); } // axiom

    pub proof fn register_external_step_osext(
        tracked &mut self,
        tracked tok: &mut os_ext::code::Token,
        post: os::State
    )
        requires
            old(tok).tstate() is ProphecyMade,
            os::next(old(self).consts(), old(self).st(), post, old(self).steps().first()),
            post.mmu == old(self).st().mmu,
            post.os_ext == old(tok).post(),
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.progress() == old(self).progress(),
            old(tok).set_valid(*tok),
    { admit(); } // axiom

    pub proof fn return_osext_token(tracked &mut self, tracked tok: os_ext::code::Token)
        requires tok.tstate() is Spent,
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.thread() == old(self).thread(),
            self.consts() == old(self).consts(),
            self.st() == old(self).st(),
            self.steps() == old(self).steps(),
            self.progress() is Unready,
    { admit(); } // axiom


    /// Register a step that corresponds to stutter in both mmu and os_ext.
    pub proof fn register_external_step(tracked &mut self, post: os::State)
        requires
            old(self).progress() is Ready,
            os::next(old(self).consts(), old(self).st(), post, old(self).steps().first()),
            post.os_ext == old(self).st().os_ext,
            post.mmu == old(self).st().mmu,
        ensures
            !self.on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.progress() == Progress::Unready,
    { admit(); } // axiom
}

pub trait CodeVC {
    // We specify the steps to be taken as labels. But the label for `MapEnd` includes the return
    // value, which we want to be equal to the result returned by the function. But we can't
    // specify this in the requires clause because we can't refer to the result there. Instead we
    // use an additional prophetic argument, which carries the return value and to which we can
    // refer in the requires clause.
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: (Result<(),()>, Tracked<Token>))
        requires
            // State machine VC preconditions
            os::step_Map_enabled(vaddr as nat, pte@),
            tok.st().inv(tok.consts()),
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is Idle,
            tok.steps() === seq![
                RLbl::MapStart { thread_id: tok.thread(), vaddr: vaddr as nat, pte: pte@ },
                RLbl::MapEnd { thread_id: tok.thread(), vaddr: vaddr as nat, result: proph_res.value() }
            ],
            tok.on_first_step(),
            tok.progress() is Unready,
            // Caller preconditions
            proph_res.may_resolve(),
            pml4 == tok.st().mmu@.pt_mem.pml4,
        ensures
            res.0 == proph_res.value(),
            res.1@.steps() === seq![],
            res.1@.progress() is Ready,
    ;

    /// This function returns the memory region that was unmapped but that value should be
    /// considered a hint as it's not verified.
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        core: Core,
        vaddr: usize,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: (Result<MemRegionExec,()>, Tracked<Token>))
        requires
            tok.core() == core,
            tok.st().core_states[core] is Idle,
            tok.steps() === seq![
                RLbl::UnmapStart { thread_id: tok.thread(), vaddr: vaddr as nat },
                RLbl::UnmapEnd { thread_id: tok.thread(), vaddr: vaddr as nat, result: proph_res.value() }
            ],
            tok.on_first_step(),
            tok.progress() is Unready,
            proph_res.may_resolve(),
        ensures
            res.0 is Ok <==> proph_res.value() is Ok,
            res.1@.steps() === seq![],
            res.1@.progress() is Ready,
    ;
}

pub open spec fn unchanged_state_during_concurrent_trs(pre: os::State, post: os::State) -> bool {
    &&& post.mmu@.happy        == pre.mmu@.happy
    &&& post.mmu@.pt_mem       == pre.mmu@.pt_mem
    &&& post.mmu@.writes       == pre.mmu@.writes
    &&& post.mmu@.pending_maps == pre.mmu@.pending_maps
}

} // verus!
