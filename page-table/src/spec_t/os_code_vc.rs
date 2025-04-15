#![cfg_attr(verus_keep_ghost, verus::trusted)]
// trusted: VCs for implementation
use vstd::prelude::*;

use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu;
use crate::spec_t::os_ext;
use crate::spec_t::mmu::defs::{ PageTableEntryExec, Core, MemRegionExec };
use crate::theorem::RLbl;
use crate::spec_t::mmu::rl3::refinement::to_rl1;

verus! {

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
            os::Step::UnmapOpFail { core, .. } |
            os::Step::UnmapInitiateShootdown { core, .. } |
            os::Step::UnmapWaitShootdown { core } |
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

/// "What do we know about how concurrent transitions can change the state if we're *not* holding
/// the lock?"
pub proof fn lemma_concurrent_trs_no_lock(pre: os::State, post: os::State, c: os::Constants, core: Core, pidx: nat)
    requires
        concurrent_trs(pre, post, c, core, pidx),
        pre.inv(c),
        //c.valid_core(core),
    ensures
        post.mmu@.pt_mem.pml4 == pre.mmu@.pt_mem.pml4,
        post.core_states[core] == pre.core_states[core],
        post.inv(c),
{
    let pred = |pre: os::State, post: os::State|
        pre.inv(c) ==> {
            &&& post.mmu@.pt_mem.pml4 == pre.mmu@.pt_mem.pml4
            &&& post.core_states[core] == pre.core_states[core]
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
        if pre.inv(c) {
            os_invariant::next_preserves_inv(c, mid, post, lbl);
            broadcast use to_rl1::next_refines;
        }
    };
    lemma_concurrent_trs_induct(pre, post, c, core, pidx, pred);
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
        unchanged_state_during_concurrent_trs(pre, post, core),
        post.core_states[core] == pre.core_states[core],
        post.inv(c),
{
    let pred = |pre: os::State, post: os::State|
        pre.inv(c) && pre.os_ext.lock == Some(core) ==> {
            &&& unchanged_state_during_concurrent_trs(pre, post, core)
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
            assert(unchanged_state_during_concurrent_trs(pre, mid, core));
            //match step {
            //    //os::Step::MMU                                          => admit(),
            //    //os::Step::MemOp { core }                               => admit(),
            //    //os::Step::ReadPTMem { core, paddr, value }             => admit(),
            //    //os::Step::Barrier { core }                             => {},
            //    //os::Step::Invlpg { core, vaddr }                       => {},
            //    //os::Step::MapStart { core }                            => admit(),
            //    //os::Step::MapOpStart { core }                          => admit(),
            //    //os::Step::Allocate { core, res }                       => admit(),
            //    //os::Step::MapOpStutter { core, paddr, value }          => admit(),
            //    //os::Step::MapOpEnd { core, paddr, value, result }      => admit(),
            //    //os::Step::MapEnd { core }                              => admit(),
            //    //os::Step::UnmapStart { core }                          => admit(),
            //    //os::Step::UnmapOpStart { core }                        => admit(),
            //    //os::Step::Deallocate { core, reg }                     => admit(),
            //    //os::Step::UnmapOpChange { core, paddr, value, result } => admit(),
            //    //os::Step::UnmapOpStutter { core, paddr, value }        => admit(),
            //    //os::Step::UnmapOpFail { core }                          => admit(),
            //    //os::Step::UnmapInitiateShootdown { core }              => admit(),
            //    //os::Step::AckShootdownIPI { core }                     => admit(),
            //    //os::Step::UnmapEnd { core }                            => admit(),
            //    _ => {},
            //}
        }
    };
    lemma_concurrent_trs_induct(pre, post, c, core, pidx, pred);
}


impl Token {
    // User-space thread
    pub uninterp spec fn thread(self) -> nat;
    pub uninterp spec fn consts(self) -> os::Constants;
    pub uninterp spec fn st(self) -> os::State;
    pub uninterp spec fn steps(self) -> Seq<RLbl>;
    pub uninterp spec fn steps_taken(self) -> Seq<RLbl>;
    pub uninterp spec fn progress(self) -> Progress;
    pub uninterp spec fn on_first_step(self) -> bool;

    pub open spec fn core(self) -> Core {
        self.consts().ult2core[self.thread()]
    }

    pub open spec fn withdraw_token(self, new: Token) -> bool {
        &&& new.consts() == self.consts()
        &&& new.thread() == self.thread()
        &&& new.st() == self.st()
        &&& new.steps() == self.steps()
        &&& new.steps_taken() == self.steps_taken()
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
            self.steps_taken() == old(self).steps_taken(),
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
            tok.consts() == old(self).consts().common,
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
            self.steps_taken() == old(self).steps_taken(),
            self.progress() == old(self).progress(),
            old(tok).set_validated(*tok),
    { admit(); } // axiom

    // Not needed.
    //pub proof fn register_external_step_mmu(
    //    tracked &mut self,
    //    tracked tok: &mut mmu::rl3::code::Token,
    //    post: os::State,
    //    lbl: RLbl,
    //)
    //    requires
    //        old(tok).tstate() is ProphecyMade,
    //        lbl.compatible_with(old(self).steps().first()),
    //        os::next(old(self).consts(), old(self).st(), post, lbl),
    //        post.os_ext == old(self).st().os_ext,
    //        post.mmu == old(tok).post(),
    //    ensures
    //        self.on_first_step() == old(self).on_first_step(),
    //        self.consts() == old(self).consts(),
    //        self.thread() == old(self).thread(),
    //        self.st() == post,
    //        self.steps() == old(self).steps().drop_first(),
    //        self.steps_taken() == old(self).steps_taken().push(lbl),
    //        self.progress() == old(self).progress(),
    //        old(tok).set_validated(*tok),
    //{ admit(); } // axiom

    pub proof fn return_mmu_token(tracked &mut self, tracked tok: mmu::rl3::code::Token)
        requires tok.tstate() is Spent,
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.thread() == old(self).thread(),
            self.consts() == old(self).consts(),
            self.st() == old(self).st(),
            self.steps() == old(self).steps(),
            self.steps_taken() == old(self).steps_taken(),
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
            tok.consts() == old(self).consts().common,
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
            self.steps_taken() == old(self).steps_taken(),
            self.progress() == old(self).progress(),
            old(tok).set_valid(*tok),
    { admit(); } // axiom

    pub proof fn register_external_step_osext(
        tracked &mut self,
        tracked tok: &mut os_ext::code::Token,
        post: os::State,
        lbl: RLbl,
    )
        requires
            old(tok).tstate() is ProphecyMade,
            lbl.compatible_with(old(self).steps().first()),
            os::next(old(self).consts(), old(self).st(), post, lbl),
            post.mmu == old(self).st().mmu,
            post.os_ext == old(tok).post(),
        ensures
            self.on_first_step() == old(self).on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.steps_taken() == old(self).steps_taken().push(lbl),
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
            self.steps_taken() == old(self).steps_taken(),
            self.progress() is Unready,
    { admit(); } // axiom


    /// Register a step that corresponds to stutter in both mmu and os_ext.
    pub proof fn register_internal_step(tracked &mut self, post: os::State)
        requires
            old(self).progress() is Ready,
            os::next(old(self).consts(), old(self).st(), post, RLbl::Tau),
            post.os_ext == old(self).st().os_ext,
            post.mmu == old(self).st().mmu,
        ensures
            !self.on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps(),
            self.steps_taken() == old(self).steps_taken(),
            self.progress() == Progress::Unready,
    { admit(); } // axiom

    /// Register a step that corresponds to stutter in both mmu and os_ext.
    pub proof fn register_external_step(tracked &mut self, post: os::State, lbl: RLbl)
        requires
            old(self).progress() is Ready,
            lbl.compatible_with(old(self).steps().first()),
            os::next(old(self).consts(), old(self).st(), post, lbl),
            post.os_ext == old(self).st().os_ext,
            post.mmu == old(self).st().mmu,
        ensures
            !self.on_first_step(),
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.steps_taken() == old(self).steps_taken().push(lbl),
            self.progress() == Progress::Unready,
    { admit(); } // axiom
}

pub trait CodeVC {
    /// We specify the steps to be taken as labels. Outputs (like `result`) in the prescribed
    /// transitions are an arbitrary value, which may not match the actual output. The label of the
    /// step that's actually taken agrees on all non-output fields and is recorded in the token's
    /// `steps_taken`, which we can use to tie it to the return value.
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
    ) -> (res: (Result<(),()>, Tracked<Token>))
        requires
            // State machine VC preconditions
            os::step_Map_enabled(tok.consts(), vaddr as nat, pte@),
            tok.st().inv(tok.consts()),
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is Idle,
            tok.steps() === seq![
                RLbl::MapStart { thread_id: tok.thread(), vaddr: vaddr as nat, pte: pte@ },
                RLbl::MapEnd { thread_id: tok.thread(), vaddr: vaddr as nat, result: arbitrary() }
            ],
            tok.steps_taken() === seq![],
            tok.on_first_step(),
            tok.progress() is Unready,
            // Caller preconditions
            pml4 == tok.st().mmu@.pt_mem.pml4,
        ensures
            res.0 == res.1@.steps_taken().last()->MapEnd_result,
            res.1@.steps() === seq![],
            res.1@.progress() is Unready,
    ;

    /// This function returns the memory region that was unmapped but that value should be
    /// considered a hint as it's not verified.
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
    ) -> (res: (Result<MemRegionExec,()>, Tracked<Token>))
        requires
            os::step_Unmap_enabled(vaddr as nat),
            tok.st().inv(tok.consts()),
            tok.consts().valid_ult(tok.thread()),
            tok.st().core_states[tok.core()] is Idle,
            tok.steps() === seq![
                RLbl::UnmapStart { thread_id: tok.thread(), vaddr: vaddr as nat },
                RLbl::UnmapEnd { thread_id: tok.thread(), vaddr: vaddr as nat, result: arbitrary() }
            ],
            tok.steps_taken() === seq![],
            tok.on_first_step(),
            tok.progress() is Unready,
            // Caller preconditions
            pml4 == tok.st().mmu@.pt_mem.pml4,
        ensures
            res.0 is Ok <==> res.1@.steps_taken().last()->UnmapEnd_result is Ok,
            res.1@.steps() === seq![],
            res.1@.progress() is Unready,
    ;
}

pub open spec fn unchanged_state_during_concurrent_trs(pre: os::State, post: os::State, core: Core) -> bool {
    &&& post.mmu@.happy          == pre.mmu@.happy
    &&& post.mmu@.pt_mem         == pre.mmu@.pt_mem
    &&& post.os_ext.allocated    == pre.os_ext.allocated
    &&& post.mmu@.writes.tso.subset_of(pre.mmu@.writes.tso)
    &&& post.mmu@.writes.nonpos.subset_of(pre.mmu@.writes.nonpos)
    &&& post.mmu@.pending_maps.submap_of(pre.mmu@.pending_maps)
    &&& post.mmu@.pending_unmaps.submap_of(pre.mmu@.pending_unmaps)
    &&& post.os_ext.shootdown_vec.open_requests.subset_of(pre.os_ext.shootdown_vec.open_requests)
    &&& pre.os_ext.shootdown_vec.open_requests.contains(core)
        ==> post.os_ext.shootdown_vec.open_requests.contains(core)
    // &&& forall|core| c.valid_core(core) && !pre.mmu@.writes.nonpos.contains(core)
}

} // verus!
