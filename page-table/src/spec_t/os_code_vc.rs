use vstd::prelude::*;

use crate::spec_t::os;
use crate::spec_t::os_invariant;
use crate::spec_t::mmu;
use crate::spec_t::os_ext;
use crate::spec_t::mmu::defs::{ PageTableEntryExec, Core, aligned };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };
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
            os::Step::MapOpEnd { core, .. } |
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
    let pred =
        |pre: os::State, post: os::State| pre.inv(c) && pre.os_ext.lock == Some(core) ==> {
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

    pub open spec fn core(self) -> Core {
        self.consts().ult2core[self.thread()]
    }

    pub open spec fn withdraw_token(self, new: Token) -> bool {
        &&& new.consts() == self.consts()
        &&& new.thread() == self.thread()
        &&& new.st() == self.st()
        &&& new.steps() == self.steps()
        &&& new.progress() is TokenWithdrawn
    }


    #[verifier(external_body)] // axiom
    pub proof fn do_concurrent_trs(tracked &mut self) -> (pidx: nat)
        requires
            old(self).progress() is Unready,
        ensures
            self.progress() is Ready,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.steps() == old(self).steps(),
            concurrent_trs(old(self).st(), self.st(), old(self).consts(), old(self).core(), pidx),
    { unimplemented!() }



    // Take MMU steps

    #[verifier(external_body)] // axiom
    pub proof fn get_mmu_token(tracked &mut self) -> (tracked tok: mmu::rl3::code::Token)
        requires
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
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.st() == post,
            self.steps() == old(self).steps().drop_first(),
            self.progress() == Progress::Unready,
    { admit(); } // axiom
}

trait CodeVC {
    // We specify the steps to be taken as labels. But the label for `MapEnd` includes the return
    // value, which we want to be equal to the result returned by the function. But we can't
    // specify this in the requires clause because we can't refer to the result there. Instead we
    // use an additional prophetic argument, which carries the return value and to which we can
    // refer in the requires clause.
    exec fn sys_do_map(
        Tracked(tok): Tracked<&mut Token>,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: Result<(),()>)
        requires
            os::step_Map_enabled(vaddr as nat, pte@),
            old(tok).st().inv(old(tok).consts()),
            old(tok).consts().valid_ult(old(tok).thread()),
            old(tok).st().core_states[old(tok).core()] is Idle,
            old(tok).steps() === seq![
                RLbl::MapStart { thread_id: old(tok).thread(), vaddr: vaddr as nat, pte: pte@ },
                RLbl::MapEnd { thread_id: old(tok).thread(), vaddr: vaddr as nat, result: proph_res.value() }
            ],
            old(tok).progress() is Unready,
            proph_res.may_resolve(),
        ensures
            res == proph_res.value(),
            tok.steps() === seq![],
            tok.progress() is Ready,
    ;

    exec fn sys_do_unmap(
        Tracked(tok): Tracked<&mut Token>,
        core: Core,
        vaddr: usize,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: Result<(),()>)
        requires
            old(tok).core() == core,
            old(tok).st().core_states[core] is Idle,
            old(tok).steps() === seq![
                RLbl::UnmapStart { thread_id: old(tok).thread(), vaddr: vaddr as nat },
                RLbl::UnmapEnd { thread_id: old(tok).thread(), vaddr: vaddr as nat, result: proph_res.value() }
            ],
            old(tok).progress() is Unready,
            proph_res.may_resolve(),
        ensures
            res == proph_res.value(),
            tok.steps() === seq![],
            tok.progress() is Ready,
    ;
}

pub open spec fn unchanged_state_during_concurrent_trs(pre: os::State, post: os::State) -> bool {
    &&& post.mmu@.happy        == pre.mmu@.happy
    &&& post.mmu@.pt_mem       == pre.mmu@.pt_mem
    &&& post.mmu@.writes       == pre.mmu@.writes
    &&& post.mmu@.pending_maps == pre.mmu@.pending_maps
}

pub exec fn do_step_mapstart(Tracked(tok): Tracked<&mut Token>, vaddr: usize, pte: PageTableEntryExec)
    requires
        os::step_Map_enabled(vaddr as nat, pte@),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).consts().valid_core(old(tok).core()), // TODO: ??
        old(tok).st().core_states[old(tok).core()] is Idle,
        old(tok).steps().len() > 0,
        old(tok).steps().first() == (RLbl::MapStart { thread_id: old(tok).thread(), vaddr: vaddr as nat, pte: pte@ }),
        old(tok).progress() is Unready,
        old(tok).st().inv(old(tok).consts()),
    ensures
        tok.core() == old(tok).core(),
        tok.st().core_states[tok.core()] is MapWaiting,
        tok.st().core_states[tok.core()]->MapWaiting_ult_id == tok.thread(),
        tok.st().core_states[tok.core()]->MapWaiting_vaddr == vaddr as nat,
        tok.st().core_states[tok.core()]->MapWaiting_pte == pte@,
        unchanged_state_during_concurrent_trs(old(tok).st(), tok.st()),
        //tok.st().os_ext.lock == old(tok).st().os_ext.lock,
        tok.thread() == old(tok).thread(),
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps().drop_first(),
        tok.progress() is Ready,
        tok.st().inv(tok.consts()),
{
    let state1 = Ghost(tok.st());
    let core = Ghost(tok.core());
    assert(core@ == tok.consts().ult2core[tok.thread()]);
    proof {
        let pidx = tok.do_concurrent_trs();
        // TODO: This part is weird because according to the state machine this step we're taking
        // is unstable. But in practice it is stable (actually, no it's not really), it's just that
        // we use the core state to express that fact.. We probably just need to assume that the
        // first step is stable, which we can do by starting with progress as Ready
        //
        // Maybe we don't do mapstart in the implementation.. which would be a bit strange but
        // probably fine. then the first step (acquiring the lock) is actually stable. But then
        // we're not enforcing that the first step actually is that of acuiring the lock. Is that a
        // problem?
        assume(tok.st().core_states[core@] == state1@.core_states[core@]);
        assume(tok.st().inv(tok.consts()));
        //lemma_concurrent_trs(state1@, tok.st(), tok.consts(), tok.core(), pidx);
    }
    let state2 = Ghost(tok.st());
    proof {
        let new_cs = os::CoreState::MapWaiting { ult_id: tok.thread(), vaddr: vaddr as nat, pte: pte@ };
        let new_sound = tok.st().sound && os::step_Map_sound(tok.st().interp_pt_mem(), tok.st().core_states.values(), vaddr as nat, pte@);
        let post = os::State {
            core_states: tok.st().core_states.insert(core@, new_cs),
            sound: new_sound,
            ..tok.st()
        };
        let lbl = RLbl::MapStart { thread_id: tok.thread(), vaddr: vaddr as nat, pte: pte@ };
        assert(os::step_MapStart(tok.consts(), tok.st(), post, core@, lbl));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapStart { core: core@ }, lbl));
        tok.register_external_step(post);
        let state3 = Ghost(tok.st());
        os_invariant::next_preserves_inv(tok.consts(), state2@, state3@, lbl);
        tok.do_concurrent_trs();
        let state4 = Ghost(tok.st());
        //lemma_concurrent_trs(state3@, state4@, tok.consts(), tok.core(), pidx);
        assume(state4@.core_states[core@] == state3@.core_states[core@]);
        assume(state4@.inv(tok.consts()));
        assume(unchanged_state_during_concurrent_trs(old(tok).st(), tok.st()));
    }
}

pub exec fn do_step_mapopstart(Tracked(tok): Tracked<&mut Token>)
    requires
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).thread() == old(tok).st().core_states[old(tok).core()]->MapWaiting_ult_id,
        old(tok).st().core_states[old(tok).core()] is MapWaiting,
        old(tok).steps().len() > 0,
        old(tok).progress() is Ready,
        old(tok).st().inv(old(tok).consts()),
    ensures
        tok.core() == old(tok).core(),
        tok.thread() == old(tok).thread(),
        old(tok).st().core_states[tok.core()] matches os::CoreState::MapWaiting { ult_id, vaddr, pte }
            && tok.st().core_states[tok.core()] == (os::CoreState::MapExecuting { ult_id, vaddr, pte }),
        tok.progress() is Ready,
        unchanged_state_during_concurrent_trs(old(tok).st(), tok.st()),
        tok.st().os_ext.lock == Some(tok.core()),
        tok.st().inv(tok.consts()),
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps(),
{
    let state1 = Ghost(tok.st());
    let core = Ghost(tok.core());
    assert(core@ == tok.consts().ult2core[tok.thread()]);
    let tracked mut osext_tok = tok.get_osext_token();
    proof {
        osext_tok.prophesy_acquire_lock();
        let vaddr = tok.st().core_states[core@]->MapWaiting_vaddr;
        let pte = tok.st().core_states[core@]->MapWaiting_pte;
        let new_cs = os::CoreState::MapExecuting { ult_id: tok.thread(), vaddr, pte };
        let post = os::State {
            core_states: tok.st().core_states.insert(core@, new_cs),
            os_ext: osext_tok.post(),
            ..tok.st()
        };
        //assert(os_ext::step_AcquireLock(tok.st().os_ext, post.os_ext, tok.consts().os_ext(), osext_tok.lbl()));
        assert(os::step_MapOpStart(tok.consts(), tok.st(), post, core@, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapOpStart { core: core@ }, RLbl::Tau));
        tok.register_internal_step_osext(&mut osext_tok, post);
        os_invariant::next_preserves_inv(tok.consts(), state1@, tok.st(), RLbl::Tau);
    }

    os_ext::code::acquire_lock(Tracked(&mut osext_tok));
    let state2 = Ghost(tok.st());

    proof {
        tok.return_osext_token(osext_tok);
        let pidx = tok.do_concurrent_trs();
        let state3 = Ghost(tok.st());
        lemma_concurrent_trs(state2@, state3@, tok.consts(), tok.core(), pidx);
    }
}

pub exec fn do_step_read(Tracked(tok): Tracked<&mut Token>, addr: usize) -> (res: usize)
    requires
        aligned(addr as nat, 8),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).thread() == old(tok).st().core_states[old(tok).core()]->MapExecuting_ult_id,
        old(tok).st().core_states[old(tok).core()] is MapExecuting,
        old(tok).steps().len() > 0,
        old(tok).progress() is Ready,
        old(tok).st().inv(old(tok).consts()),
    ensures
        tok.thread() == old(tok).thread(),
        tok.core() == old(tok).core(),
        tok.st().core_states[tok.core()] == old(tok).st().core_states[tok.core()],
        tok.progress() is Ready,
        unchanged_state_during_concurrent_trs(old(tok).st(), tok.st()),
        tok.st().inv(tok.consts()),
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps(),
        res & MASK_NEG_DIRTY_ACCESS == tok.st().mmu@.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS,
{
    let state1 = Ghost(tok.st());
    let core = Ghost(tok.core());
    assert(core@ == tok.consts().ult2core[tok.thread()]);
    assert(tok.consts().valid_core(core@));
    let tracked mut mmu_tok = tok.get_mmu_token();
    proof {
        mmu_tok.prophesy_read(addr);
        let vaddr = tok.st().core_states[core@]->MapExecuting_vaddr;
        let pte = tok.st().core_states[core@]->MapExecuting_pte;
        let post = os::State {
            mmu: mmu_tok.post(),
            ..tok.st()
        };
        let read_result = mmu_tok.lbl()->Read_2;
        assert(mmu::rl3::next(tok.st().mmu, post.mmu, tok.consts().mmu, mmu_tok.lbl()));
        assert(os::step_ReadPTMem(tok.consts(), tok.st(), post, core@, addr, read_result, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::ReadPTMem { core: core@, paddr: addr, value: read_result }, RLbl::Tau));
        tok.register_internal_step_mmu(&mut mmu_tok, post);
        os_invariant::next_preserves_inv(tok.consts(), state1@, tok.st(), RLbl::Tau);
    }

    let res = mmu::rl3::code::read(Tracked(&mut mmu_tok), addr);
    let state2 = Ghost(tok.st());

    proof {
        broadcast use to_rl1::next_refines;
        // TODO: This probably needs an additional invariant on the os state machine
        // Something like this: is_in_crit_sect(core) && writes nonempty ==> writes.core == core
        assume(state1@.mmu@.is_tso_read_deterministic(core@, addr));
        assert(state1@.os_ext.lock == Some(core@));
        tok.return_mmu_token(mmu_tok);
        let pidx = tok.do_concurrent_trs();
        let state3 = Ghost(tok.st());
        lemma_concurrent_trs(state2@, state3@, tok.consts(), tok.core(), pidx);
    }
    res
}

pub exec fn do_step_write_stutter(Tracked(tok): Tracked<&mut Token>, addr: usize, value: usize)
    requires
        aligned(addr as nat, 8),
        old(tok).consts().valid_ult(old(tok).thread()),
        old(tok).thread() == old(tok).st().core_states[old(tok).core()]->MapExecuting_ult_id,
        old(tok).st().core_states[old(tok).core()] is MapExecuting,
        old(tok).steps().len() > 0,
        old(tok).progress() is Ready,
        old(tok).st().inv(old(tok).consts()),
        old(tok).st().mmu@.pt_mem.is_nonneg_write(addr, value),
        old(tok).st().mmu@.pt_mem.write(addr, value)@ == old(tok).st().mmu@.pt_mem@,
    ensures
        tok.thread() == old(tok).thread(),
        tok.core() == old(tok).core(),
        tok.st().core_states[tok.core()] == old(tok).st().core_states[tok.core()],
        tok.st().mmu@.happy == old(tok).st().mmu@.happy,
        tok.st().mmu@.writes ==
            (mmu::rl3::Writes {
                all: old(tok).st().mmu@.writes.all.insert(addr),
                core: tok.core(),
            }),
        tok.st().mmu@.pending_maps == old(tok).st().mmu@.pending_maps,
        tok.st().inv(tok.consts()),
        tok.progress() is Ready,
        tok.consts() == old(tok).consts(),
        tok.steps() == old(tok).steps(),
{

    let state1 = Ghost(tok.st());
    let core = Ghost(tok.core());
    let tracked mut mmu_tok = tok.get_mmu_token();
    proof {
        broadcast use to_rl1::next_refines;

        // TODO: This should follow from the same invariant we need in do_step_read
        assume(!state1@.mmu@.writes.all.is_empty() ==> core == state1@.mmu@.writes.core);

        mmu_tok.prophesy_write(addr, value);
        let vaddr = tok.st().core_states[core@]->MapExecuting_vaddr;
        let pte = tok.st().core_states[core@]->MapExecuting_pte;
        let post = os::State { mmu: mmu_tok.post(), ..tok.st() };
        // TODO: Need to think about how to resolve this. Hopefully can use the pt_mem view everywhere.
        assume(state1@.interp_pt_mem() == nat_keys(old(tok).st().mmu@.pt_mem@));
        assume(post.interp_pt_mem() == nat_keys(old(tok).st().mmu@.pt_mem.write(addr, value)@));
        //assert(post.interp_pt_mem() == state1@.interp_pt_mem());
        //assert(post.mmu@.pt_mem@ == state1@.mmu@.pt_mem@);

        //assert(Map::new(
        //    |vbase| post.mmu@.pt_mem@.contains_key(vbase) && !state1@.mmu@.pt_mem@.contains_key(vbase),
        //    |vbase| post.mmu@.pt_mem@[vbase]
        //) === map![]);
        //assert(tok.st().mmu@.pending_maps == old(tok).st().mmu@.pending_maps);
        assert(mmu::rl3::next(tok.st().mmu, post.mmu, tok.consts().mmu, mmu_tok.lbl()));
        assert(os::step_MapOpStutter(tok.consts(), tok.st(), post, core@, addr, value, RLbl::Tau));
        assert(os::next_step(tok.consts(), tok.st(), post, os::Step::MapOpStutter { core: core@, paddr: addr, value }, RLbl::Tau));
        tok.register_internal_step_mmu(&mut mmu_tok, post);
        os_invariant::next_preserves_inv(tok.consts(), state1@, tok.st(), RLbl::Tau);
    }

    let res = mmu::rl3::code::write(Tracked(&mut mmu_tok), addr, value);
    let state2 = Ghost(tok.st());

    proof {
        // TODO: This probably needs an additional invariant on the os state machine
        // Something like this: is_in_crit_sect(core) && writes nonempty ==> writes.core == core
        //assume(state1@.mmu@.is_tso_read_deterministic(core@, addr));
        assert(state1@.os_ext.lock == Some(core@));
        tok.return_mmu_token(mmu_tok);
        let pidx = tok.do_concurrent_trs();
        let state3 = Ghost(tok.st());
        lemma_concurrent_trs(state2@, state3@, tok.consts(), tok.core(), pidx);
        assert(state3@.mmu@.pending_maps === state1@.mmu@.pending_maps);
    }
}

// TODO: delete eventually. Dummy implementation to make sure we prove the right stuff for the
// wrappers above.
impl CodeVC for () {
    exec fn sys_do_map(
        Tracked(tok): Tracked<&mut Token>,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: Result<(),()>)
    {
        assume(tok.consts().valid_core(tok.core())); // TODO: Should be provable somehow
        do_step_mapstart(Tracked(tok), vaddr, pte);
        do_step_mapopstart(Tracked(tok));
        let dummy_addr: usize = 48;
        do_step_read(Tracked(tok), dummy_addr);
        assume(tok.st().mmu@.is_this_write_happy(tok.core(), dummy_addr, 42));
        assume(tok.st().mmu@.pt_mem.write(dummy_addr, 42)@ == tok.st().mmu@.pt_mem@);
        do_step_write_stutter(Tracked(tok), dummy_addr, 42);

        // read, allocate, mapopstutter, mapopend, mapend, barrier

        proof { admit(); }
        unreached()
    }

    #[verifier(external_body)]
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<&mut Token>,
        core: Core,
        vaddr: usize,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: Result<(),()>)
    { unimplemented!() }
}

pub open spec fn nat_keys<V>(m: Map<usize, V>) -> Map<nat, V> {
    Map::new(|k: nat| k <= usize::MAX && m.contains_key(k as usize), |k: nat| m[k as usize])
}

} // verus!
