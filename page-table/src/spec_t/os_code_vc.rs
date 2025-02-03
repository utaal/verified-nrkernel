use vstd::prelude::*;

//use crate::spec_t::mmu::{rl3_code};
use crate::spec_t::os;
use crate::spec_t::mmu;
use crate::spec_t::mmu::defs::{
    PageTableEntryExec,
    //PTE,
    //aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    //candidate_mapping_overlaps_existing_vmem, overlap, x86_arch_spec, MemRegion, PTE,
    Core,
};
use crate::theorem::RLbl;

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

/*

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
            os::Step::MMU => true,
            os::Step::MemOp { core, .. } |
            os::Step::ReadPTMem { core, .. } |
            os::Step::Barrier { core, .. } |
            os::Step::Invlpg { core, .. } |
            os::Step::MapStart { core, .. } |
            os::Step::MapOpStart { core, .. } |
            os::Step::MapOpStutter { core, .. } |
            os::Step::MapOpEnd { core, .. } |
            os::Step::MapEnd { core, .. } |
            os::Step::UnmapStart { core, .. } |
            os::Step::UnmapOpStart { core, .. } |
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

//pub proof fn lemma_concurrent_trs(pre: os::State, post: os::State, pidx: nat)
//    requires concurrent_trs(pre, post, pidx)
//    ensures
//        post.sys == pre.sys,
//        post.env.ptmem == pre.env.ptmem,
//{
//    // We'll have to prove this but it should be fairly easy
//    admit();
//}


//proof fn env_tr_eqI(pre: mmu::rl3::State)
//    ensures concurrent_trs(pre, pre, 0)
//{}
//
//proof fn env_tr_flipI(pre: mmu::rl3::State, post: mmu::rl3::State, pidx: nat, ppost:
//mmu::rl3::State)
//    requires
//        concurrent_trs(pre, post, pidx),
//        EnvLowM::step_Flip(post, ppost, RLbl::Flip),
//    ensures
//        concurrent_trs(post, ppost, pidx + 1)
//{
//    if pidx == 0 {
//    } else {
//        assert(sub(pidx + 1, 1) == pidx);
//        assert(concurrent_trs(pre, post, sub(pidx + 1, 1)) && EnvLowM::step_Flip(post, ppost, RLbl::Flip));
//    }
//}

/// The OS part of the OS state machine's state. I.e. everything except for `mmu`.
pub struct OSState {
    pub core_states: Map<Core, os::CoreState>,
    pub shootdown_vec: os::ShootdownVector,
    pub sound: bool,
}

impl OSState {
    pub open spec fn combine(self, mmu: mmu::rl3::State) -> os::State {
        os::State {
            core_states: self.core_states,
            shootdown_vec: self.shootdown_vec,
            sound: self.sound,
            mmu: mmu,
        }
    }
}

impl Token {
    // User-space thread
    pub spec fn thread(self) -> nat;
    pub spec fn consts(self) -> os::Constants;
    pub spec fn os_st(self) -> OSState;
    pub spec fn mmu_st(self) -> mmu::rl3::State;
    pub spec fn remaining_steps(self) -> Seq<RLbl>;
    pub spec fn progress(self) -> Progress;

    pub open spec fn core(self) -> Core {
        self.consts().ult2core[self.thread()]
    }

    pub open spec fn st(self) -> os::State {
        self.os_st().combine(self.mmu_st())
    }

    #[verifier(external_body)]
    pub proof fn do_concurrent_trs(tracked &mut self) -> (pidx: nat)
        requires
            old(self).progress() is Unready,
        ensures
            self.progress() is Ready,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.remaining_steps() == old(self).remaining_steps(),
            concurrent_trs(old(self).st(), self.st(), old(self).consts(), old(self).core(), pidx),
    { unimplemented!() }

    #[verifier(external_body)]
    pub proof fn get_env_token(tracked &mut self) -> (tracked tok: mmu::rl3_code::Token)
        requires
            old(self).progress() is Ready,
        ensures
            self.progress() is TokenWithdrawn,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.os_st() == old(self).os_st(),
            self.mmu_st() == old(self).mmu_st(),
            self.remaining_steps() == old(self).remaining_steps(),
            tok.pre() == self.mmu_st(),
    { unimplemented!() }

    #[verifier(external_body)]
    pub proof fn register_internal_step(tracked &mut self, tracked stub: Tracked<mmu::rl3_code::Stub>, os_post: OSState)
        requires
            old(self).remaining_steps().len() > 0, // No more steps allowed if we're already finished
            old(self).progress() is TokenWithdrawn,
            os::next(
                old(self).consts(),
                old(self).st(),
                os_post.combine(stub@.post()),
                RLbl::Tau),
        ensures
            self.progress() is Unready,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.remaining_steps() == old(self).remaining_steps(),
            self.os_st() == os_post,
            self.mmu_st() == stub@.post(),
    {}

    // XXX: Problem with this approach: A non-terminating program could take one invalid
    // step and just not register it. Do we have termination checking for exec now?
    // Otherwise we'll have to change this to "pre-register" transitions before taking
    // them.
    #[verifier(external_body)]
    pub proof fn register_external_step(tracked &mut self, tracked stub: Tracked<mmu::rl3_code::Stub>, os_post: OSState, lbl: RLbl)
        requires
            old(self).remaining_steps().len() > 0,
            old(self).progress() is TokenWithdrawn,
            os::next(
                old(self).consts(),
                old(self).st(),
                os_post.combine(stub@.post()),
                lbl),
        ensures
            self.progress() is Unready,
            self.consts() == old(self).consts(),
            self.thread() == old(self).thread(),
            self.remaining_steps() == old(self).remaining_steps().drop_first(),
            self.os_st() == os_post,
            self.mmu_st() == stub@.post(),
    {}
}

trait CodeVC {
    // XXX: One problem here:
    // * `progress()` is `Unready` so we're forced to prove that we're not relying on
    //   "unstable" preconditions.
    // * But the step of acquiring the lock on this thread is in fact unstable, since
    //   another core might acquire it first.
    // * .. what to do?
    //
    // We specify the steps to be taken as labels. But the label for `MapEnd` includes the return
    // value, which we want to be equal to the result returned by the function. But we can't
    // specify this in the requires clause because we can't refer to the result there. Instead we
    // use an additional prophetic argument, which carries the return value and to which we can
    // refer in the requires clause.
    exec fn sys_do_map(
        tracked tok: &mut Token,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
        )
        -> (res: Result<(),()>)
        requires
            old(tok).os_st().core_states[old(tok).core()] is Idle,
            old(tok).remaining_steps() === seq![
                RLbl::MapStart { thread_id: old(tok).thread(), vaddr: vaddr as nat, pte: pte@ },
                RLbl::MapEnd { thread_id: old(tok).thread(), vaddr: vaddr as nat, result: proph_res.value() }
            ],
            old(tok).progress() is Unready,
            proph_res.may_resolve(),
        ensures
            res == proph_res.value(),
            tok.remaining_steps() === seq![],
            tok.progress() is Ready,
    ;
}

//pub exec fn do_mapstart(state: &mut Tracked<SysM::Interface::Token>, va: usize, pa: usize)
//    requires
//        old(state)@.os_st().thread_state is Idle,
//        old(state)@.remaining_steps().len() > 0,
//        old(state)@.remaining_steps().first() == SysM::RLbl::MapStart(va as nat, pa as nat),
//        old(state)@.progress() is Unready,
//    ensures
//        // XXX: can't directly use the transition definition because of the additional
//        // environment transitions :(
//        // This may get a bit unwieldy with larger state machines like we have with the
//        // page table.
//        //SysM::step_MapStart(old(state)@.st(), state@.st(), SysM::RLbl::MapStart(va as nat, pa as nat)),
//        state@.mmu_st().interp().ptmem == old(state)@.mmu_st().interp().ptmem,
//        state@.os_st().thread_state == SysM::TState::Mapping(va as nat, pa as nat),
//        state@.remaining_steps() == old(state)@.remaining_steps().drop_first(),
//        state@.progress() is Ready,
//{
//    // Allow concurrent transitions to get `progress()` to `Ready`
//    proof {
//        let pre_concurrent_state = state@;
//        let pidx = state.borrow_mut().do_concurrent_trs();
//        SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
//    }
//
//    let tracked env_token = state.borrow_mut().get_env_token();
//    // MapStart is a stutter step in the environment state machine
//    let stub = mmu::rl3_code::stutter(Tracked(env_token));
//
//    // We change the thread_state with a MapStart transition
//    let ghost os_post = OSState {
//        thread_state: SysM::TState::Mapping(va as nat, pa as nat),
//    };
//    proof {
//        EnvLowM::refinement::next_step_refines(state@.mmu_st(), stub@.post(), EnvLowM::Step::Stutter, stub@.lbl());
//        assert(SysM::next_step(
//                state@.st(),
//                os::State { sys: os_post, env: stub@.post() },
//                SysM::Step::MapStart,
//                SysM::RLbl::MapStart(va as nat, pa as nat))
//        );
//        state.borrow_mut().register_external_step(stub, os_post);
//    }
//
//    // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
//    proof {
//        let pre_concurrent_state = state@;
//        let pidx = state.borrow_mut().do_concurrent_trs();
//        SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
//    }
//}
//
//pub exec fn do_mapstutter(state: &mut Tracked<SysM::Interface::Token>, i: usize, v: usize)
//    requires
//        old(state)@.os_st().thread_state is Mapping,
//        old(state)@.remaining_steps().len() > 0,
//        old(state)@.progress() is Ready,
//        old(state)@.mmu_st().interp().ptmem.write(i as nat, v as nat)@ == old(state)@.mmu_st().interp().ptmem@,
//    ensures
//        state@.mmu_st().interp().ptmem@ == old(state)@.mmu_st().interp().ptmem@,
//        state@.os_st().thread_state    == old(state)@.os_st().thread_state,
//        state@.remaining_steps()        == old(state)@.remaining_steps(),
//        state@.progress() is Ready,
//{
//    let tracked env_token = state.borrow_mut().get_env_token();
//    // Do the write
//    let stub = mmu::rl3_code::remap(Tracked(env_token), i, v);
//
//    proof {
//        assert(stub@.lbl() == Lbl::Remap(i as nat, v as nat));
//        assert(EnvLowM::next_step(state@.mmu_st(), stub@.post(), EnvLowM::Step::Remap, stub@.lbl()));
//        EnvLowM::refinement::next_step_refines(state@.mmu_st(), stub@.post(), EnvLowM::Step::Remap, stub@.lbl());
//        assert(SysM::next_step(
//                state@.st(),
//                os::State { sys: state@.os_st(), env: stub@.post() },
//                SysM::Step::MapStutter(i as nat, v as nat),
//                SysM::RLbl::Tau)
//        );
//        state.borrow_mut().register_internal_step(stub, state@.os_st());
//    }
//
//    // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
//    proof {
//        let pre_concurrent_state = state@;
//        let pidx = state.borrow_mut().do_concurrent_trs();
//        SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
//    }
//}
//
//pub exec fn do_mapend(state: &mut Tracked<SysM::Interface::Token>, i: usize, v: usize)
//    requires
//        old(state)@.os_st().thread_state is Mapping,
//        old(state)@.remaining_steps() =~= seq![SysM::RLbl::MapEnd],
//        old(state)@.progress() is Ready,
//        ({
//            // https://github.com/verus-lang/verus/issues/1393
//            let va = old(state)@.os_st().thread_state->Mapping_0;
//            let pa = old(state)@.os_st().thread_state->Mapping_1;
//            old(state)@.mmu_st().ptmem.write(i as nat, v as nat)@ == old(state)@.mmu_st().ptmem@.insert(va, pa)
//        }),
//    ensures
//        ({
//            let va = old(state)@.os_st().thread_state->Mapping_0;
//            let pa = old(state)@.os_st().thread_state->Mapping_1;
//            state@.mmu_st().ptmem@ == old(state)@.mmu_st().ptmem@.insert(va, pa)
//        }),
//        state@.os_st().thread_state == SysM::TState::Idle,
//        state@.remaining_steps()     =~= seq![],
//        state@.progress() is Ready,
//{
//    let tracked env_token = state.borrow_mut().get_env_token();
//    // Do the write
//    let stub = mmu::rl3_code::remap(Tracked(env_token), i, v);
//
//    proof {
//        assert(stub@.lbl() == Lbl::Remap(i as nat, v as nat));
//        assert(EnvLowM::next_step(state@.mmu_st(), stub@.post(), EnvLowM::Step::Remap, stub@.lbl()));
//        EnvLowM::refinement::next_step_refines(state@.mmu_st(), stub@.post(), EnvLowM::Step::Remap, stub@.lbl());
//
//        // We change the thread_state back to Idle
//        let os_post = OSState {
//            thread_state: SysM::TState::Idle,
//        };
//        assert(SysM::next_step(
//                state@.st(),
//                os::State { sys: os_post, env: stub@.post() },
//                SysM::Step::MapEnd(i as nat, v as nat),
//                SysM::RLbl::MapEnd)
//        );
//        state.borrow_mut().register_external_step(stub, os_post);
//    }
//
//    // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
//    proof {
//        let pre_concurrent_state = state@;
//        let pidx = state.borrow_mut().do_concurrent_trs();
//        SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
//    }
//}

*/

} // verus!
