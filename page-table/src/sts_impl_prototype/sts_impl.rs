use vstd::prelude::*;

verus! {

mod EnvM {
    use super::*;

    pub enum Lbl {
        Remap(nat, nat),
        ProcessWrite(nat, nat),
        Tau,
    }

    pub struct PTMem {
        pub mem: Map<nat, nat>,
    }

    impl PTMem {
        pub spec fn view(self) -> Map<nat, nat>;
        pub open spec fn write(self, i: nat, v: nat) -> PTMem {
            PTMem {
                mem: self.mem.insert(i, v),
            }
        }
        pub open spec fn read(self, i: nat) -> nat {
            self.mem[i]
        }
    }

    pub struct State {
        pub ptmem: PTMem,
        pub pmem: Map<nat, nat>,
    }

    pub open spec fn step_Remap(pre: State, post: State, lbl: Lbl) -> bool {
        &&& lbl matches Lbl::Remap(i, v)

        &&& post.ptmem == pre.ptmem.write(i, v)
        &&& post.pmem == pre.pmem
    }

    pub open spec fn step_ProcessWrite(pre: State, post: State, lbl: Lbl) -> bool {
        &&& lbl matches Lbl::ProcessWrite(i, v)

        &&& post.ptmem == pre.ptmem
        &&& post.pmem == pre.pmem.insert(pre.ptmem@[i], v)
    }

    /// TODO: I think "stutter" here also covers other internal behaviors that don't cause any
    /// state changes in the abstracted environment model.
    pub open spec fn step_Stutter(pre: State, post: State, lbl: Lbl) -> bool {
        &&& lbl is Tau
        &&& post == pre
    }

    pub enum Step {
        Remap,
        ProcessWrite,
        Stutter,
    }

    pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
        match step {
            Step::Remap        => step_Remap(pre, post, lbl),
            Step::ProcessWrite => step_ProcessWrite(pre, post, lbl),
            Step::Stutter      => step_Stutter(pre, post, lbl),
        }
    }

    pub open spec fn next(pre: State, post: State, lbl: Lbl) -> bool {
        exists|step| next_step(pre, post, step, lbl)
    }

    pub open spec fn init(pre: State) -> bool {
        &&& pre.ptmem === PTMem { mem: Map::total(|i| 0) }
        &&& pre.pmem === Map::total(|i| 0)
    }

    pub mod Interface {
        use vstd::prelude::*;
        use super::{EnvM, Lbl};

        #[verifier(external_body)]
        pub tracked struct Token {}

        #[verifier(external_body)]
        pub tracked struct Stub {}

        impl Token {
            pub spec fn st(self) -> EnvM::State;
        }

        impl Stub {
            pub spec fn st(self) -> EnvM::State;
            pub spec fn lbl(self) -> EnvM::Lbl;
        }

        #[verifier(external_body)]
        pub exec fn remap(Tracked(tok): Tracked<Token>, i: usize, v: usize) -> (stub: Tracked<Stub>)
            ensures
                EnvM::step_Remap(tok.st(), stub@.st(), stub@.lbl()),
                stub@.lbl() == Lbl::Remap(i as nat, v as nat),
        {
            unimplemented!()
        }

        #[verifier(external_body)]
        pub exec fn stutter(Tracked(tok): Tracked<Token>) -> (stub: Tracked<Stub>)
            ensures
                EnvM::step_Stutter(tok.st(), stub@.st(), stub@.lbl()),
                stub@.lbl() == Lbl::Tau,
        {
            unimplemented!()
        }

    }
}



mod SysM {
    use super::*;
    use super::EnvM;

    /// Thread state
    pub enum TState {
        Idle,
        Mapping(nat, nat),
    }

    /// Refinement labels
    /// TODO: where do the arguments go? Start? End? Both?
    pub enum Lbl {
        MapStart(nat, nat),
        MapEnd,
        ProcessWrite(nat, nat),
        Tau,
    }

    pub struct SysState {
        pub thread_state: TState,
    }

    pub struct State {
        pub env: EnvM::State,
        pub sys: SysState,
    }

    pub open spec fn step_MapStart(pre: State, post: State, lbl: Lbl) -> bool {
        &&& lbl matches Lbl::MapStart(va, pa)

        &&& pre.sys.thread_state is Idle

        &&& post.sys.thread_state == TState::Mapping(va, pa)
        &&& EnvM::step_Stutter(pre.env, post.env, EnvM::Lbl::Tau)
    }

    pub open spec fn step_MapStutter(pre: State, post: State, i: nat, v: nat, lbl: Lbl) -> bool {
        &&& lbl is Tau

        &&& pre.sys.thread_state matches TState::Mapping(va, pa)
        // Can do writes that don't change the view
        &&& post.env.ptmem@ == pre.env.ptmem@

        &&& post.sys.thread_state == pre.sys.thread_state
        &&& EnvM::next(pre.env, post.env, EnvM::Lbl::Remap(i, v))
    }

    pub open spec fn step_MapEnd(pre: State, post: State, i: nat, v: nat, lbl: Lbl) -> bool {
        &&& lbl is MapEnd

        &&& pre.sys.thread_state matches TState::Mapping(va, pa)
        // Final write changes the view
        &&& post.env.ptmem@ == pre.env.ptmem@.insert(va, pa)

        &&& post.sys.thread_state == TState::Idle
        &&& EnvM::next(pre.env, post.env, EnvM::Lbl::Remap(i, v))
    }

    pub open spec fn step_ProcessWrite(pre: State, post: State, lbl: Lbl) -> bool {
        &&& lbl matches Lbl::ProcessWrite(va, val)

        &&& post.sys.thread_state == pre.sys.thread_state
        &&& EnvM::next(pre.env, post.env, EnvM::Lbl::ProcessWrite(va, val))
    }

    pub enum Step {
        MapStart,
        MapStutter(nat, nat),
        MapEnd(nat, nat),
        ProcessWrite,
        //Stutter,
    }

    pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
        match step {
            Step::MapStart         => step_MapStart(pre, post, lbl),
            Step::MapStutter(i, v) => step_MapStutter(pre, post, i, v, lbl),
            Step::MapEnd(i, v)     => step_MapEnd(pre, post, i, v, lbl),
            Step::ProcessWrite     => step_ProcessWrite(pre, post, lbl),
        }
    }

    pub open spec fn next(pre: State, post: State, lbl: Lbl) -> bool {
        exists|step| next_step(pre, post, step, lbl)
    }

    pub open spec fn init(pre: State) -> bool {
        &&& EnvM::init(pre.env)
    }

    mod Interface {
        use vstd::prelude::*;
        use super::{SysM, EnvM, Lbl};

        pub enum Progress {
            Unready,
            Ready,
            TokenWithdrawn
        }

        #[verifier(external_body)]
        pub tracked struct Token {
            //pub env_token: EnvM::Interface::Token,
        }

        impl SysM::Step {
            pub open spec fn is_actor_step(self) -> bool {
                // XXX: Whether or not transitions are actor steps depends on the core. E.g.
                // MapStart on different core is non-actor step but we can easily prove that its
                // enabling conditions aren't satisfied.
                arbitrary()
            }
        }

        pub open spec fn concurrent_trs(pre: SysM::State, post: SysM::State, pidx: nat) -> bool
            decreases pidx
        {
            if pidx == 0 {
                post == pre
            } else {
                exists|state: SysM::State, step, lbl| {
                    &&& concurrent_trs(pre, state, sub(pidx, 1)) 
                    &&& SysM::next_step(state, post, step, lbl)
                    &&& !step.is_actor_step()
                }
            }
        }

        pub proof fn lemma_concurrent_trs(pre: SysM::State, post: SysM::State, pidx: nat)
            requires concurrent_trs(pre, post, pidx)
            ensures
                post.sys == pre.sys,
                post.env.ptmem == pre.env.ptmem,
        {
            // We'll have to prove this but it should be fairly easy
            admit();
        }


        //proof fn env_tr_eqI(pre: EnvM::State)
        //    ensures concurrent_trs(pre, pre, 0)
        //{}
        //
        //proof fn env_tr_flipI(pre: EnvM::State, post: EnvM::State, pidx: nat, ppost: EnvM::State)
        //    requires
        //        concurrent_trs(pre, post, pidx),
        //        EnvM::step_Flip(post, ppost, Lbl::Flip),
        //    ensures
        //        concurrent_trs(post, ppost, pidx + 1)
        //{
        //    if pidx == 0 {
        //    } else {
        //        assert(sub(pidx + 1, 1) == pidx);
        //        assert(concurrent_trs(pre, post, sub(pidx + 1, 1)) && EnvM::step_Flip(post, ppost, Lbl::Flip));
        //    }
        //}

        impl Token {
            pub spec fn sys_st(self) -> SysM::SysState;
            pub spec fn env_st(self) -> EnvM::State;
            pub spec fn remaining_steps(self) -> Seq<Lbl>;
            pub spec fn progress(self) -> Progress;

            pub open spec fn st(self) -> SysM::State {
                SysM::State {
                    sys: self.sys_st(),
                    env: self.env_st(),
                }
            }

            #[verifier(external_body)]
            pub proof fn do_concurrent_trs(tracked &mut self) -> (pidx: nat)
                requires
                    old(self).progress() is Unready,
                ensures
                    self.progress() is Ready,
                    self.remaining_steps() == old(self).remaining_steps(),
                    concurrent_trs(old(self).st(), self.st(), pidx),
            { unimplemented!() }

            #[verifier(external_body)]
            pub proof fn get_env_token(tracked &mut self) -> (tracked tok: EnvM::Interface::Token)
                requires
                    old(self).progress() is Ready,
                ensures
                    self.progress() is TokenWithdrawn,
                    self.sys_st() == old(self).sys_st(),
                    self.env_st() == old(self).env_st(),
                    self.remaining_steps() == old(self).remaining_steps(),
                    tok.st() == self.env_st(),
            { unimplemented!() }

            #[verifier(external_body)]
            pub proof fn register_internal_step(tracked &mut self, tracked stub: Tracked<EnvM::Interface::Stub>, sys_post: SysM::SysState)
                requires
                    old(self).remaining_steps().len() > 0, // No more steps allowed if we're already finished
                    old(self).progress() is TokenWithdrawn,
                    SysM::next(old(self).st(), SysM::State { sys: sys_post, env: stub@.st() }, SysM::Lbl::Tau),
                ensures
                    self.progress() is Unready,
                    self.remaining_steps() == old(self).remaining_steps(),
                    self.sys_st() == sys_post,
                    self.env_st() == stub@.st(),
            {}

            // XXX: Problem with this approach: A non-terminating program could take one invalid
            // step and just not register it. Do we have termination checking for exec now?
            // Otherwise we'll have to change this to "pre-register" transitions before taking
            // them.
            #[verifier(external_body)]
            pub proof fn register_external_step(tracked &mut self, tracked stub: Tracked<EnvM::Interface::Stub>, sys_post: SysM::SysState)
                requires
                    old(self).remaining_steps().len() > 0,
                    old(self).progress() is TokenWithdrawn,
                    SysM::next(old(self).st(), SysM::State { sys: sys_post, env: stub@.st() }, old(self).remaining_steps().first()),
                ensures
                    self.progress() is Unready,
                    self.remaining_steps() == old(self).remaining_steps().drop_first(),
                    self.sys_st() == sys_post,
                    self.env_st() == stub@.st(),
            {}
        }

        pub exec fn do_mapstart(state: &mut Tracked<SysM::Interface::Token>, va: usize, pa: usize)
            requires
                old(state)@.sys_st().thread_state is Idle,
                old(state)@.remaining_steps().len() > 0,
                old(state)@.remaining_steps().first() == SysM::Lbl::MapStart(va as nat, pa as nat),
                old(state)@.progress() is Unready,
            ensures
                // XXX: can't directly use the transition definition because of the additional
                // environment transitions :(
                // This may get a bit unwieldy with larger state machines like we have with the
                // page table.
                //SysM::step_MapStart(old(state)@.st(), state@.st(), SysM::Lbl::MapStart(va as nat, pa as nat)),
                state@.env_st().ptmem == old(state)@.env_st().ptmem,
                state@.sys_st().thread_state == SysM::TState::Mapping(va as nat, pa as nat),
                state@.remaining_steps() == old(state)@.remaining_steps().drop_first(),
                state@.progress() is Ready,
        {
            // Allow concurrent transitions to get `progress()` to `Ready`
            proof {
                let pre_concurrent_state = state@;
                let pidx = state.borrow_mut().do_concurrent_trs();
                SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
            }

            let tracked env_token = state.borrow_mut().get_env_token();
            // MapStart is a stutter step in the environment state machine
            let stub = EnvM::Interface::stutter(Tracked(env_token));

            // We change the thread_state with a MapStart transition
            let ghost sys_post = SysM::SysState {
                thread_state: SysM::TState::Mapping(va as nat, pa as nat),
            };
            proof {
                assert(SysM::next_step(
                        state@.st(),
                        SysM::State { sys: sys_post, env: stub@.st() },
                        SysM::Step::MapStart,
                        SysM::Lbl::MapStart(va as nat, pa as nat))
                );
                state.borrow_mut().register_external_step(stub, sys_post);
            }

            // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
            proof {
                let pre_concurrent_state = state@;
                let pidx = state.borrow_mut().do_concurrent_trs();
                SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
            }
        }

        pub exec fn do_mapstutter(state: &mut Tracked<SysM::Interface::Token>, i: usize, v: usize)
            requires
                old(state)@.sys_st().thread_state is Mapping,
                old(state)@.remaining_steps().len() > 0,
                old(state)@.progress() is Ready,
                old(state)@.env_st().ptmem.write(i as nat, v as nat)@ == old(state)@.env_st().ptmem@,
            ensures
                state@.env_st().ptmem@       == old(state)@.env_st().ptmem@,
                state@.sys_st().thread_state == old(state)@.sys_st().thread_state,
                state@.remaining_steps()     == old(state)@.remaining_steps(),
                state@.progress() is Ready,
        {
            let tracked env_token = state.borrow_mut().get_env_token();
            // Do the write
            let stub = EnvM::Interface::remap(Tracked(env_token), i, v);

            proof {
                assert(stub@.lbl() == EnvM::Lbl::Remap(i as nat, v as nat));
                assert(EnvM::next_step(state@.env_st(), stub@.st(), EnvM::Step::Remap, stub@.lbl()));
                assert(SysM::next_step(
                        state@.st(),
                        SysM::State { sys: state@.sys_st(), env: stub@.st() },
                        SysM::Step::MapStutter(i as nat, v as nat),
                        SysM::Lbl::Tau)
                );
                state.borrow_mut().register_internal_step(stub, state@.sys_st());
            }

            // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
            proof {
                let pre_concurrent_state = state@;
                let pidx = state.borrow_mut().do_concurrent_trs();
                SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
            }
        }

        pub exec fn do_mapend(state: &mut Tracked<SysM::Interface::Token>, i: usize, v: usize)
            requires
                old(state)@.sys_st().thread_state is Mapping,
                old(state)@.remaining_steps() =~= seq![SysM::Lbl::MapEnd],
                old(state)@.progress() is Ready,
                ({
                    // https://github.com/verus-lang/verus/issues/1393
                    let va = old(state)@.sys_st().thread_state->Mapping_0;
                    let pa = old(state)@.sys_st().thread_state->Mapping_1;
                    old(state)@.env_st().ptmem.write(i as nat, v as nat)@ == old(state)@.env_st().ptmem@.insert(va, pa)
                }),
            ensures
                ({
                    let va = old(state)@.sys_st().thread_state->Mapping_0;
                    let pa = old(state)@.sys_st().thread_state->Mapping_1;
                    state@.env_st().ptmem@ == old(state)@.env_st().ptmem@.insert(va, pa)
                }),
                state@.sys_st().thread_state == SysM::TState::Idle,
                state@.remaining_steps()     =~= seq![],
                state@.progress() is Ready,
        {
            let tracked env_token = state.borrow_mut().get_env_token();
            // Do the write
            let stub = EnvM::Interface::remap(Tracked(env_token), i, v);

            proof {
                assert(stub@.lbl() == EnvM::Lbl::Remap(i as nat, v as nat));
                assert(EnvM::next_step(state@.env_st(), stub@.st(), EnvM::Step::Remap, stub@.lbl()));

                // We change the thread_state back to Idle
                let sys_post = SysM::SysState {
                    thread_state: SysM::TState::Idle,
                };
                assert(SysM::next_step(
                        state@.st(),
                        SysM::State { sys: sys_post, env: stub@.st() },
                        SysM::Step::MapEnd(i as nat, v as nat),
                        SysM::Lbl::MapEnd)
                );
                state.borrow_mut().register_external_step(stub, sys_post);
            }

            // And then we'll allow for concurrent transitions to set `progress()` to `Ready` again
            proof {
                let pre_concurrent_state = state@;
                let pidx = state.borrow_mut().do_concurrent_trs();
                SysM::Interface::lemma_concurrent_trs(pre_concurrent_state.st(), state@.st(), pidx);
            }
        }

    }

    mod Exec {
        use vstd::prelude::*;
        use super::{ SysM };

        trait CodeVC {
            // XXX: One problem here:
            // * `progress()` is `Unready` so we're forced to prove that we're not relying on
            //   "unstable" preconditions.
            // * But the step of acquiring the lock on this thread is in fact unstable, since
            //   another core might acquire it first.
            // * .. what to do?
            exec fn sys_do_map(pre: Tracked<SysM::Interface::Token>, va: usize, pa: usize) -> (post: Tracked<SysM::Interface::Token>)
                requires
                    pre@.sys_st().thread_state is Idle,
                    pre@.remaining_steps() === seq![SysM::Lbl::MapStart(va as nat, pa as nat), SysM::Lbl::MapEnd],
                    pre@.progress() is Unready,
                ensures
                    post@.remaining_steps() === seq![],
                    post@.progress() is Ready // XXX: maybe not necessary
            ;
        }

        // TODO:
        // If we can directly do the "refinement"/simulation in the implementation, we don't really
        // have a refinement mapping, not even an implicit one. E.g. on a step where a certain field
        // doesn't change, we don't have to prove that according to our refinement mapping that
        // field is unchanged, we can just keep it the same. All that's necessary is that when we
        // do rely on the content of that field, we need to be able to show that it changes in the
        // right way.
        // TODO: How can we recover a trace inclusion argument from this?

        impl CodeVC for () {
            exec fn sys_do_map(pre: Tracked<SysM::Interface::Token>, va: usize, pa: usize) -> (post: Tracked<SysM::Interface::Token>) {
                let mut state = pre;
                SysM::Interface::do_mapstart(&mut state, va, pa);
                let (i, v) = arbitrary_exec(0); // dummy values
                assume(state@.env_st().ptmem.write(i as nat, v as nat)@ == state@.env_st().ptmem@);
                SysM::Interface::do_mapstutter(&mut state, i, v);
                let (i2, v2) = arbitrary_exec(1); // dummy values
                assume(state@.env_st().ptmem.write(i2 as nat, v2 as nat)@ == state@.env_st().ptmem@.insert(va as nat, pa as nat));
                SysM::Interface::do_mapend(&mut state, i2, v2);
                state
            }
        }

        #[verifier(external_body)]
        fn arbitrary_exec(n: usize) -> (usize, usize) {
            unimplemented!()
        }
    }
}


} // verus!
