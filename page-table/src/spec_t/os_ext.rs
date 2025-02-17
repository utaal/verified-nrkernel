use vstd::prelude::*;
use crate::spec_t::mmu::defs::{ Core, MemRegion };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ overlap, aligned };

verus! {

// This is the extra/external part of the OS. It specifies the kernel lock, (de-)allocation, and
// shootdown coordination

pub enum Lbl {
    Tau,
    AcquireLock { core: Core },
    ReleaseLock { core: Core },
    InitShootdown { core: Core, vaddr: nat },
    AckShootdown { core: Core },
    Allocate { core: Core, res: MemRegion },
    Deallocate { core: Core, reg: MemRegion },
}

pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    pub allocated: Set<MemRegion>,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}

pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
}

impl Constants {
    // FIXME: This is duplicated in mmu constants. Can we somehow get rid of one of these?
    #[verifier(opaque)]
    pub open spec fn valid_core(self, core: Core) -> bool {
        &&& core.node_id < self.node_count
        &&& core.core_id < self.core_count
    }
}

impl State {
    pub open spec fn disjoint_from_allocations(self, reg: MemRegion) -> bool {
        forall|reg2| #[trigger] self.allocated.contains(reg2) ==> !overlap(reg, reg2)
    }
}

pub enum Step {
    AcquireLock,
    ReleaseLock,
    InitShootdown,
    AckShootdown,
    Allocate,
    Deallocate
}

// State machine transitions

pub open spec fn step_AcquireLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AcquireLock { core }

    &&& c.valid_core(core)
    &&& pre.lock is None

    &&& post == State {
        lock: Some(core),
        ..pre
    }
}

pub open spec fn step_ReleaseLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::ReleaseLock { core }

    &&& c.valid_core(core)
    &&& pre.lock == Some(core)

    &&& post == State {
        lock: None,
        ..pre
    }
}

// This initiates a shootdown for all other cores in the system, so we don't take the cores as an
// argument.
pub open spec fn step_InitShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InitShootdown { core, vaddr }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests === set![]

    &&& post == State {
        shootdown_vec: ShootdownVector {
            vaddr,
            open_requests: Set::new(|core| c.valid_core(core))
        },
        ..pre
    }
}

pub open spec fn step_AckShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AckShootdown { core }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests.contains(core)

    &&& post == State {
        shootdown_vec: ShootdownVector {
            open_requests: pre.shootdown_vec.open_requests.remove(core),
            ..pre.shootdown_vec
        },
        ..pre
    }
}

// TODO: Hardcoding 4k allocations for now. Should fix that to support large mappings.
pub open spec fn step_Allocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Allocate { core, res }

    &&& c.valid_core(core)
    &&& pre.disjoint_from_allocations(res)
    &&& aligned(res.base, 4096)
    &&& res.size == 4096

    &&& post == State {
        allocated: pre.allocated.insert(res),
        ..pre
    }
}

pub open spec fn step_Deallocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Deallocate { core, reg }

    &&& c.valid_core(core)
    &&& pre.allocated.contains(reg)

    &&& post == State {
        allocated: pre.allocated.remove(reg),
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::AcquireLock   => step_AcquireLock(pre, post, c, lbl),
        Step::ReleaseLock   => step_ReleaseLock(pre, post, c, lbl),
        Step::InitShootdown => step_InitShootdown(pre, post, c, lbl),
        Step::AckShootdown  => step_AckShootdown(pre, post, c, lbl),
        Step::Allocate      => step_Allocate(pre, post, c, lbl),
        Step::Deallocate    => step_Deallocate(pre, post, c, lbl),
    }
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.lock === None
    &&& pre.shootdown_vec.open_requests === set![]
    &&& pre.allocated === set![]
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}





//// Invariants for this state machine
//
//impl State {
//    pub open spec fn wf(self, c: Constants) -> bool {
//        &&& forall|core| self.shootdown_vec.open_requests.contains(core) ==> #[trigger] c.valid_core(core)
//    }
//
//    pub open spec fn inv(self, c: Constants) -> bool {
//        &&& self.wf(c)
//    }
//} // impl State
//
//
//pub proof fn init_implies_inv(pre: State, c: Constants)
//    requires init(pre, c)
//    ensures pre.inv(c)
//{}
//
//pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next(pre, post, c, lbl),
//    ensures post.inv(c)
//{}



/// The axiomatized interface to execute the actions specified in this state machine.
pub mod code {
    use vstd::prelude::*;
    use crate::spec_t::os_ext;
    use crate::spec_t::mmu::defs::{ Core, MemRegionExec };
    use crate::theorem::TokState;

    #[verifier(external_body)]
    pub tracked struct Token {}

    impl Token {
        pub spec fn consts(self) -> os_ext::Constants;
        pub spec fn core(self) -> Core;
        pub spec fn pre(self) -> os_ext::State;
        pub spec fn post(self) -> os_ext::State;
        pub spec fn lbl(self) -> os_ext::Lbl;
        pub spec fn tstate(self) -> TokState;

        pub open spec fn set_valid(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.post() == self.post()
            &&& new.lbl() == self.lbl()
            &&& new.tstate() is Validated
        }

        pub open spec fn prophesied_step(self, new: Token) -> bool {
            &&& new.consts() == self.consts()
            &&& new.core() == self.core()
            &&& new.pre() == self.pre()
            &&& new.tstate() is ProphecyMade
            &&& os_ext::next(new.pre(), new.post(), new.consts(), new.lbl())
        }

        // FIXME: Allowing multiple calls to prophesy functions is unsound because they can give
        // potentially conflicting information about the pre state, which remains unchanged on each call.
        pub proof fn prophesy_acquire_lock(tracked &mut self)
            requires
                //old(self).consts().valid_core(old(self).core()), TODO: ??
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::AcquireLock { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        // TODO: Requiring that we hold the lock here is a bit weird because in the
        // transitions we don't really distinguish which preconditions are ones that the
        // user has to satisfy and which ones are consequences of executing the function.
        // But it's probably fine? The function just has to be specified in a way that
        // makes sense.
        //
        // We have enabling conditions that need to be ensured by the caller and "technical"
        // enabling conditions, which are guaranteed by executing the function. In the first case,
        // the user must show that after an arbitrary sequence of concurrent transitions the
        // condition holds. In the second case, this is a guarantee obtained from the function that
        // must not conflict with what we can derive ourselves from the concurrent transitions.
        //
        // TODO: is it still fine if it's on the prophesy call?
        pub proof fn prophesy_release_lock(tracked &mut self)
            requires
                old(self).tstate() is Init,
                old(self).pre().lock == Some(old(self).core())
            ensures
                self.lbl() == (os_ext::Lbl::ReleaseLock { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_init_shootdown(tracked &mut self, vaddr: usize)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::InitShootdown { core: self.core(), vaddr: vaddr as nat }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_ack_shootdown(tracked &mut self)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() == (os_ext::Lbl::AckShootdown { core: self.core() }),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_allocate(tracked &mut self)
            requires
                old(self).tstate() is Init,
            ensures
                self.lbl() is Allocate,
                self.lbl()->Allocate_core == self.core(),
                old(self).prophesied_step(*self),
        {
            admit();
        }

        pub proof fn prophesy_deallocate(tracked &mut self, reg: MemRegionExec)
            requires
                old(self).tstate() is Init,
                old(self).pre().allocated.contains(reg@),
            ensures
                self.lbl() == (os_ext::Lbl::Deallocate { core: self.core(), reg: reg@ }),
                old(self).prophesied_step(*self),
        {
            admit();
        }
    }

    #[verifier(external_body)]
    pub exec fn acquire_lock(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::AcquireLock { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn release_lock(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::ReleaseLock { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn init_shootdown(Tracked(tok): Tracked<&mut Token>, vaddr: usize)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::InitShootdown { core: old(tok).core(), vaddr: vaddr as nat }),
        ensures
            tok.tstate() is Spent,
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn ack_shootdown(Tracked(tok): Tracked<&mut Token>)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::AckShootdown { core: old(tok).core() }),
        ensures
            tok.tstate() is Spent,
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn allocate(Tracked(tok): Tracked<&mut Token>) -> (res: MemRegionExec)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() matches os_ext::Lbl::Deallocate { core: lbl_core, .. } && lbl_core == old(tok).core(),
        ensures
            tok.tstate() is Spent,
            res@ == old(tok).lbl()->Deallocate_reg,
    {
        unimplemented!() // TODO:
    }

    #[verifier(external_body)]
    pub exec fn deallocate(Tracked(tok): Tracked<&mut Token>, reg: MemRegionExec)
        requires
            old(tok).tstate() is Validated,
            old(tok).lbl() == (os_ext::Lbl::Deallocate { core: old(tok).core(), reg: reg@ }),
        ensures
            tok.tstate() is Spent,
    {
        unimplemented!() // TODO:
    }
}

} // verus!
