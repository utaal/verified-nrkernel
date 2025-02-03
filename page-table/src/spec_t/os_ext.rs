use vstd::prelude::*;
use crate::spec_t::mmu::defs::{ Core };

verus! {

// This is the extra/external part of the OS. It specifies the kernel lock, (de-)allocation, and
// shootdown coordination

pub enum Lbl {
    Tau,
    AcquireLock { core: Core },
    ReleaseLock { core: Core },
    InitShootdown { core: Core, vaddr: nat, cores: Set<Core> },
    AckShootdown { core: Core },
    //Alloc { core: Core, res: MemRegion },
    //Dealloc { core: Core, reg: MemRegion },
}

pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    // TODO: allocation stuff
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

pub enum Step {
    AcquireLock,
    ReleaseLock,
    InitShootdown,
    AckShootdown,
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

pub open spec fn step_InitShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InitShootdown { core, vaddr, cores }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests === set![]
    &&& forall|core| cores.contains(core) ==> c.valid_core(core)

    &&& post == State {
        shootdown_vec: ShootdownVector { vaddr, open_requests: cores },
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

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::AcquireLock => step_AcquireLock(pre, post, c, lbl),
        Step::ReleaseLock => step_ReleaseLock(pre, post, c, lbl),
        Step::InitShootdown => step_InitShootdown(pre, post, c, lbl),
        Step::AckShootdown => step_AckShootdown(pre, post, c, lbl),
    }
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.lock === None
    &&& pre.shootdown_vec.open_requests === set![]
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}





// Invariants for this state machine

impl State {
    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| self.shootdown_vec.open_requests.contains(core) ==> #[trigger] c.valid_core(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.wf(c)
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



/// The axiomatized interface to execute the actions specified in this state machine.
pub mod code {
    use vstd::prelude::*;
    use crate::spec_t::os_ext;
    use crate::spec_t::mmu::defs::{ Core };

    #[verifier(external_body)]
    pub tracked struct Token {}

    #[verifier(external_body)]
    pub tracked struct Stub {}

    impl Token {
        pub spec fn consts(self) -> os_ext::Constants;
        pub spec fn pre(self) -> os_ext::State;
        pub spec fn core(self) -> Core;
    }

    impl Stub {
        pub spec fn post(self) -> os_ext::State;
        pub spec fn lbl(self) -> os_ext::Lbl;
    }

    #[verifier(external_body)]
    pub exec fn acquire_lock(Tracked(tok): Tracked<Token>) -> (stub: Tracked<Stub>)
        ensures
            os_ext::step_AcquireLock(tok.pre(), stub@.post(), tok.consts(), stub@.lbl()),
            stub@.lbl() == (os_ext::Lbl::AcquireLock { core: tok.core() }),
    {
        unimplemented!()
    }

    // TODO: Requiring that we hold the lock here is a bit weird because in the transitions we
    // don't really distinguish which preconditions are ones that the user has to satisfy and which
    // ones are consequences of executing the function.
    // But it's probably fine? The function just has to be specified in a way that makes sense.
    #[verifier(external_body)]
    pub exec fn release_lock(Tracked(tok): Tracked<Token>) -> (stub: Tracked<Stub>)
        requires tok.pre().lock == Some(tok.core())
        ensures
            os_ext::step_ReleaseLock(tok.pre(), stub@.post(), tok.consts(), stub@.lbl()),
            stub@.lbl() == (os_ext::Lbl::ReleaseLock { core: tok.core() }),
    {
        unimplemented!()
    }

    // This initiates a shootdown for all other cores in the system, so we don't take the cores as
    // an argument.
    #[verifier(external_body)]
    pub exec fn init_shootdown(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
        ensures
            os_ext::step_InitShootdown(tok.pre(), stub@.post(), tok.consts(), stub@.lbl()),
            stub@.lbl() ==
                (os_ext::Lbl::InitShootdown {
                    core: tok.core(),
                    vaddr: vaddr as nat,
                    cores: Set::new(|core| tok.consts().valid_core(core))
                }),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub exec fn ack_shootdown(Tracked(tok): Tracked<Token>, vaddr: usize) -> (stub: Tracked<Stub>)
        ensures
            os_ext::step_InitShootdown(tok.pre(), stub@.post(), tok.consts(), stub@.lbl()),
            stub@.lbl() ==
                (os_ext::Lbl::InitShootdown {
                    core: tok.core(),
                    vaddr: vaddr as nat,
                    cores: Set::new(|core| tok.consts().valid_core(core))
                }),
    {
        unimplemented!()
    }
}

} // verus!
