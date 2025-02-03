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
}

impl Constants {
    pub open spec fn valid_core(self, core: Core) -> bool {
        arbitrary() // FIXME: ??
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
    arbitrary() // FIXME: ??
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


} // verus!
