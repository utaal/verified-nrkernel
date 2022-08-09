#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;

use map::*;
use seq::*;
#[allow(unused_imports)] use set::*;
use crate::spec::MemRegion;

use crate::system::spec as system;
use crate::pt;

verus! {

pub struct OSVariables {
    pub system: system::SystemVariables,
    pub pt: pt::PageTableVariables,
}

pub open spec fn step_System(s1: OSVariables, s2: OSVariables, system_step: system::SystemStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& system::next_step(s1.system, s2.system, system_step)
    &&& pt:step_Noop(s1.pt, s2.pt)
}

pub open spec fn step_PT(s1: OSVariables, s2: OSVariables) -> bool {
    &&& system::step_PTMemOp(s1.system, s2.system)
    &&& pt::step_Op(s1.pt, s2.pt, s1.system.pt_mem, s2.system.pt_mem)
    // &&& arbitrary() // TODO: tie the state of pt and system
}

pub enum OSStep {
    System { step: system::SystemStep },
    PT,
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::System { step } => step_System(s1, s2, step),
        OSStep::PT => step_PT(s1, s2),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

}
