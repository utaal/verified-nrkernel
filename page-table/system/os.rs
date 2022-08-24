#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use crate::system::spec as system;
use crate::pt;
use crate::aux_defs::{ PageTableEntry };
use crate::high_level_spec;

verus! {

pub struct OSVariables {
    pub system: system::SystemVariables,
    // pub pt: pt::PageTableVariables,
}

pub open spec fn pt_vars_from_system_vars(s: system::SystemVariables) -> pt::PageTableVariables {
    pt::PageTableVariables {
        pt: system::interp_pt_mem(s.pt_mem),
    }
}

pub open spec fn step_System(s1: OSVariables, s2: OSVariables, system_step: system::SystemStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& system::next_step(s1.system, s2.system, system_step)
    &&& pt::step_Noop(pt_vars_from_system_vars(s1.system), pt_vars_from_system_vars(s2.system))
}

pub open spec fn step_Map(s1: OSVariables, s2: OSVariables, base: nat, pte: PageTableEntry) -> bool {
    &&& system::step_PTMemOp(s1.system, s2.system)
    &&& pt::step_Map(pt_vars_from_system_vars(s1.system), pt_vars_from_system_vars(s2.system), base, pte)
}

pub open spec fn step_Unmap(s1: OSVariables, s2: OSVariables, base: nat) -> bool {
    &&& system::step_PTMemOp(s1.system, s2.system)
    &&& pt::step_Unmap(pt_vars_from_system_vars(s1.system), pt_vars_from_system_vars(s2.system), base)
}

pub enum OSStep {
    System { step: system::SystemStep },
    Map { base: nat, pte: PageTableEntry },
    Unmap { base: nat },
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::System { step }      => step_System(s1, s2, step),
        OSStep::Map    { base, pte } => step_Map(s1, s2, base, pte),
        OSStep::Unmap  { base }      => step_Unmap(s1, s2, base),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

// FIXME:
pub open spec fn os_step_to_abstract_step(step: OSStep) -> high_level_spec::AbstractStep;

pub open spec fn os_state_to_abstract_state(s: OSVariables) -> high_level_spec::AbstractVariables;

proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        next_step(s1, s2, step)
    ensures
        high_level_spec::next_step(os_state_to_abstract_state(s1), os_state_to_abstract_state(s2), os_step_to_abstract_step(step))
{
    assume(false);
}

}
