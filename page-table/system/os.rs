#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use map::*;

use crate::system::spec as system;
use crate::pt;
use crate::aux_defs::{ between, PageTableEntry, IoOp };
use crate::high_level_spec as hlspec;

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
    &&& pt::step_Stutter(pt_vars_from_system_vars(s1.system), pt_vars_from_system_vars(s2.system))
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

pub open spec fn os_step_to_abstract_step(step: OSStep) -> hlspec::AbstractStep {
    match step {
        OSStep::System { step }      =>
            match step {
                system::SystemStep::IoOp { vaddr, paddr, op, pte } => hlspec::AbstractStep::IoOp { vaddr, op, pte },
                system::SystemStep::PTMemOp                        => arbitrary(),
                system::SystemStep::TLBFill { base, pte }          => hlspec::AbstractStep::Stutter,
                system::SystemStep::TLBEvict { base }              => hlspec::AbstractStep::Stutter,
            },
        OSStep::Map    { base, pte } => hlspec::AbstractStep::Map { base, pte },
        OSStep::Unmap  { base }      => hlspec::AbstractStep::Unmap { base },
    }
}

pub open spec fn os_state_to_abstract_state(s: OSVariables) -> hlspec::AbstractVariables {
    let mappings = system::interp_pt_mem(s.system.pt_mem).map;
    let mem: Map<nat,nat> = Map::new(
        |vaddr: nat| exists|base: nat, pte: PageTableEntry| mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size),
        |vaddr: nat| {
            let (base, pte) = choose|basepte: (nat, PageTableEntry)| #![auto] mappings.contains_pair(basepte.0, basepte.1) && between(vaddr, basepte.0, basepte.0 + basepte.1.frame.size);
            let phys_addr = (pte.frame.base + (vaddr - base)) as nat;
            s.system.mem[phys_addr]
        });
    hlspec::AbstractVariables {
        mem,
        mappings,
    }
}

proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        next_step(s1, s2, step)
    ensures
        hlspec::next_step(os_state_to_abstract_state(s1), os_state_to_abstract_state(s2), os_step_to_abstract_step(step))
{
    let abs_s1   = os_state_to_abstract_state(s1);
    let abs_s2   = os_state_to_abstract_state(s2);
    let abs_step = os_step_to_abstract_step(step);
    match step {
        OSStep::System { step } =>
            match step {
                system::SystemStep::IoOp { vaddr, paddr, op, pte } => {
                    // hlspec::AbstractStep::IoOp { vaddr, op, pte }
                    assume(hlspec::next_step(abs_s1, abs_s2, abs_step));
                },
                system::SystemStep::PTMemOp => assert(false),
                system::SystemStep::TLBFill { base, pte } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
                system::SystemStep::TLBEvict { base } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
            },
        OSStep::Map { base, pte } => {
            assume(hlspec::next_step(abs_s1, abs_s2, abs_step));
            // hlspec::AbstractStep::Map { base, pte }
        },
        OSStep::Unmap { base } => {
            // hlspec::AbstractStep::Unmap { base }
            assert(abs_step === hlspec::AbstractStep::Unmap { base });
            assert(step_Unmap(s1, s2, base));
            assume(hlspec::next_step(abs_s1, abs_s2, abs_step));
        },
    }
}

}
