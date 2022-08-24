#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use seq::*;
use crate::pt_impl::l0;
use crate::aux_defs::{ PageTableEntry };

verus! {

pub struct PageTableVariables {
    pub pt: l0::PageTableContents,
    // pub pt_mem: PageTableMemory,
}

pub enum PageTableStep {
    Map { base: nat, pte: PageTableEntry },
    Unmap { base: nat },
    Noop,
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, base: nat, pte: PageTableEntry) -> bool {
    &&& arbitrary()
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, base: nat) -> bool {
    &&& arbitrary()
}

pub open spec fn step_Noop(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(s1: PageTableVariables, s2: PageTableVariables, step: PageTableStep) -> bool {
    match step {
        PageTableStep::Map   { base, pte } => step_Map(s1, s2, base, pte),
        PageTableStep::Unmap { base }      => step_Unmap(s1, s2, base),
        PageTableStep::Noop                => step_Noop(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

}
