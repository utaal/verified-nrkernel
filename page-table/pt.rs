#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;

#[allow(unused_imports)] use seq::*;
use crate::pt_impl::high_level_pt;

verus! {

pub struct PageTableVariables {
    pub pt: high_level_pt::PageTableContents,
    // pub pt_mem: PageTableMemory,
}

pub enum PageTableStep {
    Map,
    Unmap,
    Noop,
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    &&& arbitrary()
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    &&& arbitrary()
}

pub open spec fn step_Noop(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(s1: PageTableVariables, s2: PageTableVariables, step: PageTableStep) -> bool {
    match step {
        PageTableStep::Map  => step_Map(s1, s2),
        PageTableStep::Unmap  => step_Unmap(s1, s2),
        PageTableStep::Noop => step_Noop(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

}
