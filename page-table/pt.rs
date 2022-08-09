#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;

use map::*;
#[allow(unused_imports)] use seq::*;
use crate::spec::{MemRegion, PageTableMemory};

verus! {

pub struct PageTableVariables {
    pub map: Map<nat /* VAddr */, MemRegion>,
    pub pt_mem: PageTableMemory,
}

pub enum PageTableStep {
    Op { undefined: nat },
    Noop,
}

pub open spec fn step_Op(s1: PageTableVariables, s2: PageTableVariables, pt_mem1: Seq<nat>, pt_mem2: Seq<nat>) -> bool {
    &&& s1.pt_mem@ === pt_mem1
    &&& s2.pt_mem@ === pt_mem2
    &&& arbitrary()
}

pub open spec fn step_Noop(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(s1: PageTableVariables, s2: PageTableVariables, step: PageTableStep) -> bool {
    match step {
        PageTableStep::Op { undefined: _ } => step_Op(s1, s2, s1.pt_mem@, s2.pt_mem@),
        PageTableStep::Noop => step_Noop(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

}
