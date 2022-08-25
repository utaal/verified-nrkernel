#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use seq::*;
use crate::pt_impl::l0;
use crate::aux_defs::{ PageTableEntry, MapResult, UnmapResult };

verus! {

pub struct PageTableVariables {
    pub pt: l0::PageTableContents,
    // pub pt_mem: PageTableMemory,
}

pub enum PageTableStep {
    Map { base: nat, pte: PageTableEntry, result: MapResult },
    Unmap { base: nat, result: UnmapResult },
    Stutter,
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    // TODO: This needs to also consider preconditions at l2 but need to reformulate them to not reference layer.
    // Maybe use contains_entry_size_at_index_atleast instead?
    &&& s1.pt.accepted_mapping(base, pte)
    &&& match result {
        MapResult::Ok => {
            &&& s1.pt.map_frame(base, pte).is_Ok()
            &&& s2.pt === s1.pt.map_frame(base, pte).get_Ok_0()
        },
        MapResult::ErrOverlap => {
            &&& s1.pt.map_frame(base, pte).is_Err()
            &&& s2.pt === s1.pt
        },
    }
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, base: nat, result: UnmapResult) -> bool {
    &&& s1.pt.accepted_unmap(base)
    &&& match result {
        UnmapResult::Ok => {
            &&& s1.pt.unmap(base).is_Ok()
            &&& s2.pt === s1.pt.unmap(base).get_Ok_0()
        },
        UnmapResult::ErrNoSuchMapping => {
            &&& s1.pt.unmap(base).is_Err()
            &&& s2.pt === s1.pt
        },
    }
}

pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(s1: PageTableVariables, s2: PageTableVariables, step: PageTableStep) -> bool {
    match step {
        PageTableStep::Map   { base, pte, result } => step_Map(s1, s2, base, pte, result),
        PageTableStep::Unmap { base, result }      => step_Unmap(s1, s2, base, result),
        PageTableStep::Stutter                     => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

}
