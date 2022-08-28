#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use seq::*;
use map::*;
use crate::pt_impl::l0;
use crate::aux_defs::{ PageTableEntry, MapResult, UnmapResult, Arch, overlap, MemRegion, aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_mapping };
use crate::aux_defs::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE };

verus! {

pub struct PageTableVariables {
    pub map: Map<nat /* VAddr */, PageTableEntry>,
}

pub enum PageTableStep {
    Map { base: nat, pte: PageTableEntry, result: MapResult },
    Unmap { base: nat, result: UnmapResult },
    Stutter,
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& aligned(base, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(base, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }

    &&& match result {
        MapResult::Ok => {
            &&& !candidate_mapping_overlaps_existing_mapping(s1.map, base, pte)
            &&& s2.map === s1.map.insert(base, pte)
        },
        MapResult::ErrOverlap => {
            &&& candidate_mapping_overlaps_existing_mapping(s1.map, base, pte)
            &&& s2.map === s1.map
        },
    }
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, base: nat, result: UnmapResult) -> bool {
    &&& between(base, PT_BOUND_LOW, PT_BOUND_HIGH)
    &&& { // The given base must be aligned to some valid page size
        ||| aligned(base, L3_ENTRY_SIZE)
        ||| aligned(base, L2_ENTRY_SIZE)
        ||| aligned(base, L1_ENTRY_SIZE)
    }
    &&& match result {
        UnmapResult::Ok => {
            &&& s1.map.dom().contains(base)
            &&& s2.map === s1.map.remove(base)
        },
        UnmapResult::ErrNoSuchMapping => {
            &&& !s1.map.dom().contains(base)
            &&& s2.map === s1.map
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
