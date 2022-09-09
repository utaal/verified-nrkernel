#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use seq::*;
use map::*;
use crate::impl_u::l0;
use crate::definitions_t::{ PageTableEntry, MapResult, UnmapResult, Arch, overlap, MemRegion, aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
use crate::definitions_t::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE };

verus! {

pub struct PageTableVariables {
    pub map: Map<nat /* VAddr */, PageTableEntry>,
}

impl PageTableVariables {
    pub open spec fn mappings_dont_overlap(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.map.contains_pair(b1, pte1) && self.map.contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: pte1.frame.size },
                    MemRegion { base: b2, size: pte2.frame.size }))
    }

    // FIXME: dont think i actually need an invariant here
    pub open spec fn inv(self) -> bool {
        self.mappings_dont_overlap()
    }
}

pub enum PageTableStep {
    Map   { base: nat, pte: PageTableEntry, result: MapResult },
    Unmap { base: nat, result: UnmapResult },
    Stutter,
}

// TODO: discuss not-always-enabled actions unsatisfiable spec problem in thesis

pub open spec fn step_Map_preconditions(base: nat, pte: PageTableEntry) -> bool {
    &&& aligned(base, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(base, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& step_Map_preconditions(base, pte)
    &&& !candidate_mapping_overlaps_existing_pmem(s1.map, base, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.map, base, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.map === s1.map
    } else {
        &&& result.is_Ok()
        &&& s2.map === s1.map.insert(base, pte)
    }
}

pub open spec fn step_Unmap_preconditions(base: nat) -> bool {
    &&& between(base, PT_BOUND_LOW, PT_BOUND_HIGH)
    &&& { // The given base must be aligned to some valid page size
        ||| aligned(base, L3_ENTRY_SIZE)
        ||| aligned(base, L2_ENTRY_SIZE)
        ||| aligned(base, L1_ENTRY_SIZE)
    }
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, base: nat, result: UnmapResult) -> bool {
    &&& step_Unmap_preconditions(base)
    &&& if s1.map.dom().contains(base) {
        &&& result.is_Ok()
        &&& s2.map === s1.map.remove(base)
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.map === s1.map
    }
}

pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 === s2
}

pub open spec fn init(s: PageTableVariables) -> bool {
    s.map === Map::empty()
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
