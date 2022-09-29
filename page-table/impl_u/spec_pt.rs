#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

use seq::*;
use map::*;
use option::{*, Option::*};
use crate::impl_u::l0;
use crate::definitions_t::{ PageTableEntry, MapResult, UnmapResult, ResolveResult, Arch, overlap, MemRegion, aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
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
}

pub enum PageTableStep {
    Map     { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap   { vaddr: nat, result: UnmapResult },
    Resolve { vaddr: nat, result: ResolveResult },
    Stutter,
}

pub open spec fn step_Map_enabled(map: Map<nat,PageTableEntry>, vaddr: nat, pte: PageTableEntry) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(map, vaddr, pte)
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& step_Map_enabled(s1.map, vaddr, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.map, vaddr, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.map === s1.map
    } else {
        &&& result.is_Ok()
        &&& s2.map === s1.map.insert(vaddr, pte)
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE)
        ||| aligned(vaddr, L2_ENTRY_SIZE)
        ||| aligned(vaddr, L1_ENTRY_SIZE)
    }
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, result: UnmapResult) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& if s1.map.dom().contains(vaddr) {
        &&& result.is_Ok()
        &&& s2.map === s1.map.remove(vaddr)
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.map === s1.map
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
}

pub open spec fn step_Resolve(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, result: ResolveResult) -> bool {
    &&& step_Resolve_enabled(vaddr)
    &&& s2 === s1
    &&& match result {
        ResolveResult::Ok(base, pte) => {
            // If result is Ok, it's an existing mapping that contains vaddr..
            &&& s1.map.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
        },
        ResolveResult::ErrUnmapped => {
            // If result is ErrUnmapped, no mapping containing vaddr exists..
            &&& (!exists|base: nat, pte: PageTableEntry| s1.map.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size))
        },
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
        PageTableStep::Map     { vaddr, pte, result } => step_Map(s1, s2, vaddr, pte, result),
        PageTableStep::Unmap   { vaddr, result }      => step_Unmap(s1, s2, vaddr, result),
        PageTableStep::Resolve { vaddr, result }      => step_Resolve(s1, s2, vaddr, result),
        PageTableStep::Stutter                        => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

}
