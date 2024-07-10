use vstd::prelude::*;

use crate::definitions_t::{
    aligned, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_vmem,
    PageTableEntry, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR, x86_arch_spec
};
use crate::spec_t::hardware;
use crate::spec_t::mem;

// trusted: not trusted
// the interface spec is written in such a way that it guarantees that the impl behaves according
// to the state machine, and then in the OS state machine we use these definitions, but the actual
// content of these definitions does not matter because:
//
// if we were to mis-specify things in this file, we wouldn't be able to prove the state machine
// refinement
//
// if we split impl <-> system state machines, this becomes trusted for the impl
verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// State
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub struct PageTableVariables {
    pub pt_mem: mem::PageTableMemory,
}

impl PageTableVariables {
    /// Interpretation of the memory according to the MMU's semantics.
    pub open spec fn interp(self) -> Map<nat, PageTableEntry> {
        hardware::interp_pt_mem(self.pt_mem)
    }
}

#[allow(inconsistent_fields)]
pub enum PageTableStep {
    MapStart { vaddr: nat, pte: PageTableEntry },
    MapEnd { vaddr: nat, pte: PageTableEntry, result: Result<(), ()> },
    UnmapStart { vaddr: nat },
    UnmapEnd { vaddr: nat, result: Result<(), ()> },
    Stutter,
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_enabled(s: PageTableVariables, vaddr: nat, pte: PageTableEntry) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& s.pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_Map_Start(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& step_Map_enabled(s1, vaddr, pte)
    &&& s1 == s2
}

pub open spec fn step_Map_End(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    pte: PageTableEntry,
    result: Result<(), ()>,
) -> bool {
    if candidate_mapping_overlaps_existing_vmem(s1.interp(), vaddr, pte) {
        &&& result is Err
        &&& s2.interp() == s1.interp()
    } else {
        &&& result is Ok
        &&& s2.interp() == s1.interp().insert(vaddr, pte)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap_Start(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& s1 == s2
}

pub open spec fn step_Unmap_End(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    result: Result<(), ()>,
) -> bool {
    if s1.interp().dom().contains(vaddr) {
        &&& result is Ok
        &&& s2.interp() == s1.interp().remove(vaddr)
    } else {
        &&& result is Err
        &&& s2.interp() == s1.interp()
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Stutter
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 == s2
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Init
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn init(s: PageTableVariables) -> bool {
    &&& s.pt_mem.inv()
    &&& s.pt_mem.regions() === set![s.pt_mem.cr3_spec()@]
    &&& s.pt_mem.region_view(s.pt_mem.cr3_spec()@).len() == 512
    &&& (forall|i: nat| i < 512 ==> s.pt_mem.region_view(s.pt_mem.cr3_spec()@)[i as int] == 0)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Next_Step
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn next_step(
    s1: PageTableVariables,
    s2: PageTableVariables,
    step: PageTableStep,
) -> bool {
    match step {
        PageTableStep::MapStart { vaddr, pte } => step_Map_Start(s1, s2, vaddr, pte),
        PageTableStep::MapEnd { vaddr, pte, result } => step_Map_End(s1, s2, vaddr, pte, result),
        PageTableStep::UnmapStart { vaddr } => step_Unmap_Start(s1, s2, vaddr),
        PageTableStep::UnmapEnd { vaddr, result } => step_Unmap_End(s1, s2, vaddr, result),
        PageTableStep::Stutter => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

} // verus!
