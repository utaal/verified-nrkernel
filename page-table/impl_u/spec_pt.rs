use vstd::prelude::*;

use crate::spec_t::mem;
use crate::spec_t::hardware;
use crate::definitions_t::{ PageTableEntry, aligned, between,
candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_vmem,
candidate_mapping_overlaps_existing_pmem, PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE,
L2_ENTRY_SIZE, L1_ENTRY_SIZE, MAX_PHYADDR, MAX_BASE };


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
    Map     { vaddr: nat, pte: PageTableEntry, result: Result<(),()> },
    Unmap   { vaddr: nat, result: Result<(),()> },
    Resolve { vaddr: nat, result: Result<(nat,PageTableEntry),()> },
    Stutter,
}

pub open spec fn step_Map_enabled(s: PageTableVariables, vaddr: nat, pte: PageTableEntry) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(s.interp(), vaddr, pte)
    &&& s.pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_Map(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, pte: PageTableEntry, result: Result<(),()>) -> bool {
    &&& step_Map_enabled(s1, vaddr, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.interp(), vaddr, pte) {
        &&& result is Err
        &&& s2.interp() == s1.interp()
    } else {
        &&& result is Ok
        &&& s2.interp() == s1.interp().insert(vaddr, pte)
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH as nat)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, result: Result<(),()>) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& if s1.interp().dom().contains(vaddr) {
        &&& result is Ok
        &&& s2.interp() == s1.interp().remove(vaddr)
    } else {
        &&& result is Err
        &&& s2.interp() == s1.interp()
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
    &&& vaddr < MAX_BASE
}

pub open spec fn step_Resolve(s1: PageTableVariables, s2: PageTableVariables, vaddr: nat, result: Result<(nat,PageTableEntry),()>) -> bool {
    &&& step_Resolve_enabled(vaddr)
    &&& s2 == s1
    &&& match result {
        Ok((base, pte)) => {
            // If result is Ok, it's an existing mapping that contains vaddr..
            &&& s1.interp().contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
        },
        Err(_) => {
            // If result is Err, no mapping containing vaddr exists..
            &&& (!exists|base: nat, pte: PageTableEntry| s1.interp().contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size))
        },
    }
}


pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 == s2
}

pub open spec fn init(s: PageTableVariables) -> bool {
    &&& s.pt_mem.inv()
    &&& s.pt_mem.regions() === set![s.pt_mem.cr3_spec()@]
    &&& s.pt_mem.region_view(s.pt_mem.cr3_spec()@).len() == 512
    &&& (forall|i: nat| i < 512 ==> s.pt_mem.region_view(s.pt_mem.cr3_spec()@)[i as int] == 0)
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
