use vstd::prelude::*;

use crate::definitions_t::{candidate_mapping_overlaps_existing_vmem, PageTableEntry};
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

// Assume `ViewStutter` is any write, that doesn't change the view of the page table memory.
// Then, mapping an entry is a sequence that matches: `(Read | ViewStutter)* Write`
// (Reading, inserting empty directories and finally mapping the entry with a view-affecting write)
// and unmapping an entry is a sequence that matches: `Read* (Write (Read | ViewStutter)*)?`
// (Reading to traverse the tree, then if the entry exists, unmapping it with a view-affecting
// write and unmapping zero or more, now-empty directories)
pub enum ThreadState {
    Idle,
    Mapping,
    /// `result` is `Some`, as soon as the "main" step of unmapping has happened, i.e. either
    /// removal of the mapped frame, or determination that result is an error
    Unmapping { result: Result<PageTableEntry, ()> },
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
    UnmapStart { vaddr: nat, result: Result<(), ()> },
    UnmapEnd,
    ViewStutter,
    Stutter,
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_Start(
    s1: PageTableVariables,
    s2: PageTableVariables,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& s2 == s1
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
pub open spec fn step_Unmap_Start(
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

pub open spec fn step_Unmap_End(
    s1: PageTableVariables,
    s2: PageTableVariables,
) -> bool {
    &&& s2 == s1
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Stutter
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Stutter(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    s1 == s2
}

pub open spec fn step_View_Stutter(
    s1: PageTableVariables,
    s2: PageTableVariables,
) -> bool {
    &&& s2.interp() == s1.interp()
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
        PageTableStep::MapStart { vaddr, pte }       => step_Map_Start(s1, s2, vaddr, pte),
        PageTableStep::MapEnd { vaddr, pte, result } => step_Map_End(s1, s2, vaddr, pte, result),
        PageTableStep::UnmapStart { vaddr, result }  => step_Unmap_Start(s1, s2, vaddr, result),
        PageTableStep::UnmapEnd                      => step_Unmap_End(s1, s2),
        PageTableStep::ViewStutter                   => step_View_Stutter(s1, s2),
        PageTableStep::Stutter                       => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: PageTableVariables, s2: PageTableVariables) -> bool {
    exists|step: PageTableStep| next_step(s1, s2, step)
}

} // verus!
