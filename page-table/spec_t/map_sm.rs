use vstd::prelude::*;

use crate::definitions_t::{candidate_mapping_overlaps_existing_vmem, PageTableEntry};
use crate::spec_t::hardware;
use crate::spec_t::mmu::{self};

verus! {

pub struct State<M: mmu::MMU> {
    pub mmu: M,
    pub thread_state: ThreadState,
}

pub enum ThreadState {
    Mapping { vaddr: nat, pte: PageTableEntry },
    MapWritten { result: Result<(), ()> },
    Done { result: Result<(), ()> },
}

impl<M: mmu::MMU> State<M> {
    pub open spec fn interp_pt_mem(self) -> Map<nat, PageTableEntry> {
        hardware::interp_pt_mem(self.mmu.pt_mem())
    }
}

//#[allow(inconsistent_fields)]
//pub enum Step {
//    MapStart { vaddr: nat, pte: PageTableEntry },
//    MapStutter,
//    MapEnd { vaddr: nat, pte: PageTableEntry, result: Result<(), ()> },
//    Stutter,
//}

pub open spec fn init<M: mmu::MMU>(s: State<M>) -> bool {
    // TODO: does this need an init state? maybe just s.state.inv()?
    arbitrary()
    //&&& s.pt_mem.inv()
    //&&& s.pt_mem.regions() === set![s.pt_mem.cr3_spec()@]
    //&&& s.pt_mem.region_view(s.pt_mem.cr3_spec()@).len() == 512
    //&&& (forall|i: nat| i < 512 ==> s.pt_mem.region_view(s.pt_mem.cr3_spec()@)[i as int] == 0)
}

pub open spec fn step_Read<M: mmu::MMU>(s1: State<M>, s2: State<M>, addr: usize, value: usize) -> bool {
    &&& s1.thread_state is Mapping

    &&& s2.thread_state == s1.thread_state
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
}

pub open spec fn step_WriteStutter<M: mmu::MMU>(s1: State<M>, s2: State<M>, addr: usize, value: usize) -> bool {
    &&& s1.thread_state is Mapping

    &&& s2.thread_state == s1.thread_state
}

pub open spec fn step_WriteChange<M: mmu::MMU>(s1: State<M>, s2: State<M>, addr: usize, value: usize, result: Result<(), ()>) -> bool {
    &&& s1.thread_state matches ThreadState::Mapping { vaddr, pte }

    &&& if candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte) {
        &&& result is Err
        &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    } else {
        &&& result is Ok
        &&& s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte)
    }

    &&& s2.thread_state == ThreadState::MapWritten { result }
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
}

pub open spec fn step_Done<M: mmu::MMU>(s1: State<M>, s2: State<M>) -> bool {
    &&& s1.thread_state matches ThreadState::MapWritten { result }
    &&& s2.thread_state == ThreadState::Done { result }
}

pub open spec fn step_Stutter<M: mmu::MMU>(s1: State<M>, s2: State<M>) -> bool {
    s1 == s2
}

//pub open spec fn next_step(s1: State, s2: State, step: Step) -> bool {
//    match step {
//        Step::MapStart { vaddr, pte }       => step_Map_Start(s1, s2, vaddr, pte),
//        Step::MapStutter                    => step_Map_Stutter(s1, s2),
//        Step::MapEnd { vaddr, pte, result } => step_Map_End(s1, s2, vaddr, pte, result),
//        Step::Stutter                       => step_Stutter(s1, s2),
//    }
//}

//pub open spec fn next(s1: State, s2: State) -> bool {
//    exists|step: Step| next_step(s1, s2, step)
//}

} // verus!
