#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::hlspec_t as hlspec;
use crate::pervasive::*;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::pt_u as pt;
use crate::system::spec::interp_pt_mem;
use crate::mem_t as mem;

verus! {

pub struct PTState {
    pub memory: mem::PageTableMemory,
}

// FIXME: What's the pen-and-paper VC here? I think it's: The specification for each of the
// operations specified here results in the corresponding state transition in the *os* state
// machine being satisfied.
// FIXME: do i need to add memory invariant preservation to the ensures?
// Do i actually need it?
pub trait PTImpl {
    spec fn implspec_inv(&self, memory: mem::PageTableMemory) -> bool;

    proof fn implspec_init_implies_inv(&self, memory: mem::PageTableMemory)
        requires
            pt::init(pt::PageTableVariables { map: interp_pt_mem(memory) })
        ensures
            self.implspec_inv(memory);

    fn implspec_map_frame(&self, memory: mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory))
        requires
            pt::step_Map_preconditions(base, pte@),
            self.implspec_inv(memory),
        ensures
            self.implspec_inv(res.1),
            pt::step_Map(pt::PageTableVariables { map: interp_pt_mem(memory) }, pt::PageTableVariables { map: interp_pt_mem(res.1) }, base, pte@, res.0);

    // FIXME: do i need to add tlb state to the pt state machine?
    fn implspec_unmap(&self, memory: mem::PageTableMemory, base: usize) -> (res: (UnmapResult, mem::PageTableMemory))
        requires
            pt::step_Unmap_preconditions(base),
            self.implspec_inv(memory),
        ensures
            self.implspec_inv(res.1),
            pt::step_Unmap(pt::PageTableVariables { map: interp_pt_mem(memory) }, pt::PageTableVariables { map: interp_pt_mem(res.1) }, base, res.0);
            // FIXME: tlb stuff
}

}
