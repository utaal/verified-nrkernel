#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::high_level_spec as hlspec;
use crate::pervasive::*;
use crate::aux_defs::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::pt;
use crate::system::spec::interp_pt_mem;
use crate::mem;
use crate::pt::PageTableVariables;

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
            pt::init(PageTableVariables { map: interp_pt_mem(memory) })
        ensures
            self.implspec_inv(memory);

    fn implspec_map_frame(&self, memory: &mut mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (res: MapResult)
        requires
            pt::step_Map_preconditions(base, pte@),
            self.implspec_inv(*old(memory)),
        ensures
            self.implspec_inv(*memory),
            pt::step_Map(PageTableVariables { map: interp_pt_mem(*old(memory)) }, PageTableVariables { map: interp_pt_mem(*memory) }, base, pte@, res);

    // FIXME: do i need to add tlb state to the pt state machine?
    fn implspec_unmap(&self, memory: &mut mem::PageTableMemory, base: usize) -> (res: UnmapResult)
        requires
            pt::step_Unmap_preconditions(base),
            self.implspec_inv(*old(memory)),
        ensures
            self.implspec_inv(*memory),
            pt::step_Unmap(PageTableVariables { map: interp_pt_mem(*old(memory)) }, PageTableVariables { map: interp_pt_mem(*memory) }, base, res);
            // FIXME: tlb stuff
}

}
