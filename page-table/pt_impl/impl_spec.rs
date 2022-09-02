#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::high_level_spec as hlspec;
use crate::pervasive::*;
use crate::aux_defs::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::pt;

verus! {

// FIXME: What's the pen-and-paper VC here? I think it's: The specification for each of the
// operations specified here results in the corresponding state transition in the *os* state
// machine being satisfied.
// FIXME: do i need to add memory invariant preservation to the ensures?
// Do i actually need it?
pub trait PTImpl {
    spec fn interp(&self) -> pt::PageTableVariables;

    spec fn inv(&self) -> bool;

    proof fn init_implies_inv(&self)
        requires
            pt::init(self.interp())
        ensures
            self.inv();

    fn map_frame(&mut self, base: usize, pte: PageTableEntryExec) -> (res: MapResult)
        requires
            pt::step_Map_preconditions(base, pte@),
            old(self).inv(),
        ensures
            self.inv(),
            pt::step_Map(old(self).interp(), self.interp(), base, pte@, res);

    // FIXME: do i need to add tlb state to the pt state machine?
    fn unmap(&mut self, base: usize) -> (res: UnmapResult)
        requires
            pt::step_Unmap_preconditions(base),
            old(self).inv(),
        ensures
            self.inv(),
            pt::step_Unmap(old(self).interp(), self.interp(), base, res);
            // FIXME: tlb stuff
}

}
