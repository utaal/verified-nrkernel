#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::high_level_spec as hlspec;
use crate::pervasive::*;
use crate::aux_defs::{ PageTableEntryExec, MapResult };
use crate::pt;

verus! {

pub trait PTImpl {
    spec fn interp(&self) -> pt::PageTableVariables;

    spec fn inv(&self) -> bool;

    proof fn init_implies_inv(&self)
        requires
            pt::init(self.interp())
        ensures
            self.inv();

    fn map_frame(&mut self, vaddr: usize, pte: PageTableEntryExec) -> (res: MapResult)
        requires
            old(self).inv()
        ensures
            self.inv(),
            pt::step_Map(old(self).interp(), self.interp(), vaddr, pte@, res);
}

}
