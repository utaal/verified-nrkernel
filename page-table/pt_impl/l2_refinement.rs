#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use modes::*;
use seq::*;
use option::{*, Option::*};
use map::*;
use set::*;
use set_lib::*;
use seq_lib::*;
use vec::*;
use crate::lib_axiom::*;

use result::{*, Result::*};

use crate::aux_defs::{ x86_arch, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE };
use crate::pt_impl::l1;
use crate::pt_impl::l0::{ambient_arith};
use crate::pt_impl::impl_spec;
use crate::mem::{ self, word_index_spec };
use crate::pt;
use crate::aux_defs::{ PageTableEntryExec, MapResult, UnmapResult };

verus! {

pub struct PageTableImpl {}

impl impl_spec::PTImpl for PageTableImpl {
    spec fn implspec_inv(&self, memory: mem::PageTableMemory) -> bool {
        // &&& self.inv()
        // &&& self.interp().inv()
        // &&& self.arch@ === x86_arch
        // &&& self.ghost_pt@.region === 
        true
    }

    fn implspec_map_frame(&self, memory: &mut mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (res: MapResult) {

        // requires
        assert(pt::step_Map_preconditions(base, pte@));
        // assert(aligned(base, pte@.frame.size));
        // assert(aligned(pte.frame.base, pte@.frame.size));
        // assert(candidate_mapping_in_bounds(base, pte@));
        // assert({
        //     ||| pte.frame.size == L3_ENTRY_SIZE
        //     ||| pte.frame.size == L2_ENTRY_SIZE
        //     ||| pte.frame.size == L1_ENTRY_SIZE
        // });
        assert(page_table.accepted_mapping(base, pte@)) by {
            reveal(Self::accepted_mapping);
        };
        assert(page_table.implspec_inv());
        let res = page_table.map_frame(base, pte);
        // ensures
        assert(page_table.implspec_inv());
        assume(pt::step_Map(old(page_table).implspec_interp(), page_table.implspec_interp(), base, pte@, res));
        res
    }

    fn implspec_unmap(&self, memory: &mut mem::PageTableMemory, base: usize) -> (res: UnmapResult) {
        assume(false);
        UnmapResult::Ok
    }
}

}
