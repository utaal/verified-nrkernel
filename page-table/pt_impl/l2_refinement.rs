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

use crate::aux_defs::{ x86_arch_exec, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE };
use crate::pt_impl::l1;
use crate::pt_impl::l0::{ambient_arith};
use crate::pt_impl::impl_spec;
use crate::pt_impl::l2_impl;
use crate::mem::{ self, word_index_spec };
use crate::pt;
use crate::aux_defs::{ PageTableEntryExec, MapResult, UnmapResult };

verus! {

pub struct PageTableImpl {}

impl impl_spec::PTImpl for PageTableImpl {
    spec fn implspec_inv(&self, memory: mem::PageTableMemory) -> bool {
        exists|ghost_pt: Ghost<l2_impl::PTDir>| {
            let page_table = l2_impl::PageTable {
                memory: memory,
                arch: x86_arch_exec,
                ghost_pt: ghost_pt,
            };
            &&& page_table.inv()
            &&& page_table.interp().inv()
        }
    }

    fn implspec_map_frame(&self, memory: mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory)) {
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
        assert(self.implspec_inv(memory));
        let ghost_pt = choose|ghost_pt: Ghost<l2_impl::PTDir>| {
            let page_table = l2_impl::PageTable {
                memory: memory,
                arch: x86_arch_exec,
                ghost_pt: ghost_pt,
            };
            &&& page_table.inv()
            &&& page_table.interp().inv()
        };

        let page_table = l2_impl::PageTable {
            memory: memory,
            arch: x86_arch_exec,
            ghost_pt: ghost_pt,
        };
        assert(page_table.inv());
        assert(page_table.interp().inv());

        assert(page_table.accepted_mapping(base, pte@)) by {
            reveal(l2_impl::PageTable::accepted_mapping);
        };
        let res = page_table.map_frame(base, pte);
        // ensures
        assert(self.implspec_inv(memory));
        // assume(pt::step_Map(old(page_table).implspec_interp(), page_table.implspec_interp(), base, pte@, res));
        (res, page_table.memory)
    }

    // fn implspec_unmap(&self, memory: &mut mem::PageTableMemory, base: usize) -> (res: UnmapResult) {
    //     assume(false);
    //     UnmapResult::Ok
    // }
}

}
