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
use crate::mem_t as mem;

use result::{*, Result::*};

use crate::definitions_t::{ x86_arch_exec, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::spec_t::impl_spec;
use crate::impl_u::l2_impl;
use crate::impl_u::spec_pt;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::spec_t::hardware::interp_pt_mem;

verus! {

pub struct PageTableImpl {}

spec fn dummy_trigger(x: l2_impl::PTDir) -> bool {
    true
}

impl impl_spec::PTImpl for PageTableImpl {
    spec fn implspec_inv(&self, memory: mem::PageTableMemory) -> bool {
        exists|ghost_pt: l2_impl::PTDir| {
            let page_table = l2_impl::PageTable {
                memory: memory,
                arch: x86_arch_exec,
                ghost_pt: Ghost::new(ghost_pt),
            };
            &&& page_table.inv()
            &&& page_table.interp().inv()
            &&& #[trigger] dummy_trigger(ghost_pt)
        }
    }

    fn implspec_map_frame(&self, memory: mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory)) {
        // requires
        assert(spec_pt::step_Map_preconditions(base, pte@));
        // assert(aligned(base, pte@.frame.size));
        // assert(aligned(pte.frame.base, pte@.frame.size));
        // assert(candidate_mapping_in_bounds(base, pte@));
        // assert({
        //     ||| pte.frame.size == L3_ENTRY_SIZE
        //     ||| pte.frame.size == L2_ENTRY_SIZE
        //     ||| pte.frame.size == L1_ENTRY_SIZE
        // });
        assert(self.implspec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    arch: x86_arch_exec,
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            arch:      x86_arch_exec,
            ghost_pt:  ghost_pt,
        };
        assert(page_table.inv());
        assert(page_table.interp().inv());

        assert(page_table.accepted_mapping(base, pte@)) by {
            reveal(l2_impl::PageTable::accepted_mapping);
            assume(false);
        };
        assume(page_table.interp().accepted_mapping(base, pte@));
        let res = page_table.map_frame(base, pte);
        assert(page_table.inv());
        assert(page_table.interp().inv());
        // ensures
        proof {
            let page_table_post_state = page_table;
            assert(self.implspec_inv(page_table.memory)) by {
                assert(dummy_trigger(page_table_post_state.ghost_pt@));
            };
            assume(spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(page_table.memory) }, base, pte@, res));
        }
        (res, page_table.memory)
    }

    // fn implspec_unmap(&self, memory: &mut mem::PageTableMemory, base: usize) -> (res: UnmapResult) {
    //     assume(false);
    //     UnmapResult::Ok
    // }
}

}
