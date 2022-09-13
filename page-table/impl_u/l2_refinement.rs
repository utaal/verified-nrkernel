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

use crate::definitions_t::{ x86_arch, x86_arch_exec, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, candidate_mapping_in_bounds, aligned, candidate_mapping_overlaps_existing_vmem };
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
        assert(spec_pt::step_Map_preconditions(interp_pt_mem(memory), base, pte@));
        assert(aligned(base, pte@.frame.size));
        assert(aligned(pte.frame.base, pte@.frame.size));
        assert(candidate_mapping_in_bounds(base, pte@));
        assert({
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        });
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

        assert(x86_arch_exec@ === page_table.arch@);
        // FIXME: problem with definition
        assume(x86_arch_exec@ === x86_arch);

        assert(page_table.accepted_mapping(base, pte@)) by {
            reveal(l2_impl::PageTable::accepted_mapping);
            if pte@.frame.size == L3_ENTRY_SIZE {
            } else if pte@.frame.size == L2_ENTRY_SIZE {
            } else {
                assert(pte@.frame.size == L1_ENTRY_SIZE);
            }
        };
        proof {
            let (cr3_region, cr3) = page_table.memory.cr3_spec();
            page_table.lemma_interp_at_facts(0, cr3, 0, page_table.ghost_pt@);
            assert(page_table.interp().upper_vaddr() == page_table.arch@.upper_vaddr(0, 0));
        }
        assert(page_table.interp().accepted_mapping(base, pte@));
        assert(page_table.arch@.upper_vaddr(0, 0) == page_table.arch@.num_entries(0) * page_table.arch@.entry_size(0));
        assert(page_table.arch@.upper_vaddr(0, 0) <= MAX_BASE);
        let old_page_table: Ghost<l2_impl::PageTable> = ghost(page_table);
        let res = page_table.map_frame(base, pte);
        assert(page_table.inv());
        assert(page_table.interp().inv());
        // ensures
        proof {
            let page_table_post_state = page_table;
            assert(self.implspec_inv(page_table.memory)) by {
                assert(dummy_trigger(page_table_post_state.ghost_pt@));
            };
            impl_spec::axiom_page_table_walk_interp();
            assume(forall|pt: l2_impl::PageTable| pt.inv() ==> #[trigger] pt.interp().interp().map === interp_pt_mem(pt.memory));
            old_page_table@.interp().lemma_inv_implies_interp_inv();
            page_table.interp().lemma_inv_implies_interp_inv();
            if candidate_mapping_overlaps_existing_vmem(interp_pt_mem(memory), base, pte@) {
                assert(res.is_ErrOverlap());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory));
            } else {
                assert(res.is_Ok());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory).insert(base, pte@));
            }
            assert(spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(page_table.memory) }, base, pte@, res));
        }
        (res, page_table.memory)
    }

    fn implspec_unmap(&self, memory: mem::PageTableMemory, base: usize) -> (res: (UnmapResult, mem::PageTableMemory)) {
        assume(false);
        (UnmapResult::Ok, memory)
    }
}

}
