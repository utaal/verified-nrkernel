#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::prelude::*;
use modes::*;
use seq::*;
use map::*;
use set::*;
use set_lib::*;
use seq_lib::*;
use crate::spec_t::mem;

use crate::definitions_t::{ MemRegionExec, Flags, x86_arch_spec, x86_arch_exec, x86_arch_exec_spec, axiom_x86_arch_exec_spec, MAX_BASE, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, candidate_mapping_in_bounds, aligned, candidate_mapping_overlaps_existing_vmem, new_seq, lemma_new_seq, x86_arch_inv };
use crate::impl_u::l1;
use crate::impl_u::l0;
use crate::spec_t::impl_spec;
use crate::impl_u::l2_impl;
use crate::impl_u::spec_pt;
use crate::definitions_t::{ PageTableEntry, PageTableEntryExec, MapResult, UnmapResult, ResolveResultExec };
use crate::spec_t::hardware::{interp_pt_mem,lemma_page_table_walk_interp};

verus! {

pub struct PageTableImpl {}

proof fn lemma_no_entries_implies_interp_at_aux_no_entries(pt: l2_impl::PageTable, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, ghost_pt: l2_impl::PTDir)
    requires
        pt.memory.regions() == set![pt.memory.cr3_spec()@],
        (forall|i: nat| i < 512 ==> pt.memory.region_view(pt.memory.cr3_spec()@)[i as int] == 0),
        layer == 0,
        pt.inv_at(layer, ptr, ghost_pt),
        forall|i: nat| i < init.len() ==> init[i as int] == l1::NodeEntry::Empty(),
        init.len() <= 512,
    ensures
        ({ let res = pt.interp_at_aux(layer, ptr, base_vaddr, init, ghost_pt);
            &&& res.len() == 512
            &&& forall|i: nat| i < res.len() ==> res[i as int] == l1::NodeEntry::Empty()
        })
    decreases 512 - init.len()
{
    lemma_new_seq::<Option<l2_impl::PTDir>>(512, Option::None);
    let res = pt.interp_at_aux(layer, ptr, base_vaddr, init, ghost_pt);
    if init.len() >= 512 {
    } else {
        let entry = pt.interp_at_entry(layer, ptr, base_vaddr, init.len(), ghost_pt);
        assert(pt.ghost_pt_matches_structure(layer, ptr, ghost_pt));
        assert forall|i: nat| i < 512 implies pt.view_at(layer, ptr, i, ghost_pt).is_Empty() by {
            let entry = pt.memory.spec_read(i, ghost_pt.region);
            assert((entry & (1u64 << 0)) != (1u64 << 0)) by (bit_vector) requires entry == 0u64;
        };
        assert(entry == l1::NodeEntry::Empty());
        lemma_no_entries_implies_interp_at_aux_no_entries(pt, layer, ptr, base_vaddr, init.push(entry), ghost_pt);
    }
}

pub open spec fn dummy_trigger(x: l2_impl::PTDir) -> bool {
    true
}

impl impl_spec::InterfaceSpec for PageTableImpl {
    closed spec fn ispec_inv(&self, memory: mem::PageTableMemory) -> bool {
        exists|ghost_pt: l2_impl::PTDir| {
            let page_table = l2_impl::PageTable {
                memory: memory,
                ghost_pt: Ghost::new(ghost_pt),
            };
            &&& page_table.inv()
            &&& page_table.interp().inv()
            &&& #[trigger] dummy_trigger(ghost_pt)
        }
    }

    proof fn ispec_init_implies_inv(&self, memory: mem::PageTableMemory) {
        let ptr: usize = memory.cr3_spec().base;
        let pt = l2_impl::PTDir {
            region: memory.cr3_spec()@,
            entries: new_seq(512, Option::None),
            used_regions: set![memory.cr3_spec()@],
        };
        lemma_new_seq::<Option<l2_impl::PTDir>>(512, Option::None);
        let page_table = l2_impl::PageTable {
            memory: memory,
            ghost_pt: Ghost::new(pt),
        };
        assert(page_table.inv()) by {
            x86_arch_inv();
            axiom_x86_arch_exec_spec();
            page_table.lemma_zeroed_page_implies_empty_at(0, ptr, pt);
        };

        lemma_no_entries_implies_interp_at_aux_no_entries(page_table, 0, ptr, 0, seq![], pt);
        assert(page_table.interp().inv());
        assert(dummy_trigger(pt));
    }

    fn ispec_map_frame(&self, memory: mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory)) {
        // requires
        assert(spec_pt::step_Map_enabled(interp_pt_mem(memory), vaddr as nat, pte@));
        assert(aligned(vaddr as nat, pte@.frame.size));
        assert(aligned(pte.frame.base as nat, pte@.frame.size));
        assert(candidate_mapping_in_bounds(vaddr as nat, pte@));
        assert({
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        });
        assert(self.ispec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = Ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            ghost_pt:  ghost_pt,
        };
        assert(page_table.inv());
        assert(page_table.interp().inv());

        assert(page_table.accepted_mapping(vaddr as nat, pte@)) by {
            reveal(l2_impl::PageTable::accepted_mapping);
            if pte@.frame.size == L3_ENTRY_SIZE {
            } else if pte@.frame.size == L2_ENTRY_SIZE {
            } else {
                assert(pte@.frame.size == L1_ENTRY_SIZE);
            }
        };
        proof {
            let cr3 = page_table.memory.cr3_spec();
            page_table.lemma_interp_at_facts(0, cr3.base, 0, page_table.ghost_pt@);
            assert(page_table.interp().upper_vaddr() == x86_arch_spec.upper_vaddr(0, 0));
        }
        assert(page_table.interp().accepted_mapping(vaddr as nat, pte@));
        assert(MAX_BASE == 512 * L0_ENTRY_SIZE);
        let old_page_table: Ghost<l2_impl::PageTable> = Ghost(page_table);
        let res = page_table.map_frame(vaddr, pte);
        assert(page_table.inv());
        assert(page_table.interp().inv());
        // ensures
        proof {
            let page_table_post_state = page_table;
            assert(self.ispec_inv(page_table.memory)) by {
                assert(dummy_trigger(page_table_post_state.ghost_pt@));
            };
            lemma_page_table_walk_interp();
            old_page_table@.interp().lemma_inv_implies_interp_inv();
            page_table.interp().lemma_inv_implies_interp_inv();
            if candidate_mapping_overlaps_existing_vmem(interp_pt_mem(memory), vaddr as nat, pte@) {
                assert(res.is_ErrOverlap());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory));
            } else {
                assert(res.is_Ok());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory).insert(vaddr as nat, pte@));
            }
            assert(spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(page_table.memory) }, vaddr as nat, pte@, res));
        }
        (res, page_table.memory)
    }

    fn ispec_unmap(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (UnmapResult, mem::PageTableMemory)) {
        assert(self.ispec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = Ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            ghost_pt:  ghost_pt,
        };
        proof {
            let cr3 = page_table.memory.cr3_spec();
            page_table.lemma_interp_at_facts(0, cr3.base, 0, page_table.ghost_pt@);
            page_table.interp().lemma_inv_implies_interp_inv();
        }
        let res = page_table.unmap(vaddr);
        // ensures
        proof {
            assert(self.ispec_inv(page_table.memory)) by {
                assert(dummy_trigger(page_table.ghost_pt@));
            };
            lemma_page_table_walk_interp();
            page_table.interp().lemma_inv_implies_interp_inv();
            assert(spec_pt::step_Unmap(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(page_table.memory) }, vaddr as nat, res));
        }
        (res, page_table.memory)

    }

    fn ispec_resolve(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (ResolveResultExec, mem::PageTableMemory)) {
        assert(self.ispec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = Ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let page_table = l2_impl::PageTable {
            memory:    memory,
            ghost_pt:  ghost_pt,
        };
        proof {
            x86_arch_inv();
        }
        assert(page_table.inv());
        assert(page_table.interp().inv());

        proof {
            let cr3 = page_table.memory.cr3_spec();
            page_table.lemma_interp_at_facts(0, cr3.base, 0, page_table.ghost_pt@);
            assert(page_table.interp().upper_vaddr() == x86_arch_spec.upper_vaddr(0, 0));
            assert(page_table.interp().interp().upper == x86_arch_spec.upper_vaddr(0, 0));
            assert(MAX_BASE == 512 * L0_ENTRY_SIZE);
            assert(page_table.interp().interp().accepted_resolve(vaddr as nat));
            lemma_page_table_walk_interp();
        }
        assert(page_table.interp().interp().map == interp_pt_mem(memory));
        match page_table.resolve(vaddr) {
            Ok((v,pte)) => (ResolveResultExec::Ok(v,pte),   page_table.memory),
            Err(e)      => (ResolveResultExec::ErrUnmapped, page_table.memory),
        }
    }
}

}
