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
use crate::spec_t::mem;

use result::{*, Result::*};

use crate::definitions_t::{ MemRegionExec, Flags, x86_arch, x86_arch_exec, x86_arch_exec_spec, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, candidate_mapping_in_bounds, aligned, candidate_mapping_overlaps_existing_vmem, new_seq, lemma_new_seq, x86_arch_inv };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::spec_t::impl_spec;
use crate::impl_u::l2_impl;
use crate::impl_u::spec_pt;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult, ResolveResultExec };
use crate::spec_t::hardware::{interp_pt_mem,axiom_page_table_walk_interp};

verus! {

pub struct PageTableImpl {}

spec fn dummy_trigger(x: l2_impl::PTDir) -> bool {
    true
}

impl impl_spec::InterfaceSpec for PageTableImpl {
    spec fn ispec_inv(&self, memory: mem::PageTableMemory) -> bool {
        exists|ghost_pt: l2_impl::PTDir| {
            let page_table = l2_impl::PageTable {
                memory: memory,
                arch: x86_arch_exec_spec(),
                ghost_pt: Ghost::new(ghost_pt),
            };
            &&& page_table.inv()
            &&& page_table.interp().inv()
            &&& #[trigger] dummy_trigger(ghost_pt)
        }
    }

    fn ispec_map_frame(&self, memory: mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory)) {
        // requires
        assert(spec_pt::step_Map_enabled(interp_pt_mem(memory), vaddr, pte@));
        assert(aligned(vaddr, pte@.frame.size));
        assert(aligned(pte.frame.base, pte@.frame.size));
        assert(candidate_mapping_in_bounds(vaddr, pte@));
        assert({
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        });
        assert(self.ispec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    arch: x86_arch_exec_spec(),
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let x86_arch_exec_v = x86_arch_exec();
        // FIXME: problem with definition
        assume(x86_arch_exec_spec() === x86_arch_exec_v);
        assert(x86_arch_exec_spec()@ === x86_arch);

        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            arch:      x86_arch_exec_v,
            ghost_pt:  ghost_pt,
        };
        assert(page_table.inv());
        assert(page_table.arch@.inv());
        assert(page_table.interp().inv());

        assert(x86_arch_exec_spec()@ === page_table.arch@);
        assert(page_table.arch@ === x86_arch);

        assert(page_table.accepted_mapping(vaddr, pte@)) by {
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
            assert(page_table.interp().upper_vaddr() == page_table.arch@.upper_vaddr(0, 0));
        }
        assert(page_table.interp().accepted_mapping(vaddr, pte@));
        assert(page_table.arch@.num_entries(0) == 512);
        // FIXME: incompleteness?
        assume(page_table.arch@.num_entries(0) * page_table.arch@.entry_size(0) == 512 * L0_ENTRY_SIZE);
        assert(MAX_BASE == 512 * L0_ENTRY_SIZE);
        assert(page_table.arch@.upper_vaddr(0, 0) == page_table.arch@.num_entries(0) * page_table.arch@.entry_size(0));
        assert(page_table.arch@.upper_vaddr(0, 0) <= MAX_BASE);
        let old_page_table: Ghost<l2_impl::PageTable> = ghost(page_table);
        let res = page_table.map_frame(vaddr, pte);
        assert(page_table.inv());
        assert(page_table.interp().inv());
        // ensures
        proof {
            let page_table_post_state = page_table;
            assert(self.ispec_inv(page_table.memory)) by {
                assert(dummy_trigger(page_table_post_state.ghost_pt@));
            };
            axiom_page_table_walk_interp();
            old_page_table@.interp().lemma_inv_implies_interp_inv();
            page_table.interp().lemma_inv_implies_interp_inv();
            if candidate_mapping_overlaps_existing_vmem(interp_pt_mem(memory), vaddr, pte@) {
                assert(res.is_ErrOverlap());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory));
            } else {
                assert(res.is_Ok());
                assert(interp_pt_mem(page_table.memory) === interp_pt_mem(memory).insert(vaddr, pte@));
            }
            assert(spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(page_table.memory) }, vaddr, pte@, res));
        }
        (res, page_table.memory)
    }

    fn ispec_unmap(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (UnmapResult, mem::PageTableMemory)) {
        assume(false);
        (UnmapResult::Ok, memory)
    }

    fn ispec_resolve(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (ResolveResultExec, mem::PageTableMemory)) {
        assert(self.ispec_inv(memory));
        let ghost_pt: Ghost<l2_impl::PTDir> = ghost(
            choose|ghost_pt: l2_impl::PTDir| {
                let page_table = l2_impl::PageTable {
                    memory: memory,
                    arch: x86_arch_exec_spec(),
                    ghost_pt: Ghost::new(ghost_pt),
                };
                &&& page_table.inv()
                &&& page_table.interp().inv()
                &&& #[trigger] dummy_trigger(ghost_pt)
            }
        );

        let x86_arch_exec_v = x86_arch_exec();
        // FIXME: problem with definition
        assume(x86_arch_exec_spec() === x86_arch_exec_v);
        assert(x86_arch_exec_spec()@ === x86_arch);

        let page_table = l2_impl::PageTable {
            memory:    memory,
            arch:      x86_arch_exec_v,
            ghost_pt:  ghost_pt,
        };
        assert(page_table.inv());
        assert(page_table.arch@.inv());
        assert(page_table.interp().inv());

        assert(x86_arch_exec_spec()@ === page_table.arch@);
        assert(page_table.arch@ === x86_arch);

        proof {
            let cr3 = page_table.memory.cr3_spec();
            page_table.lemma_interp_at_facts(0, cr3.base, 0, page_table.ghost_pt@);
            assert(page_table.interp().upper_vaddr() == page_table.arch@.upper_vaddr(0, 0));
        }
        assume(false);
        match page_table.resolve(vaddr) {
            Ok((v,pte)) => (ResolveResultExec::Ok(v,pte), page_table.memory),
            Err(e)      => (ResolveResultExec::ErrUnmapped, page_table.memory),
        }
    }
}

// Can't directly do it in trait because of Verus bug.
proof fn ispec_init_implies_inv(memory: mem::PageTableMemory)
    requires
        memory.inv(),
        memory.regions() === set![memory.cr3_spec()@],
        memory.region_view(memory.cr3_spec()@).len() == 512,
        (forall|i: nat| i < 512 ==> memory.region_view(memory.cr3_spec()@)[i] == 0),
    ensures
        exists|ghost_pt: l2_impl::PTDir| {
                    let page_table = l2_impl::PageTable {
                        memory: memory,
                        arch: x86_arch_exec_spec(),
                        ghost_pt: Ghost::new(ghost_pt),
                    };
                    &&& page_table.inv()
                    &&& page_table.interp().inv()
                    &&& #[trigger] dummy_trigger(ghost_pt)
                }
{
    let ptr: usize = memory.cr3_spec().base;
    memory.cr3_facts();
    let pt = l2_impl::PTDir {
        region: memory.cr3_spec()@,
        entries: new_seq(512, Option::None),
        used_regions: set![memory.cr3_spec()@],
    };
    lemma_new_seq::<Option<l2_impl::PTDir>>(512, Option::None);
    let page_table = l2_impl::PageTable {
        memory: memory,
        arch: x86_arch_exec_spec(),
        ghost_pt: Ghost::new(pt),
    };
    assert(page_table.inv()) by {
        // FIXME: problem with definition
        assume(x86_arch_exec_spec()@ === x86_arch);
        x86_arch_inv();
        assert(page_table.well_formed(0, ptr));
        assert(page_table.memory.inv());
        assert(page_table.memory.regions().contains(pt.region));
        assert(pt.region.base == ptr);
        assert(pt.region.size == PAGE_SIZE);
        assert(page_table.memory.region_view(pt.region).len() == pt.entries.len());
        assert(page_table.layer_in_range(0));
        assert(pt.entries.len() == page_table.arch@.num_entries(0));
        page_table.lemma_zeroed_page_implies_empty_at(0, ptr, pt);
        assert(page_table.directories_obey_invariant_at(0, ptr, pt));
        assert(page_table.ghost_pt_matches_structure(0, ptr, pt));
        assert(page_table.ghost_pt_used_regions_rtrancl(0, ptr, pt));
        assert(page_table.ghost_pt_used_regions_pairwise_disjoint(0, ptr, pt));
        assert(page_table.ghost_pt_region_notin_used_regions(0, ptr, pt));
        assert(pt.used_regions.subset_of(page_table.memory.regions()));
        assert(page_table.entry_addrs_are_zero_padded(0, ptr, pt));
    };

    // FIXME:
    assume(page_table.interp().inv());
    assert(dummy_trigger(pt));
}

}
