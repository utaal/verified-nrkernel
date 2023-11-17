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

use crate::definitions_t::{ MemRegionExec, Flags, x86_arch_spec, x86_arch_exec, x86_arch_exec_spec, axiom_x86_arch_exec_spec, MAX_BASE, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, candidate_mapping_in_bounds, aligned, candidate_mapping_overlaps_existing_vmem, new_seq, x86_arch_inv, bitmask_inc, bit };
use crate::definitions_u::{lemma_new_seq};
use crate::impl_u::l1;
use crate::impl_u::l0;
use crate::spec_t::impl_spec;
use crate::impl_u::l2_impl;
use crate::impl_u::spec_pt;
use crate::definitions_t::{ PageTableEntry, PageTableEntryExec, MapResult, UnmapResult, ResolveResultExec, MemRegion };
use crate::spec_t::hardware::{interp_pt_mem, l0_bits, l1_bits, l2_bits, l3_bits, valid_pt_walk, read_entry, GhostPageDirectoryEntry, nat_to_u64};

verus! {

pub proof fn lemma_page_table_walk_interp()
    ensures
        forall|pt: l2_impl::PageTable| #![auto] pt.inv() && pt.interp().inv() ==> pt.interp().interp().map === interp_pt_mem(pt.memory)
{
    assert forall|pt: l2_impl::PageTable| #![auto]
        pt.inv() && pt.interp().inv() implies pt.interp().interp().map === interp_pt_mem(pt.memory)
    by { lemma_page_table_walk_interp_aux(pt); }
}

pub proof fn lemma_page_table_walk_interp_aux(pt: l2_impl::PageTable)
    requires pt.inv() && pt.interp().inv()
    ensures pt.interp().interp().map === interp_pt_mem(pt.memory)
{
    let mem = pt.memory;
    let m1 = interp_pt_mem(mem);
    let m2 = pt.interp().interp().map;
    pt.interp().lemma_inv_implies_interp_inv();
    assert(pt.interp().interp().inv());
    assert forall|addr: nat, pte: PageTableEntry|
        m1.contains_pair(addr, pte) implies #[trigger] m2.contains_pair(addr, pte)
    by {
        let addr: u64 = addr as u64;
        assert(addr < MAX_BASE);
        let pte = choose|pte: PageTableEntry| valid_pt_walk(mem, addr, pte);
        assert(valid_pt_walk(mem, addr as u64, pte));
        pt.lemma_interp_at_facts(0, mem.cr3_spec().base, 0, pt.ghost_pt@);

        let l0_idx_u64:  u64 = l0_bits!(addr);
        let l0_idx:      nat = l0_idx_u64 as nat;
        let l1_idx_u64:  u64 = l1_bits!(addr);
        let l1_idx:      nat = l1_idx_u64 as nat;
        let l2_idx_u64:  u64 = l2_bits!(addr);
        let l2_idx:      nat = l2_idx_u64 as nat;
        let l3_idx_u64:  u64 = l3_bits!(addr);
        let l3_idx:      nat = l3_idx_u64 as nat;
        assert(forall|a:u64| (a & bitmask_inc!(0u64,8u64) == a) ==> a < 512) by (bit_vector);
        assert(l0_idx < 512 && l1_idx < 512 && l2_idx < 512 && l3_idx < 512) by {
            assert(((addr & bitmask_inc!(12u64,20u64)) >> 12u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(12u64,20u64)) >> 12u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(21u64,29u64)) >> 21u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(21u64,29u64)) >> 21u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(30u64,38u64)) >> 30u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(30u64,38u64)) >> 30u64)) by (bit_vector);
            assert(((addr & bitmask_inc!(39u64,47u64)) >> 39u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(39u64,47u64)) >> 39u64)) by (bit_vector);
        };
        assert(bitmask_inc!(39u64,47u64) == 0xFF80_0000_0000) by (compute);
        assert(bitmask_inc!(30u64,38u64) == 0x007F_C000_0000) by (compute);
        assert(bitmask_inc!(21u64,29u64) == 0x0000_3FE0_0000) by (compute);
        assert(bitmask_inc!(12u64,20u64) == 0x0000_001F_F000) by (compute);
        let interp_l0_dir   = pt.interp();
        let interp_l0_entry = pt.interp_at_entry(0, mem.cr3_spec().base, 0, l0_idx, pt.ghost_pt@);
        interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_idx);
        match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
            GhostPageDirectoryEntry::Directory {
                addr: l0_dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
            } => {
                assert(interp_l0_entry.is_Directory());
                let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                let l0_dir_ghost_pt = pt.ghost_pt@.entries[l0_idx as int].get_Some_0();
                assert(pt.directories_obey_invariant_at(0, mem.cr3_spec().base, pt.ghost_pt@));
                assert(pt.inv_at(1, l0_dir_addr, l0_dir_ghost_pt));
                pt.lemma_interp_at_facts(1, l0_dir_addr, l1_base_vaddr, l0_dir_ghost_pt);
                let interp_l1_dir   = pt.interp_at(1, l0_dir_addr, l1_base_vaddr, l0_dir_ghost_pt);
                let interp_l1_entry = pt.interp_at_entry(1, l0_dir_addr, l1_base_vaddr, l1_idx, l0_dir_ghost_pt);
                interp_l1_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l1_idx);
                match read_entry(mem, l0_dir_addr as nat, 1, l1_idx) {
                    GhostPageDirectoryEntry::Page {
                        addr: page_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                    } => {
                        assert(aligned(addr as nat, L1_ENTRY_SIZE as nat));
                        assert(pte == PageTableEntry {
                            frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                            flags: Flags {
                                is_writable:      l0_RW &&  l1_RW,
                                is_supervisor:   !l0_US || !l1_US,
                                disable_execute:  l0_XD ||  l1_XD
                            }
                        });

                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64))) by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                addr % mul(512, mul(512, 4096)) == 0;

                        assert(add(mul(l0_idx_u64, mul(512u64, mul(512, mul(512, 4096)))), mul(l1_idx_u64, mul(512u64, mul(512, 4096)))) == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64) by (bit_vector)
                            requires l0_idx_u64 < 512 && l1_idx_u64 < 512;
                        // Previous assert proves: l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64

                        assert(interp_l1_dir.interp_of_entry(l1_idx).map.contains_pair(addr as nat, pte));
                        assert(interp_l1_dir.interp().map.contains_pair(addr as nat, pte));
                        assert(interp_l0_dir.interp().map.contains_pair(addr as nat, pte));
                        assert(m2.contains_pair(addr as nat, pte));
                    },
                    GhostPageDirectoryEntry::Directory {
                        addr: l1_dir_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                    } => {
                        assert(interp_l1_entry.is_Directory());
                        let l2_base_vaddr = x86_arch_spec.entry_base(1, l1_base_vaddr, l1_idx);
                        let l1_dir_ghost_pt = l0_dir_ghost_pt.entries[l1_idx as int].get_Some_0();
                        assert(pt.directories_obey_invariant_at(1, l0_dir_addr, l0_dir_ghost_pt));
                        assert(pt.inv_at(2, l1_dir_addr, l1_dir_ghost_pt));
                        pt.lemma_interp_at_facts(2, l1_dir_addr, l2_base_vaddr, l1_dir_ghost_pt);
                        let interp_l2_dir   = pt.interp_at(2, l1_dir_addr, l2_base_vaddr, l1_dir_ghost_pt);
                        let interp_l2_entry = pt.interp_at_entry(2, l1_dir_addr, l2_base_vaddr, l2_idx, l1_dir_ghost_pt);
                        interp_l2_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l2_idx);
                        match read_entry(mem, l1_dir_addr as nat, 2, l2_idx) {
                            GhostPageDirectoryEntry::Page {
                                addr: page_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                            } => {
                                assert(aligned(addr as nat, L2_ENTRY_SIZE as nat));
                                assert(pte == PageTableEntry {
                                    frame: MemRegion { base: page_addr as nat, size: L2_ENTRY_SIZE as nat },
                                    flags: Flags {
                                        is_writable:      l0_RW &&  l1_RW &&  l2_RW,
                                        is_supervisor:   !l0_US || !l1_US || !l2_US,
                                        disable_execute:  l0_XD ||  l1_XD ||  l2_XD
                                    }
                                });

                                assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64))) by (bit_vector)
                                    requires
                                        l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                        addr % mul(512, 4096) == 0;

                                assert(add(add(
                                        mul(l0_idx_u64, mul(512u64, mul(512, mul(512, 4096)))),
                                        mul(l1_idx_u64, mul(512u64, mul(512, 4096)))),
                                        mul(l2_idx_u64, mul(512, 4096)))
                                       == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64 | l2_idx_u64 << 21u64) by (bit_vector)
                                    requires l0_idx_u64 < 512 && l1_idx_u64 < 512 && l2_idx_u64 < 512;
                                // Previous assert proves:
                                // l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE + l2_idx * L2_ENTRY_SIZE
                                // == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64 | (l2_idx as u64) << 21u64

                                assert(interp_l2_dir.interp_of_entry(l2_idx).map.contains_pair(addr as nat, pte));
                                assert(interp_l2_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(interp_l1_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(interp_l0_dir.interp().map.contains_pair(addr as nat, pte));
                                assert(m2.contains_pair(addr as nat, pte));
                            },
                            GhostPageDirectoryEntry::Directory {
                                addr: l2_dir_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                            } => {
                                assert(interp_l2_entry.is_Directory());
                                let l3_base_vaddr = x86_arch_spec.entry_base(2, l2_base_vaddr, l2_idx);
                                let l2_dir_ghost_pt = l1_dir_ghost_pt.entries[l2_idx as int].get_Some_0();
                                assert(pt.directories_obey_invariant_at(2, l1_dir_addr, l1_dir_ghost_pt));
                                assert(pt.inv_at(3, l2_dir_addr, l2_dir_ghost_pt));
                                pt.lemma_interp_at_facts(3, l2_dir_addr, l3_base_vaddr, l2_dir_ghost_pt);
                                let interp_l3_dir   = pt.interp_at(3, l2_dir_addr, l3_base_vaddr, l2_dir_ghost_pt);
                                let interp_l3_entry = pt.interp_at_entry(3, l2_dir_addr, l3_base_vaddr, l3_idx, l2_dir_ghost_pt);
                                interp_l3_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l3_idx);
                                match read_entry(mem, l2_dir_addr as nat, 3, l3_idx) {
                                    GhostPageDirectoryEntry::Page {
                                        addr: page_addr, flag_RW: l3_RW, flag_US: l3_US, flag_XD: l3_XD, ..
                                    } => {
                                        assert(aligned(addr as nat, L3_ENTRY_SIZE as nat));
                                        assert(pte == PageTableEntry {
                                            frame: MemRegion { base: page_addr as nat, size: L3_ENTRY_SIZE as nat },
                                            flags: Flags {
                                                is_writable:      l0_RW &&  l1_RW &&  l2_RW &&  l3_RW,
                                                is_supervisor:   !l0_US || !l1_US || !l2_US || !l3_US,
                                                disable_execute:  l0_XD ||  l1_XD ||  l2_XD ||  l3_XD
                                            }
                                        });

                                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64) | (l3_idx_u64 << 12u64))) by (bit_vector)
                                            requires
                                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                                addr % 4096 == 0;

                                        assert(add(add(add(
                                                mul(l0_idx_u64, mul(512u64, mul(512, mul(512, 4096)))),
                                                mul(l1_idx_u64, mul(512u64, mul(512, 4096)))),
                                                mul(l2_idx_u64, mul(512, 4096))),
                                                mul(l3_idx_u64, 4096))
                                               == l0_idx_u64 << 39u64 | l1_idx_u64 << 30u64 | l2_idx_u64 << 21u64 | l3_idx_u64 << 12u64) by (bit_vector)
                                            requires l0_idx_u64 < 512 && l1_idx_u64 < 512 && l2_idx_u64 < 512 && l3_idx_u64 < 512;
                                        // Previous assert proves:
                                        // l0_idx * L0_ENTRY_SIZE + l1_idx * L1_ENTRY_SIZE + l2_idx * L2_ENTRY_SIZE + l3_idx * L3_ENTRY_SIZE
                                        // == (l0_idx as u64) << 39u64 | (l1_idx as u64) << 30u64 | (l2_idx as u64) << 21u64 | (l3_idx as u64) << 12u64

                                        assert(interp_l3_dir.interp_of_entry(l3_idx).map.contains_pair(addr as nat, pte));
                                        assert(interp_l3_dir.interp().map.contains_pair(addr as nat, pte));
                                        assert(interp_l2_dir.interp().map.contains_pair(addr as nat, pte));
                                        assert(interp_l1_dir.interp().map.contains_pair(addr as nat, pte));
                                        interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_idx);
                                        assert(interp_l0_dir.interp().map.contains_pair(addr as nat, pte));
                                        assert(m1.contains_pair(addr as nat, pte));
                                    },
                                    GhostPageDirectoryEntry::Directory { .. } => assert(false),
                                    GhostPageDirectoryEntry::Empty => assert(false),
                                }
                            },
                            GhostPageDirectoryEntry::Empty => assert(false),
                        }
                    },
                    GhostPageDirectoryEntry::Empty => assert(false),
                }
            },
            _ => assert(false),
        };
    };
    assert forall|addr: nat| !m1.contains_key(addr) ==> !m2.contains_key(addr) by {
        pt.lemma_interp_at_facts(0, mem.cr3_spec().base, 0, pt.ghost_pt@);
        pt.interp().lemma_inv_implies_interp_inv();
        if addr < MAX_BASE && (exists|pte: PageTableEntry| valid_pt_walk(mem, nat_to_u64(addr), pte)) {
        } else {
            if addr >= MAX_BASE {
            } else {
                assert(addr < MAX_BASE);
                let addr: u64 = addr as u64;
                assert(!exists|pte: PageTableEntry| valid_pt_walk(mem, addr, pte)) by {
                    assert(!exists|pte: PageTableEntry| valid_pt_walk(mem, nat_to_u64(addr as nat), pte));
                };
                let l0_idx_u64:  u64 = l0_bits!(addr);
                let l0_idx:      nat = l0_idx_u64 as nat;
                let l1_idx_u64:  u64 = l1_bits!(addr);
                let l1_idx:      nat = l1_idx_u64 as nat;
                let l2_idx_u64:  u64 = l2_bits!(addr);
                let l2_idx:      nat = l2_idx_u64 as nat;
                let l3_idx_u64:  u64 = l3_bits!(addr);
                let l3_idx:      nat = l3_idx_u64 as nat;
                assert(forall|a:u64| (a & bitmask_inc!(0u64,8u64) == a) ==> a < 512) by (bit_vector);
                assert(l0_idx < 512 && l1_idx < 512 && l2_idx < 512 && l3_idx < 512) by {
                    assert(((addr & bitmask_inc!(12u64,20u64)) >> 12u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(12u64,20u64)) >> 12u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(21u64,29u64)) >> 21u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(21u64,29u64)) >> 21u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(30u64,38u64)) >> 30u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(30u64,38u64)) >> 30u64)) by (bit_vector);
                    assert(((addr & bitmask_inc!(39u64,47u64)) >> 39u64) & bitmask_inc!(0u64,8u64) == ((addr & bitmask_inc!(39u64,47u64)) >> 39u64)) by (bit_vector);
                };
                assert(bitmask_inc!(39u64,47u64) == 0xFF80_0000_0000) by (compute);
                assert(bitmask_inc!(30u64,38u64) == 0x007F_C000_0000) by (compute);
                assert(bitmask_inc!(21u64,29u64) == 0x0000_3FE0_0000) by (compute);
                assert(bitmask_inc!(12u64,20u64) == 0x0000_001F_F000) by (compute);
                let interp_l0_dir   = pt.interp();
                let interp_l0_entry = pt.interp_at_entry(0, mem.cr3_spec().base, 0, l0_idx, pt.ghost_pt@);
                interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_idx);
                match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
                    GhostPageDirectoryEntry::Directory {
                        addr: l0_dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
                    } => {
                        assert(interp_l0_entry.is_Directory());
                        let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                        let l1_upper_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx + 1);
                        let l0_dir_ghost_pt = pt.ghost_pt@.entries[l0_idx as int].get_Some_0();
                        assert(pt.directories_obey_invariant_at(0, mem.cr3_spec().base, pt.ghost_pt@));
                        assert(pt.inv_at(1, l0_dir_addr, l0_dir_ghost_pt));
                        pt.lemma_interp_at_facts(1, l0_dir_addr, l1_base_vaddr, l0_dir_ghost_pt);
                        let interp_l1_dir   = pt.interp_at(1, l0_dir_addr, l1_base_vaddr, l0_dir_ghost_pt);
                        let interp_l1_entry = pt.interp_at_entry(1, l0_dir_addr, l1_base_vaddr, l1_idx, l0_dir_ghost_pt);
                        interp_l1_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l1_idx);

                        let low_bits: u64 = addr % (L1_ENTRY_SIZE as u64);
                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + low_bits
                        assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | low_bits
                               == add(add(mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                          mul(l1_idx_u64, mul(512, mul(512, 4096)))),
                                          low_bits)) by (bit_vector)
                            requires
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                low_bits == addr % mul(512, mul(512, 4096));
                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | low_bits)) by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                low_bits == addr % mul(512, mul(512, 4096));
                        match read_entry(mem, l0_dir_addr as nat, 1, l1_idx) {
                            GhostPageDirectoryEntry::Page {
                                addr: page_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                            } => {
                                assert_by_contradiction!(!aligned(addr as nat, L1_ENTRY_SIZE as nat), {
                                    let pte = PageTableEntry {
                                        frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                                        flags: Flags {
                                            is_writable:      l0_RW &&  l1_RW,
                                            is_supervisor:   !l0_US || !l1_US,
                                            disable_execute:  l0_XD ||  l1_XD
                                        }
                                    };
                                    assert(valid_pt_walk(mem, addr as u64, pte));
                                });
                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                assert(!m2.contains_key(addr as nat));
                            }
                            GhostPageDirectoryEntry::Directory {
                                addr: l1_dir_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                            } => {
                                assert(interp_l1_entry.is_Directory());
                                let l2_base_vaddr = x86_arch_spec.entry_base(1, l1_base_vaddr, l1_idx);
                                let l1_dir_ghost_pt = l0_dir_ghost_pt.entries[l1_idx as int].get_Some_0();
                                assert(pt.directories_obey_invariant_at(1, l0_dir_addr, l0_dir_ghost_pt));
                                assert(pt.inv_at(2, l1_dir_addr, l1_dir_ghost_pt));
                                pt.lemma_interp_at_facts(2, l1_dir_addr, l2_base_vaddr, l1_dir_ghost_pt);
                                let interp_l2_dir   = pt.interp_at(2, l1_dir_addr, l2_base_vaddr, l1_dir_ghost_pt);
                                let interp_l2_entry = pt.interp_at_entry(2, l1_dir_addr, l2_base_vaddr, l2_idx, l1_dir_ghost_pt);
                                interp_l2_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l2_idx);

                                let low_bits: u64 = addr % (L2_ENTRY_SIZE as u64);
                                // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + l2_idx_u64 * L2_ENTRY_SIZE + low_bits
                                assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64) | low_bits
                                       == add(add(add(
                                              mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                              mul(l1_idx_u64, mul(512, mul(512, 4096)))),
                                              mul(l2_idx_u64, mul(512, 4096))),
                                              low_bits)) by (bit_vector)
                                    requires
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        low_bits == addr % mul(512, 4096);
                                assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64) | low_bits)) by (bit_vector)
                                    requires
                                        l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                        l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                        l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                        addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                        low_bits == addr % mul(512, 4096);
                                match read_entry(mem, l1_dir_addr as nat, 2, l2_idx) {
                                    GhostPageDirectoryEntry::Page {
                                        addr: page_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                                    } => {
                                        assert_by_contradiction!(!aligned(addr as nat, L2_ENTRY_SIZE as nat), {
                                            let pte = PageTableEntry {
                                                frame: MemRegion { base: page_addr as nat, size: L2_ENTRY_SIZE as nat },
                                                flags: Flags {
                                                    is_writable:      l0_RW &&  l1_RW &&  l2_RW,
                                                    is_supervisor:   !l0_US || !l1_US || !l2_US,
                                                    disable_execute:  l0_XD ||  l1_XD ||  l2_XD
                                                }
                                            };
                                            assert(valid_pt_walk(mem, addr as u64, pte));
                                        });
                                        assert(!interp_l2_dir.interp_of_entry(l2_idx).map.contains_key(addr as nat));
                                        assert(!interp_l2_dir.interp().map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                        assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                        assert(!m2.contains_key(addr as nat));
                                    },
                                    GhostPageDirectoryEntry::Directory {
                                        addr: l2_dir_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                                    } => {
                                        assert(interp_l2_entry.is_Directory());
                                        let l3_base_vaddr = x86_arch_spec.entry_base(2, l2_base_vaddr, l2_idx);
                                        let l2_dir_ghost_pt = l1_dir_ghost_pt.entries[l2_idx as int].get_Some_0();
                                        assert(pt.directories_obey_invariant_at(2, l1_dir_addr, l1_dir_ghost_pt));
                                        assert(pt.inv_at(3, l2_dir_addr, l2_dir_ghost_pt));
                                        pt.lemma_interp_at_facts(3, l2_dir_addr, l3_base_vaddr, l2_dir_ghost_pt);
                                        let interp_l3_dir   = pt.interp_at(3, l2_dir_addr, l3_base_vaddr, l2_dir_ghost_pt);
                                        let interp_l3_entry = pt.interp_at_entry(3, l2_dir_addr, l3_base_vaddr, l3_idx, l2_dir_ghost_pt);
                                        interp_l3_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l3_idx);

                                        let low_bits: u64 = addr % (L3_ENTRY_SIZE as u64);
                                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + l1_idx_u64 * L1_ENTRY_SIZE + l2_idx_u64 * L2_ENTRY_SIZE + l3_idx_u64 * L3_ENTRY_SIZE + low_bits
                                        assert((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64) | (l3_idx_u64 << 12u64) | low_bits
                                               == add(add(add(add(
                                                      mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                                      mul(l1_idx_u64, mul(512, mul(512, 4096)))),
                                                      mul(l2_idx_u64, mul(512, 4096))),
                                                      mul(l3_idx_u64, 4096)),
                                                      low_bits)) by (bit_vector)
                                            requires
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                low_bits == addr % 4096;
                                        assert(addr == ((l0_idx_u64 << 39u64) | (l1_idx_u64 << 30u64) | (l2_idx_u64 << 21u64) | (l3_idx_u64 << 12u64) | low_bits)) by (bit_vector)
                                            requires
                                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                                l1_idx_u64 == (addr & 0x007F_C000_0000) >> 30,
                                                l2_idx_u64 == (addr & 0x0000_3FE0_0000) >> 21,
                                                l3_idx_u64 == (addr & 0x0000_001F_F000) >> 12,
                                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                                low_bits == addr % 4096;
                                        match read_entry(mem, l2_dir_addr as nat, 3, l3_idx) {
                                            GhostPageDirectoryEntry::Page {
                                                addr: page_addr, flag_RW: l3_RW, flag_US: l3_US, flag_XD: l3_XD, ..
                                            } => {
                                                assert_by_contradiction!(!aligned(addr as nat, L3_ENTRY_SIZE as nat), {
                                                    let pte = PageTableEntry {
                                                        frame: MemRegion { base: page_addr as nat, size: L3_ENTRY_SIZE as nat },
                                                        flags: Flags {
                                                            is_writable:      l0_RW &&  l1_RW &&  l2_RW &&  l3_RW,
                                                            is_supervisor:   !l0_US || !l1_US || !l2_US || !l3_US,
                                                            disable_execute:  l0_XD ||  l1_XD ||  l2_XD ||  l3_XD
                                                        }
                                                    };
                                                    assert(valid_pt_walk(mem, addr as u64, pte));
                                                });
                                                assert(!interp_l3_dir.interp_of_entry(l3_idx).map.contains_key(addr as nat));
                                                assert(!interp_l3_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp_of_entry(l2_idx).map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                                assert(!m2.contains_key(addr as nat));
                                            },
                                            GhostPageDirectoryEntry::Directory { .. } => assert(false),
                                            GhostPageDirectoryEntry::Empty => {
                                                assert(!interp_l3_dir.interp_of_entry(l3_idx).map.contains_key(addr as nat));
                                                assert(!interp_l3_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp_of_entry(l2_idx).map.contains_key(addr as nat));
                                                assert(!interp_l2_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                                assert(!m2.contains_key(addr as nat));
                                            }
                                        }
                                    },
                                    GhostPageDirectoryEntry::Empty => {
                                        assert(!interp_l2_dir.interp_of_entry(l2_idx).map.contains_key(addr as nat));
                                        assert(!interp_l2_dir.interp().map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                        assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                        assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                        assert(!m2.contains_key(addr as nat));
                                    },
                                }
                            },
                            GhostPageDirectoryEntry::Empty => {
                                assert(!interp_l1_dir.interp_of_entry(l1_idx).map.contains_key(addr as nat));
                                assert(!interp_l1_dir.interp().map.contains_key(addr as nat));
                                assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                                assert(!m2.contains_key(addr as nat));
                            },
                        }
                    },
                    GhostPageDirectoryEntry::Page { .. } => assert(false),
                    GhostPageDirectoryEntry::Empty => {
                        let low_bits: u64 = addr % (L0_ENTRY_SIZE as u64);
                        // This assert proves: ... == l0_idx_u64 * L0_ENTRY_SIZE + low_bits
                        assert((l0_idx_u64 << 39u64) | low_bits
                               == add(mul(l0_idx_u64, mul(512, mul(512, mul(512, 4096)))),
                                      low_bits)) by (bit_vector)
                            requires
                                low_bits == addr % mul(512, mul(512, mul(512, 4096)));
                        assert(addr == ((l0_idx_u64 << 39u64) | low_bits)) by (bit_vector)
                            requires
                                l0_idx_u64 == (addr & 0xFF80_0000_0000) >> 39,
                                addr < mul(512u64, mul(512, mul(512, mul(512, 4096)))),
                                low_bits == addr % mul(512, mul(512, mul(512, 4096)));
                        assert(!interp_l0_dir.interp().map.contains_key(addr as nat));
                        assert(!m2.contains_key(addr as nat));
                    },
                };
            }
        }
    };
    assert(m1 =~= m2) by {
        assert forall|addr: nat| m1.dom().contains(addr) <==> m2.dom().contains(addr) by {
            assert(m1.dom().contains(addr) ==> m2.contains_pair(addr, m1[addr]));
            assert(m2.dom().contains(addr) ==> m1.contains_pair(addr, m2[addr]));
        };
        assert forall|addr: nat| #[trigger] m1.contains_key(addr) && m2.contains_key(addr) implies m1[addr] == m2[addr] by {
            assert(m1.contains_pair(addr, m1[addr]));
            assert(m2.contains_pair(addr, m1[addr]));
        };
    };
}


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
