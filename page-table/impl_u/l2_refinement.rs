use vstd::prelude::*;
use vstd::assert_by_contradiction;

use crate::definitions_t::{ Flags, x86_arch_spec, axiom_x86_arch_exec_spec, MAX_BASE, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, aligned, new_seq, bitmask_inc };
use crate::definitions_t::{ PageTableEntry, PageTableEntryExec, MemRegion};
use crate::spec_t::impl_spec;
use crate::spec_t::mem;
use crate::spec_t::hardware::{ interp_pt_mem, l0_bits, l1_bits, l2_bits, l3_bits, valid_pt_walk, read_entry, GhostPageDirectoryEntry, nat_to_u64 };

use crate::definitions_u::{ lemma_new_seq, x86_arch_inv };
use crate::impl_u::l1;
use crate::impl_u::l2_impl::{ PT, PTDir };

verus! {

pub proof fn lemma_page_table_walk_interp()
    ensures
        forall|mem: mem::PageTableMemory, pt: PTDir| #![auto] PT::inv(&mem, pt) && PT::interp(&mem, pt).inv() ==> PT::interp(&mem, pt).interp().map === interp_pt_mem(mem)
{
    assert forall|mem: mem::PageTableMemory, pt: PTDir| #![auto]
        PT::inv(&mem, pt) && PT::interp(&mem, pt).inv() implies PT::interp(&mem, pt).interp().map === interp_pt_mem(mem)
    by {
        let m1 = interp_pt_mem(mem);
        let m2 = PT::interp(&mem, pt).interp().map;
        PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
        assert(PT::interp(&mem, pt).interp().inv());
        lemma_page_table_walk_interp_aux_1(mem, pt);
        lemma_page_table_walk_interp_aux_2(mem, pt);
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
    };
}

pub proof fn lemma_page_table_walk_interp_aux_1(mem: mem::PageTableMemory, pt: PTDir)
    requires PT::inv(&mem, pt) && PT::interp(&mem, pt).inv()
    ensures
        forall|k, v| interp_pt_mem(mem).contains_pair(k, v)
            ==> #[trigger] PT::interp(&mem, pt).interp().map.contains_pair(k, v)
{
    let m1 = interp_pt_mem(mem);
    let m2 = PT::interp(&mem, pt).interp().map;
    PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
    assert(PT::interp(&mem, pt).interp().inv());
    assert forall|addr: nat, pte: PageTableEntry|
        m1.contains_pair(addr, pte) implies #[trigger] m2.contains_pair(addr, pte)
    by {
        assert(addr == addr as u64);
        let addr: u64 = addr as u64;
        assert(addr < MAX_BASE);
        let pte = choose|pte: PageTableEntry| valid_pt_walk(mem, addr, pte);
        assert(valid_pt_walk(mem, addr as u64, pte));
        PT::lemma_interp_at_facts(&mem, pt, 0, mem.cr3_spec().base, 0);

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
        let interp_l0_dir   = PT::interp(&mem, pt);
        let interp_l0_entry = PT::interp_at_entry(&mem, pt, 0, mem.cr3_spec().base, 0, l0_idx);
        interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_idx);
        match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
            GhostPageDirectoryEntry::Directory {
                addr: l0_dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
            } => {
                assert(interp_l0_entry.is_Directory());
                let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                let l0_dir_ghost_pt = pt.entries[l0_idx as int].get_Some_0();
                assert(PT::directories_obey_invariant_at(&mem, pt, 0, mem.cr3_spec().base));
                assert(PT::inv_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                assert(interp_l0_dir.directories_obey_invariant());
                assert(interp_l0_dir.entries[l0_idx as int].get_Directory_0().inv());
                PT::lemma_interp_at_facts(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr);
                let interp_l1_dir   = PT::interp_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr);
                let interp_l1_entry = PT::interp_at_entry(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr, l1_idx);
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

                        assert(interp_l1_dir.interp_of_entry(l1_idx).map.contains_pair(addr as nat, pte)); // unstable
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
                        assert(PT::directories_obey_invariant_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                        assert(PT::inv_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                        PT::lemma_interp_at_facts(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr);
                        let interp_l2_dir   = PT::interp_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr);
                        let interp_l2_entry = PT::interp_at_entry(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr, l2_idx);
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
                                assert(PT::directories_obey_invariant_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                                assert(PT::inv_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr));
                                PT::lemma_interp_at_facts(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr);
                                let interp_l3_dir   = PT::interp_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr);
                                let interp_l3_entry = PT::interp_at_entry(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr, l3_idx);
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
}

pub proof fn lemma_page_table_walk_interp_aux_2(mem: mem::PageTableMemory, pt: PTDir)
    requires PT::inv(&mem, pt) && PT::interp(&mem, pt).inv()
    ensures
        forall|k| !interp_pt_mem(mem).contains_key(k)
            ==> !(#[trigger] PT::interp(&mem, pt).interp().map.contains_key(k))
{
    let m1 = interp_pt_mem(mem);
    let m2 = PT::interp(&mem, pt).interp().map;
    PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
    assert(PT::interp(&mem, pt).interp().inv());
    assert forall|addr: nat| !m1.contains_key(addr) ==> !m2.contains_key(addr) by {
        PT::lemma_interp_at_facts(&mem, pt, 0, mem.cr3_spec().base, 0);
        PT::interp(&mem, pt).lemma_inv_implies_interp_inv();
        if addr < MAX_BASE && (exists|pte: PageTableEntry| valid_pt_walk(mem, nat_to_u64(addr), pte)) {
        } else {
            if addr >= MAX_BASE {
            } else {
                assert(addr < MAX_BASE);
                // Not all of these assertions may be necessary but the assertion after the `let
                // addr` was unstable and seems okay now, so I'm not touching these.
                assert(addr == addr as u64);
                assert(nat_to_u64(addr) == addr);
                assert(!exists|pte: PageTableEntry| valid_pt_walk(mem, nat_to_u64(addr), pte));
                let addr: u64 = addr as u64;
                assert(!exists|pte: PageTableEntry| valid_pt_walk(mem, addr, pte));
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
                let interp_l0_dir   = PT::interp(&mem, pt);
                let interp_l0_entry = PT::interp_at_entry(&mem, pt, 0, mem.cr3_spec().base, 0, l0_idx);
                interp_l0_dir.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(l0_idx);
                match read_entry(mem, mem.cr3_spec()@.base, 0, l0_idx) {
                    GhostPageDirectoryEntry::Directory {
                        addr: l0_dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
                    } => {
                        assert(interp_l0_entry.is_Directory());
                        let l1_base_vaddr = x86_arch_spec.entry_base(0, 0, l0_idx);
                        let l0_dir_ghost_pt = pt.entries[l0_idx as int].get_Some_0();
                        assert(PT::directories_obey_invariant_at(&mem, pt, 0, mem.cr3_spec().base));
                        assert(PT::inv_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                        assert(interp_l0_dir.directories_obey_invariant());
                        assert(interp_l0_dir.entries[l0_idx as int].get_Directory_0().inv());
                        PT::lemma_interp_at_facts(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr);
                        let interp_l1_dir   = PT::interp_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr);
                        let interp_l1_entry = PT::interp_at_entry(&mem, l0_dir_ghost_pt, 1, l0_dir_addr, l1_base_vaddr, l1_idx);
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
                                assert(PT::directories_obey_invariant_at(&mem, l0_dir_ghost_pt, 1, l0_dir_addr));
                                assert(PT::inv_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                                PT::lemma_interp_at_facts(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr);
                                let interp_l2_dir   = PT::interp_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr);
                                let interp_l2_entry = PT::interp_at_entry(&mem, l1_dir_ghost_pt, 2, l1_dir_addr, l2_base_vaddr, l2_idx);
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
                                        assert(PT::directories_obey_invariant_at(&mem, l1_dir_ghost_pt, 2, l1_dir_addr));
                                        assert(PT::inv_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr));
                                        PT::lemma_interp_at_facts(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr);
                                        let interp_l3_dir   = PT::interp_at(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr);
                                        let interp_l3_entry = PT::interp_at_entry(&mem, l2_dir_ghost_pt, 3, l2_dir_addr, l3_base_vaddr, l3_idx);
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
}

proof fn lemma_no_entries_implies_interp_at_aux_no_entries(mem: mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>)
    requires
        mem.regions() == set![mem.cr3_spec()@],
        (forall|i: nat| i < 512 ==> mem.region_view(mem.cr3_spec()@)[i as int] == 0),
        layer == 0,
        PT::inv_at(&mem, pt, layer, ptr),
        forall|i: nat| i < init.len() ==> init[i as int] == l1::NodeEntry::Empty(),
        init.len() <= 512,
    ensures
        ({ let res = PT::interp_at_aux(&mem, pt, layer, ptr, base_vaddr, init);
            &&& res.len() == 512
            &&& forall|i: nat| i < res.len() ==> res[i as int] == l1::NodeEntry::Empty()
        })
    decreases 512 - init.len()
{
    lemma_new_seq::<Option<PTDir>>(512, Option::None);
    let res = PT::interp_at_aux(&mem, pt, layer, ptr, base_vaddr, init);
    if init.len() >= 512 {
    } else {
        let entry = PT::interp_at_entry(&mem, pt, layer, ptr, base_vaddr, init.len());
        assert(PT::ghost_pt_matches_structure(&mem, pt, layer, ptr));
        assert forall|i: nat| i < 512 implies PT::view_at(&mem, pt, layer, ptr, i).is_Empty() by {
            let entry = mem.spec_read(i, pt.region);
            assert((entry & (1u64 << 0)) != (1u64 << 0)) by (bit_vector) requires entry == 0u64;
        };
        assert(entry == l1::NodeEntry::Empty());
        lemma_no_entries_implies_interp_at_aux_no_entries(mem, pt, layer, ptr, base_vaddr, init.push(entry));
    }
}

impl impl_spec::InterfaceSpec for impl_spec::PageTableImpl {
    closed spec fn ispec_inv(&self, mem: &mem::PageTableMemory) -> bool {
        exists|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv()
    }

    proof fn ispec_init_implies_inv(&self, mem: &mem::PageTableMemory) {
        let pt = PTDir {
            region: mem.cr3_spec()@,
            entries: new_seq(512, Option::None),
            used_regions: set![mem.cr3_spec()@],
        };
        lemma_new_seq::<Option<PTDir>>(512, Option::None);
        assert(PT::inv(mem, pt)) by {
            x86_arch_inv();
            axiom_x86_arch_exec_spec();
            PT::lemma_zeroed_page_implies_empty_at(mem, pt, 0, mem.cr3_spec().base);
        };
        lemma_no_entries_implies_interp_at_aux_no_entries(*mem, pt, 0, mem.cr3_spec().base, 0, seq![]);
        assert(aligned(PT::interp(mem, pt).base_vaddr, PT::interp(mem, pt).entry_size() * PT::interp(mem, pt).num_entries())) by {
            assert(PT::interp(mem, pt).base_vaddr == 0);
            assert(forall|x: nat| x != 0 ==> #[trigger] aligned(0, x));
            assert(forall|x: nat| x != 0 ==> aligned(PT::interp(mem, pt).base_vaddr, x));
            let x = PT::interp(mem, pt).entry_size() * PT::interp(mem, pt).num_entries();
            assert(x != 0);
            assert(aligned(PT::interp(mem, pt).base_vaddr, x));
        };
        assert(PT::interp(mem, pt).inv());
    }

    fn ispec_map_frame(&self, mem: &mut mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: Result<(),()>) {
        let mut pt: Ghost<PTDir> = Ghost(choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv());
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH) by (compute_only);
            lemma_page_table_walk_interp();
        }
        PT::map_frame(mem, &mut pt, vaddr, pte)
    }

    fn ispec_unmap(&self, mem: &mut mem::PageTableMemory, vaddr: usize) -> (res: Result<(),()>) {
        let mut pt: Ghost<PTDir> = Ghost(choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv());
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH) by (compute_only);
            lemma_page_table_walk_interp();
        }
        PT::unmap(mem, &mut pt, vaddr)
    }

    fn ispec_resolve(&self, mem: &mem::PageTableMemory, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec),()>) {
        let pt: Ghost<PTDir> = Ghost(choose|pt: PTDir| #[trigger] PT::inv(mem, pt) && PT::interp(mem, pt).inv());
        proof {
            PT::lemma_interp_at_facts(mem, pt@, 0, mem.cr3_spec().base, 0);
            PT::interp(mem, pt@).lemma_inv_implies_interp_inv();
            assert(x86_arch_spec.upper_vaddr(0, 0) == crate::definitions_t::PT_BOUND_HIGH) by (compute_only);
            lemma_page_table_walk_interp();
        }
        match PT::resolve(mem, pt, vaddr) {
            Ok((v,pte)) => Ok((v,pte)),
            Err(e)      => Err(e),
        }
    }
}

}
