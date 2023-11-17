#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::modes::*;
use vstd::seq::*;
use vstd::map::*;
use vstd::set::*;
use vstd::set_lib::*;
use vstd::seq_lib::*;
use vstd::assert_by_contradiction;

use crate::definitions_t::{ MemRegion, MemRegionExec, PageTableEntry, PageTableEntryExec, Flags, overlap, between, aligned, new_seq, MapResult, UnmapResult, candidate_mapping_in_bounds, x86_arch_exec, x86_arch_spec, x86_arch_exec_spec, axiom_max_phyaddr_width_facts, Arch, ArchExec, };
use crate::definitions_u::{ lemma_maxphyaddr_facts, lemma_new_seq, aligned_exec, permissive_flags};
use crate::definitions_t::{ MAX_BASE, WORD_SIZE, PAGE_SIZE, MAX_PHYADDR, MAX_PHYADDR_WIDTH, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, X86_NUM_LAYERS, X86_NUM_ENTRIES };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::spec_t::mem;
use crate::spec_t::mem::{ word_index_spec };
use crate::impl_u::indexing;
use crate::extra as lib;
use crate::spec_t::hardware::{PageDirectoryEntry,GhostPageDirectoryEntry};
use crate::spec_t::hardware::{MASK_FLAG_P, MASK_FLAG_RW, MASK_FLAG_US, MASK_FLAG_PWT, MASK_FLAG_PCD,
MASK_FLAG_A, MASK_FLAG_XD, MASK_ADDR, MASK_PG_FLAG_D, MASK_PG_FLAG_G, MASK_PG_FLAG_PAT,
MASK_L1_PG_FLAG_PS, MASK_L2_PG_FLAG_PS, MASK_L3_PG_FLAG_PAT, MASK_DIR_ADDR, MASK_L1_PG_ADDR,
MASK_L2_PG_ADDR, MASK_L3_PG_ADDR};

verus! {

macro_rules! bit {
    ($v:expr) => {
        1u64 << $v
    }
}
// Generate bitmask where bits $low:$high are set to 1. (inclusive on both ends)
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0u64 << (($high+1u64)-$low))) << $low
    }
}
// macro_rules! bitmask {
//     ($low:expr,$high:expr) => {
//         (!(!0 << ($high-$low))) << $low
//     }
// }


proof fn lemma_page_aligned_implies_mask_dir_addr_is_identity()
    ensures forall|addr: u64| addr <= MAX_PHYADDR ==> #[trigger] aligned(addr as nat, PAGE_SIZE as nat) ==> addr & MASK_DIR_ADDR == addr,
{
    assert forall|addr: u64|
        addr <= MAX_PHYADDR &&
        #[trigger] aligned(addr as nat, PAGE_SIZE as nat)
        implies
        addr & MASK_DIR_ADDR == addr
    by {
        let max_width: u64 = MAX_PHYADDR_WIDTH;
        let mask_dir_addr: u64 = MASK_DIR_ADDR;
        assert(addr & mask_dir_addr == addr) by (bit_vector)
            requires
                addr <= sub(1u64 << max_width, 1u64),
                addr % 4096u64 == 0,
                mask_dir_addr == bitmask_inc!(12u64, max_width - 1);
    };
}

proof fn lemma_aligned_addr_mask_facts(addr: u64)
    ensures
        aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr & MASK_ADDR),
        aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr & MASK_ADDR),
        (addr & MASK_L3_PG_ADDR == addr & MASK_ADDR),
        addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
{
    axiom_max_phyaddr_width_facts();
    assert(aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr & MASK_ADDR)) by {
        if aligned(addr as nat, L1_ENTRY_SIZE as nat) {
            let max_width: u64 = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(30u64, max_width - 1) == addr & bitmask_inc!(12u64, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x40000000u64 == 0,
                    32 <= max_width;
        }
    };
    assert(aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr & MASK_ADDR)) by {
        if aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            let max_width: u64 = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(21u64, max_width - 1) == addr & bitmask_inc!(12u64, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x200000u64 == 0,
                    32 <= max_width;
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) {
            assert(aligned(L1_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by(nonlinear_arith);
            lib::aligned_transitive(addr as nat, L1_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            assert(aligned(L2_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by(nonlinear_arith);
            lib::aligned_transitive(addr as nat, L2_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) {
            assert(aligned(L3_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by(nonlinear_arith);
            lib::aligned_transitive(addr as nat, L3_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
}

pub open spec fn addr_is_zero_padded(layer: nat, addr: u64, is_page: bool) -> bool {
    is_page ==> {
        if layer == 1 {
            addr & MASK_L1_PG_ADDR == addr
        } else if layer == 2 {
            addr & MASK_L2_PG_ADDR == addr
        } else if layer == 3 {
            addr & MASK_L3_PG_ADDR == addr
        } else {
            arbitrary()
        }
    }
}

// PageDirectoryEntry is defined in crate::spec_t::hardware to define the page table walk
// semantics. Here we reuse it for the implementation and add exec functions to it.
impl PageDirectoryEntry {
    pub open spec fn can_use_generic_addr_mask(self) -> bool {
        self@.is_Page() ==>
            if self.layer == 1 {
                self.entry & MASK_L1_PG_ADDR == self.entry & MASK_ADDR
            } else if self.layer == 2 {
                self.entry & MASK_L2_PG_ADDR == self.entry & MASK_ADDR
            } else { true }
    }

    pub proof fn lemma_zero_entry_facts(self)
        requires
            self.entry == 0,
            self.layer@ <= 3,
        ensures
            self@.is_Empty(),
            self.all_mb0_bits_are_zero(),
    {
        assert(forall|a: u64| 0 & a == 0) by (bit_vector);
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        assert(1u64 << 0 == 1) by (bit_vector);
        assert(0u64 & 1 == 0) by (bit_vector);
    }

    pub proof fn lemma_new_entry_mb0_bits_are_zero(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        )
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({ let e = address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS } else { 0 }
                | if is_writable           { MASK_FLAG_RW }       else { 0 }
                | if is_supervisor         { 0 }                  else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }      else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }      else { 0 }
                | if disable_execute       { MASK_FLAG_XD }       else { 0 };
               (PageDirectoryEntry { entry: e, layer: Ghost(layer as nat) }).all_mb0_bits_are_zero()
            }),
    {
        let or1 = MASK_FLAG_P;
        let a1 = address | or1;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS as u64 } else { 0 };
        let a2 = a1 | or2;
        let or3 = if is_writable           { MASK_FLAG_RW as u64 }       else { 0 };
        let a3 = a2 | or3;
        let or4 = if is_supervisor         { 0 }                         else { MASK_FLAG_US as u64 };
        let a4 = a3 | or4;
        let or5 = if is_writethrough       { MASK_FLAG_PWT as u64 }      else { 0 };
        let a5 = a4 | or5;
        let or6 = if disable_cache         { MASK_FLAG_PCD as u64 }      else { 0 };
        let a6 = a5 | or6;
        let or7 = if disable_execute       { MASK_FLAG_XD as u64 }       else { 0 };
        let a7 = a6 | or7;
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: u64 = MAX_PHYADDR_WIDTH;
        assert(forall|a:u64| #![auto] a == a | 0) by (bit_vector);

        axiom_max_phyaddr_width_facts();
        assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(12u64,sub(mw,1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i != 7 && (a & bit!(7u64) == 0) ==> (a | bit!(i)) & bit!(7u64) == 0) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i < 13 && (a & bitmask_inc!(13u64,29u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13u64,29u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i > 29 && (a & bitmask_inc!(13u64,29u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13u64,29u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i < 13 && (a & bitmask_inc!(13u64,20u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13u64,20u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i > 20 && (a & bitmask_inc!(13u64,20u64) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13u64,20u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i < mw && (a & bitmask_inc!(mw,51u64)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i > 51 && (a & bitmask_inc!(mw,51u64)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51u64) == 0)) by (bit_vector)
            requires mw <= 52;
        assert(address & bitmask_inc!(mw, 51) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12u64, mw - 1) == address,
                32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i < mw && (a & bitmask_inc!(mw,62u64)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62u64) == 0)) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i > 62 && (a & bitmask_inc!(mw,62u64)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62u64) == 0)) by (bit_vector)
            requires mw <= 52;
        assert(address & bitmask_inc!(mw, 62) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12u64, mw - 1) == address,
                32 <= mw <= 52;
        PageDirectoryEntry::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
        if layer == 0 {
            assert(!is_page);
            assert(e & bit!(7u64) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
        } else if layer == 1 {
            if is_page {
                assert(address & bitmask_inc!(30u64,sub(mw,1)) == address ==> address & bitmask_inc!(13u64,29u64) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13u64,29u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            } else {
                assert(e & bit!(7u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            }
        } else if layer == 2 {
            if is_page {
                assert(address & bitmask_inc!(21u64,sub(mw,1)) == address ==> address & bitmask_inc!(13u64,20u64) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13u64,20u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            } else {
                assert(e & bit!(7u64) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            }
        } else if layer == 3 {
            assert(is_page);
            // assert(e & bit!(7u64) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
        } else { assert(false); }

        let pde = PageDirectoryEntry { entry: e, layer: Ghost(layer as nat) };
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        assert(pde.all_mb0_bits_are_zero());
    }


    pub proof fn lemma_new_entry_addr_mask_is_address(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        )
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            ({ let e = address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { 0 }                   else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 };
               &&& e & MASK_ADDR == address
               &&& e & MASK_FLAG_P == MASK_FLAG_P
               &&& (e & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3)
               &&& (e & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable
               &&& (e & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor
               &&& (e & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough
               &&& (e & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache
               &&& (e & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute
               &&& (is_page && layer == 1 ==> e & MASK_L1_PG_ADDR == e & MASK_ADDR)
               &&& (is_page && layer == 2 ==> e & MASK_L2_PG_ADDR == e & MASK_ADDR)
            }),
    {
        let or1 = MASK_FLAG_P;
        let a1 = address | or1;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS as u64 }  else { 0 };
        let a2 = a1 | or2;
        let or3 = if is_writable           { MASK_FLAG_RW as u64 }        else { 0 };
        let a3 = a2 | or3;
        let or4 = if is_supervisor         { 0 }                          else { MASK_FLAG_US as u64 };
        let a4 = a3 | or4;
        let or5 = if is_writethrough       { MASK_FLAG_PWT as u64 }       else { 0 };
        let a5 = a4 | or5;
        let or6 = if disable_cache         { MASK_FLAG_PCD as u64 }       else { 0 };
        let a6 = a5 | or6;
        let or7 = if disable_execute       { MASK_FLAG_XD as u64 }        else { 0 };
        let a7 = a6 | or7;
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: u64 = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        assert(forall|a:u64,x:u64| x < 64 && (a & bit!(x) == 0) ==> a & bit!(x) != bit!(x)) by (bit_vector);
        assert(forall|a:u64| #![auto] a == a | 0) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(e & MASK_ADDR == address);

        assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i < 64 ==> a & bit!(i) == 0 ==> (a | bit!(i)) & bit!(i) == bit!(i)) by (bit_vector);
        assert(forall|a:u64,i:u64,j:u64| #![auto] i != j ==> a & bit!(i) == (a | bit!(j)) & bit!(i)) by (bit_vector);

        assert(e & MASK_FLAG_P == MASK_FLAG_P);
        assert((e & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3));
        assert((e & MASK_FLAG_RW       == MASK_FLAG_RW)       == is_writable);
        assert((e & MASK_FLAG_US       == MASK_FLAG_US)       == !is_supervisor);
        assert((e & MASK_FLAG_PWT      == MASK_FLAG_PWT)      == is_writethrough);
        assert((e & MASK_FLAG_PCD      == MASK_FLAG_PCD)      == disable_cache);
        assert((e & MASK_FLAG_XD       == MASK_FLAG_XD)       == disable_execute);

        assert({
            &&& is_page && layer == 1 ==> e & MASK_L1_PG_ADDR == e & MASK_ADDR
            &&& is_page && layer == 2 ==> e & MASK_L2_PG_ADDR == e & MASK_ADDR
        }) by {
            assert(forall|a:u64| #![auto] a & bitmask_inc!(30u64,sub(mw,1)) == (a | 0)           & bitmask_inc!(30u64,sub(mw,1))) by (bit_vector);
            assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(30u64,sub(mw,1)) == (a | bit!(i))  & bitmask_inc!(30u64,sub(mw,1))) by (bit_vector);
            assert(forall|a:u64,i:u64| #![auto] i > 52 ==> a & bitmask_inc!(30u64,sub(mw,1)) == (a | bit!(i))  & bitmask_inc!(30u64,sub(mw,1))) by (bit_vector)
                requires 32 <= mw <= 52;
            assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(21u64,sub(mw,1)) == (a | bit!(i))  & bitmask_inc!(21u64,sub(mw,1))) by (bit_vector)
                requires 32 <= mw <= 52;
            assert(forall|a:u64,i:u64| #![auto] i > 52 ==> a & bitmask_inc!(21u64,sub(mw,1)) == (a | bit!(i))  & bitmask_inc!(21u64,sub(mw,1))) by (bit_vector)
                requires 32 <= mw <= 52;
        };
    }

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer as nat, pte.frame.base as u64, true),
            pte.frame.base as u64 & MASK_ADDR == pte.frame.base as u64,
        ensures
            r.all_mb0_bits_are_zero(),
            r.can_use_generic_addr_mask(),
            r@.is_Page(),
            r.layer@ == layer,
            r@.get_Page_addr() == pte.frame.base,
            r.entry & MASK_ADDR == pte.frame.base,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            (r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (layer != 3),
            (r.entry & MASK_FLAG_RW == MASK_FLAG_RW) == pte.flags.is_writable,
            r@.get_Page_flag_RW() == pte.flags.is_writable,
            (r.entry & MASK_FLAG_US == MASK_FLAG_US) == !pte.flags.is_supervisor,
            r@.get_Page_flag_US() == !pte.flags.is_supervisor,
            r.entry & MASK_FLAG_PWT != MASK_FLAG_PWT,
            r.entry & MASK_FLAG_PCD != MASK_FLAG_PCD,
            (r.entry & MASK_FLAG_XD == MASK_FLAG_XD) == pte.flags.disable_execute,
            r@.get_Page_flag_XD() == pte.flags.disable_execute,
    {
        Self::new_entry(layer, pte.frame.base as u64, true, pte.flags.is_writable, pte.flags.is_supervisor, false, false, pte.flags.disable_execute)
    }

    pub fn new_dir_entry(layer: usize, address: u64) -> (r: Self)
        requires
            layer < 3,
            address & MASK_DIR_ADDR == address
        ensures
            r.all_mb0_bits_are_zero(),
            r.can_use_generic_addr_mask(),
            r@.is_Directory(),
            r.layer@ == layer,
            r@.get_Directory_addr() == address,
            r@.get_Directory_flag_RW(),
            r@.get_Directory_flag_US(),
            !r@.get_Directory_flag_XD(),
    {
        Self::new_entry(
            layer,
            address,
            false, // is_page
            true,  // is_writable
            false, // is_supervisor
            false, // is_writethrough
            false, // disable_cache
            false) // disable_execute
    }

    pub fn new_entry(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> (r: PageDirectoryEntry)
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            r.all_mb0_bits_are_zero(),
            if is_page { r@.is_Page() && r@.get_Page_addr() == address } else { r@.is_Directory() && r@.get_Directory_addr() == address},
            r.can_use_generic_addr_mask(),
            r.layer@ == layer,
            r.entry & MASK_ADDR == address,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            (r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3),
            (r.entry & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable,
            (r.entry & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor,
            (r.entry & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough,
            (r.entry & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache,
            (r.entry & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute,
    {
        let e =
        PageDirectoryEntry {
            entry: {
                address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { 0 }                   else { MASK_FLAG_US }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 }
            },
            layer: Ghost(layer as nat),
        };

        proof {
            PageDirectoryEntry::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            PageDirectoryEntry::lemma_new_entry_mb0_bits_are_zero(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            assert(e.layer() <= 3);
            assert(e@.is_Page() ==> 0 < e.layer());
            assert(e.can_use_generic_addr_mask());
        }
        e
    }

    pub fn flags(&self) -> (res: Flags)
        requires
            self.layer() <= 3,
            self@.is_Page()
        ensures
            res.is_writable     <==> self.entry & MASK_FLAG_RW == MASK_FLAG_RW,
            res.is_supervisor   <==> self.entry & MASK_FLAG_US != MASK_FLAG_US,
            res.disable_execute <==> self.entry & MASK_FLAG_XD == MASK_FLAG_XD,
    {
        Flags {
            is_writable:     self.entry & MASK_FLAG_RW == MASK_FLAG_RW,
            is_supervisor:   self.entry & MASK_FLAG_US != MASK_FLAG_US,
            disable_execute: self.entry & MASK_FLAG_XD == MASK_FLAG_XD,
        }
    }

    pub fn address(&self) -> (res: u64)
        requires
            self.layer() <= 3,
            self@.is_Page() ==> 0 < self.layer(),
            self.can_use_generic_addr_mask(),
            !self@.is_Empty(),
        ensures
            res as usize == match self@ {
                GhostPageDirectoryEntry::Page { addr, .. }      => addr,
                GhostPageDirectoryEntry::Directory { addr, .. } => addr,
                GhostPageDirectoryEntry::Empty                  => arbitrary(),
            }
    {
        proof {
            match self@ {
                GhostPageDirectoryEntry::Page { addr, .. }      => {
                    if self.layer() == 1 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else if self.layer() == 2 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else if self.layer() == 3 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else {
                        assert(false);
                    }
                },
                GhostPageDirectoryEntry::Directory { addr, .. } => assert(addr == self.entry & MASK_ADDR),
                GhostPageDirectoryEntry::Empty                  => (),
            }
        }
        self.entry & MASK_ADDR
    }

    pub fn is_mapping(&self) -> (r: bool)
        requires
            self.all_mb0_bits_are_zero(),
            self.layer() <= 3
        ensures
            r == !self@.is_Empty(),
    {
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r { self@.is_Page() } else { self@.is_Directory() },
    {
        if layer == 3 {
            true
        } else if layer == 0 {
            false
        } else {
            (self.entry & MASK_L1_PG_FLAG_PS) == MASK_L1_PG_FLAG_PS
        }
    }

    pub fn is_dir(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r { self@.is_Directory() } else { self@.is_Page() },
    {
        !self.is_page(layer)
    }
}

/// PTDir is used in the `ghost_pt` field of the PageTable. It's used to keep track of the memory
/// regions in which the corresponding translation structures are stored.
pub struct PTDir {
    /// Region of physical memory in which this PTDir is stored
    pub region: MemRegion,
    pub entries: Seq<Option<PTDir>>,
    /// reflexive-transitive closure of `region` over `entries`
    pub used_regions: Set<MemRegion>,
}

pub struct PageTable {
    pub memory: mem::PageTableMemory,
    pub ghost_pt: Ghost<PTDir>,
}

impl PageTable {
    pub open spec(checked) fn well_formed(self, ptr: usize) -> bool {
        &&& x86_arch_spec.inv()
        // Make sure each page directory fits in one page:
        &&& forall|layer: nat| layer < X86_NUM_LAYERS ==> x86_arch_spec.num_entries(layer) == 512
    }

    pub open spec(checked) fn inv(&self) -> bool {
        let cr3 = self.memory.cr3_spec();
        &&& self.ghost_pt@.region === cr3@
        &&& self.inv_at(0, cr3.base, self.ghost_pt@)
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn entry_at_spec(self, layer: nat, ptr: usize, i: nat, pt: PTDir) -> PageDirectoryEntry {
        PageDirectoryEntry {
            entry: self.memory.spec_read(i, pt.region),
            layer: Ghost(layer),
        }
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn view_at(self, layer: nat, ptr: usize, i: nat, pt: PTDir) -> GhostPageDirectoryEntry {
        PageDirectoryEntry {
            entry: self.memory.spec_read(i, pt.region),
            layer: Ghost(layer),
        }@
    }

    /// Get the entry at address ptr + i * WORD_SIZE
    fn entry_at(&self, layer: usize, ptr: usize, i: usize, pt: Ghost<PTDir>) -> (res: PageDirectoryEntry)
        requires
            i < 512,
            self.inv_at(layer as nat, ptr, pt@),
        ensures
            res.layer@ == layer as nat,
            res@ === self.view_at(layer as nat, ptr, i as nat, pt@),
            res == self.entry_at_spec(layer as nat, ptr, i as nat, pt@),
            res.can_use_generic_addr_mask(),
            (res@.is_Page() ==> 0 < res.layer()),
    {
        assert(aligned((ptr + i * WORD_SIZE) as nat, 8)) by {
            assert(self.inv_at(layer as nat, ptr, pt@));
            assert(self.well_formed(ptr));
            assert(ptr % PAGE_SIZE == 0);
        };
        // triggering
        proof { let x = self.entry_at_spec(layer as nat, ptr, i as nat, pt@); }
        PageDirectoryEntry {
            entry: self.memory.read(ptr, i, Ghost(pt@.region)),
            layer: Ghost(layer as nat),
        }
    }

    pub open spec fn ghost_pt_matches_structure(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| #![trigger pt.entries[i as int], self.view_at(layer, ptr, i, pt)]
        i < X86_NUM_ENTRIES ==> {
            let entry = self.view_at(layer, ptr, i, pt);
            entry.is_Directory() == pt.entries[i as int].is_Some()
        }
    }

    pub open spec fn directories_obey_invariant_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        decreases X86_NUM_LAYERS - layer, 0nat
    {
        decreases_when(self.well_formed(ptr) && self.layer_in_range(layer));
        forall|i: nat| i < X86_NUM_ENTRIES ==> {
            let entry = #[trigger] self.view_at(layer, ptr, i, pt);
            entry.is_Directory() ==> {
                &&& self.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0())
            }
        }
    }

    pub open spec fn empty_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        recommends self.well_formed(ptr)
    {
        forall|i: nat| i < X86_NUM_ENTRIES ==> self.view_at(layer, ptr, i, pt).is_Empty()
    }

    pub open spec(checked) fn layer_in_range(self, layer: nat) -> bool {
        layer < X86_NUM_LAYERS
    }

    pub open spec(checked) fn inv_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        decreases X86_NUM_LAYERS - layer
    {
        &&& ptr % PAGE_SIZE == 0
        &&& self.well_formed(ptr)
        &&& self.memory.inv()
        &&& self.memory.regions().contains(pt.region)
        &&& pt.region.base == ptr
        &&& pt.region.size == PAGE_SIZE
        &&& self.memory.region_view(pt.region).len() == pt.entries.len()
        &&& self.layer_in_range(layer)
        &&& pt.entries.len() == X86_NUM_ENTRIES
        &&& self.directories_obey_invariant_at(layer, ptr, pt)
        &&& self.directories_have_flags(layer, ptr, pt)
        &&& self.ghost_pt_matches_structure(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_rtrancl(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt)
        &&& self.ghost_pt_region_notin_used_regions(layer, ptr, pt)
        &&& pt.used_regions.subset_of(self.memory.regions())
        &&& self.entry_addrs_can_use_generic_addr_mask(layer, ptr, pt)
        &&& self.entry_mb0_bits_are_zero(layer, ptr, pt)
    }

    pub open spec fn directories_have_flags(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| i < X86_NUM_ENTRIES ==> {
            let entry = #[trigger] self.view_at(layer, ptr, i, pt);
            entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
        }
    }

    pub open spec fn entry_mb0_bits_are_zero(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| i < X86_NUM_ENTRIES ==>
            (#[trigger] self.entry_at_spec(layer, ptr, i, pt)).all_mb0_bits_are_zero()
    }

    /// Superpages and huge pages have their own address masks that cover fewer bits.
    /// We ensure that the additional bits that are set in the "generic" address mask are always
    /// zero for huge and super page mappings. Thus we can always use the generic mask for these
    /// addresses.
    pub open spec fn entry_addrs_can_use_generic_addr_mask(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| i < X86_NUM_ENTRIES ==> {
            let entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt);
            &&& (entry@.is_Page() ==> 0 < entry.layer())
            &&& entry.can_use_generic_addr_mask()
        }
    }

    pub open spec fn ghost_pt_used_regions_pairwise_disjoint(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat, j: nat, r: MemRegion|
            i != j &&
            i < pt.entries.len() && pt.entries[i as int].is_Some() &&
            #[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(r) &&
            j < pt.entries.len() && pt.entries[j as int].is_Some()
            ==> !(#[trigger] pt.entries[j as int].get_Some_0().used_regions.contains(r))
    }

    // TODO: this may be implied by the other ones
    pub open spec fn ghost_pt_region_notin_used_regions(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat|
            i < pt.entries.len() && pt.entries[i as int].is_Some()
            ==> !(#[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(pt.region))
    }

    pub open spec fn ghost_pt_used_regions_rtrancl(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        // reflexive
        &&& pt.used_regions.contains(pt.region)
        // transitive
        &&& forall|i: nat, r: MemRegion| #![trigger pt.entries[i as int].get_Some_0().used_regions.contains(r), pt.used_regions.contains(r)]
                i < pt.entries.len() && pt.entries[i as int].is_Some() &&
                pt.entries[i as int].get_Some_0().used_regions.contains(r)
                ==> pt.used_regions.contains(r)
    }

    pub open spec fn interp_at(self, layer: nat, ptr: usize, base_vaddr: nat, pt: PTDir) -> l1::Directory
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES, 2nat
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        l1::Directory {
            entries: self.interp_at_aux(layer, ptr, base_vaddr, seq![], pt),
            layer: layer,
            base_vaddr,
            arch: x86_arch_spec,
            // We don't have to check the flags because we know (from the invariant) that all
            // directories have these flags set.
            flags: permissive_flags,
        }
    }

    pub open spec fn interp_at_entry(self, layer: nat, ptr: usize, base_vaddr: nat, idx: nat, pt: PTDir) -> l1::NodeEntry
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - idx, 0nat
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        match self.view_at(layer, ptr, idx, pt) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let entry_base = x86_arch_spec.entry_base(layer, base_vaddr, idx);
                l1::NodeEntry::Directory(self.interp_at(layer + 1, dir_addr, entry_base, pt.entries[idx as int].get_Some_0()))
            },
            GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } =>
                l1::NodeEntry::Page(
                    PageTableEntry {
                        frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(layer) },
                        flags: Flags {
                            is_writable:     flag_RW,
                            is_supervisor:   !flag_US,
                            disable_execute: flag_XD,
                        },
                    }),
            GhostPageDirectoryEntry::Empty =>
                l1::NodeEntry::Empty(),
        }
    }

    pub open spec fn interp_at_aux(self, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, pt: PTDir) -> Seq<l1::NodeEntry>
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        decreases_by(Self::termination_interp_at_aux);
        if init.len() >= X86_NUM_ENTRIES {
            init
        } else {
            let entry = self.interp_at_entry(layer, ptr, base_vaddr, init.len(), pt);
            self.interp_at_aux(layer, ptr, base_vaddr, init.push(entry), pt)
        }
    }

    #[verifier(decreases_by)]
    proof fn termination_interp_at_aux(self, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, pt: PTDir) {
        assert(self.directories_obey_invariant_at(layer, ptr, pt));
        assert(self.inv_at(layer, ptr, pt));
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            // Can't assert this for the actual entry because we'd have to call `interp_at_entry`
            // whose termination depends on this function's termination.
            assert(forall|e: l1::NodeEntry| #![auto] init.push(e).len() == init.len() + 1);
            assert(forall|e: l1::NodeEntry| #![auto] X86_NUM_ENTRIES - init.push(e).len() < X86_NUM_ENTRIES - init.len());
            // FIXME: Verus incompleteness?
            assume(false);
        }
    }

    pub open spec fn interp(self) -> l1::Directory {
        let cr3 = self.memory.cr3_spec();
        self.interp_at(0, cr3.base, 0, self.ghost_pt@)
    }

    proof fn lemma_inv_at_different_memory(self, other: PageTable, layer: nat, ptr: usize, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            forall|r: MemRegion| pt.used_regions.contains(r)
                ==> #[trigger] self.memory.region_view(r) === other.memory.region_view(r),
            // Some parts of other's invariant that we should already know
            other.memory.inv(),
            other.memory.regions().contains(pt.region),
            pt.used_regions.subset_of(other.memory.regions()),
        ensures
            other.inv_at(layer, ptr, pt),
        decreases X86_NUM_LAYERS - layer
    {
        assert(other.well_formed(ptr));
        assert(other.memory.inv());
        assert(other.memory.regions().contains(pt.region));
        assert(pt.region.base == ptr);
        assert(other.layer_in_range(layer));
        assert(pt.entries.len() == X86_NUM_ENTRIES);
        assert(other.ghost_pt_used_regions_rtrancl(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt));
        assert(other.ghost_pt_region_notin_used_regions(layer, ptr, pt));
        assert(pt.used_regions.subset_of(other.memory.regions()));

        assert(other.entry_mb0_bits_are_zero(layer, ptr, pt)) by {
            assert forall|i: nat|
            i < X86_NUM_ENTRIES implies {
                let entry = #[trigger] other.entry_at_spec(layer, ptr, i, pt);
                &&& entry.all_mb0_bits_are_zero()
            } by
            {
                let entry = #[trigger] other.entry_at_spec(layer, ptr, i, pt);
                let self_entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt);
                assert(entry === self_entry);
            };
        };

        assert(other.entry_addrs_can_use_generic_addr_mask(layer, ptr, pt)) by {
            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                let entry = #[trigger] other.entry_at_spec(layer, ptr, i, pt);
                &&& (entry@.is_Page() ==> 0 < entry.layer())
                &&& entry.can_use_generic_addr_mask()
            } by {
                assert(other.entry_at_spec(layer, ptr, i, pt) == self.entry_at_spec(layer, ptr, i, pt));
            };
        };

        assert forall|i: nat|
        i < X86_NUM_ENTRIES implies {
            let entry = #[trigger] other.view_at(layer, ptr, i, pt);
            entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
        } by {
            let entry = other.view_at(layer, ptr, i, pt);
            let o_entry = other.entry_at_spec(layer, ptr, i, pt);
            let s_entry = self.entry_at_spec(layer, ptr, i, pt);
            assert(o_entry@ == entry);
            assert(o_entry == s_entry);
            if entry.is_Directory() {
                assert(self.directories_have_flags(layer, ptr, pt));
                assert(self.view_at(layer, ptr, i, pt).get_Directory_flag_RW());
                assert(self.view_at(layer, ptr, i, pt).get_Directory_flag_US());
                assert(!self.view_at(layer, ptr, i, pt).get_Directory_flag_XD());
            }
        };
        assert(other.directories_have_flags(layer, ptr, pt));

        assert forall|i: nat|
        i < X86_NUM_ENTRIES implies {
            let entry = #[trigger] other.view_at(layer, ptr, i, pt);
            &&& entry.is_Directory() == pt.entries[i as int].is_Some()
            &&& entry.is_Directory() ==> other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0())
        } by
        {
            let entry = other.view_at(layer, ptr, i, pt);
            assert(entry === self.view_at(layer, ptr, i, pt));
            assert(entry.is_Directory() == pt.entries[i as int].is_Some());
            if entry.is_Directory() {
                let entry_pt = pt.entries[i as int].get_Some_0();
                assert(self.directories_obey_invariant_at(layer, ptr, pt));
                assert(self.inv_at(layer + 1, entry.get_Directory_addr(), entry_pt));
                assert(self.ghost_pt_used_regions_rtrancl(layer + 1, entry.get_Directory_addr(), entry_pt));
                assert(pt.used_regions.contains(entry_pt.region));
                assert(other.memory.regions().contains(entry_pt.region));
                self.lemma_inv_at_different_memory(other, layer + 1, entry.get_Directory_addr(), entry_pt);
                assert(other.inv_at(layer + 1, entry.get_Directory_addr(), entry_pt));
            }
        };

        assert(other.ghost_pt_matches_structure(layer, ptr, pt));
        assert(other.directories_obey_invariant_at(layer, ptr, pt));
    }

    proof fn lemma_interp_at_entry_different_memory(self, other: PageTable, layer: nat, ptr: usize, base: nat, idx: nat, pt1: PTDir, pt2: PTDir)
        requires
            idx < X86_NUM_ENTRIES,
            pt2.region === pt1.region,
            pt2.entries[idx as int] === pt1.entries[idx as int],
            self.inv_at(layer, ptr, pt1),
            other.inv_at(layer, ptr, pt2),
            self.memory.spec_read(idx, pt1.region) === other.memory.spec_read(idx, pt2.region),
            pt2.entries[idx as int].is_Some() ==> (forall|r: MemRegion| pt2.entries[idx as int].get_Some_0().used_regions.contains(r)
                ==> #[trigger] self.memory.region_view(r) === other.memory.region_view(r)),
        ensures
            self.interp_at_entry(layer, ptr, base, idx, pt1) === other.interp_at_entry(layer, ptr, base, idx, pt2),
        decreases X86_NUM_LAYERS - layer
    {
        assert(self.view_at(layer, ptr, idx, pt1) === other.view_at(layer, ptr, idx, pt2));
        let next_layer = (layer + 1) as nat;
        match self.view_at(layer, ptr, idx, pt1) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let entry_base = x86_arch_spec.entry_base(layer, base, idx);
                let dir_pt = pt1.entries[idx as int].get_Some_0();
                assert(dir_pt === pt2.entries[idx as int].get_Some_0());
                assert(self.directories_obey_invariant_at(layer, ptr, pt1));
                assert(other.directories_obey_invariant_at(layer, ptr, pt2));
                assert(self.inv_at(next_layer, dir_addr, dir_pt));
                self.lemma_interp_at_aux_facts(next_layer, dir_addr, entry_base, seq![], dir_pt);
                other.lemma_interp_at_aux_facts(next_layer, dir_addr, entry_base, seq![], dir_pt);

                assert forall|i: nat| i < X86_NUM_ENTRIES implies
                    self.interp_at_entry(next_layer, dir_addr, entry_base, i, dir_pt)
                        === other.interp_at_entry(next_layer, dir_addr, entry_base, i, dir_pt)
                    && #[trigger] self.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries[i as int]
                        === other.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries[i as int] by
                {
                    self.lemma_interp_at_entry_different_memory(other, next_layer, dir_addr, entry_base, i, dir_pt, dir_pt);
                };
                assert_seqs_equal!(self.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries, other.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries);
                assert(self.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries === other.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries);
            },
            _ => (),
        }
    }

    pub proof fn lemma_interp_at_facts(self, layer: nat, ptr: usize, base_vaddr: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            self.interp_at(layer, ptr, base_vaddr, pt).inv(),
        ensures
            self.interp_at(layer, ptr, base_vaddr, pt).base_vaddr     == base_vaddr,
            self.interp_at(layer, ptr, base_vaddr, pt).upper_vaddr()  == x86_arch_spec.upper_vaddr(layer, base_vaddr),
            self.interp_at(layer, ptr, base_vaddr, pt).interp().lower == base_vaddr,
            self.interp_at(layer, ptr, base_vaddr, pt).interp().upper == x86_arch_spec.upper_vaddr(layer, base_vaddr),
            ({ let res = self.interp_at(layer, ptr, base_vaddr, pt);
               forall|j: nat| j < res.entries.len() ==> res.entries[j as int] === #[trigger] self.interp_at_entry(layer, ptr, base_vaddr, j, pt)
            }),
    {
        self.lemma_interp_at_aux_facts(layer, ptr, base_vaddr, seq![], pt);
        let res = self.interp_at(layer, ptr, base_vaddr, pt);
        assert(res.pages_match_entry_size());
        assert(res.directories_are_in_next_layer());
        assert(res.directories_match_arch());
        assert(res.directories_obey_invariant());
        assert(res.directories_are_nonempty());
        assert(res.frames_aligned());
        res.lemma_inv_implies_interp_inv();
    }

    pub proof fn lemma_interp_at_facts_entries(self, layer: nat, ptr: usize, base_vaddr: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            self.interp_at(layer, ptr, base_vaddr, pt).inv(),
        ensures
            ({ let res = self.interp_at(layer, ptr, base_vaddr, pt);
                &&& (forall|j: nat|
                    #![trigger res.entries[j as int]]
                    j < res.entries.len() ==>
                    match self.view_at(layer, ptr, j, pt) {
                        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                            &&& res.entries[j as int].is_Directory()
                            &&& res.entries[j as int].get_Directory_0() === self.interp_at((layer + 1) as nat, dir_addr, x86_arch_spec.entry_base(layer, base_vaddr, j), pt.entries[j as int].get_Some_0())
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => res.entries[j as int].is_Page() && res.entries[j as int].get_Page_0().frame.base == addr,
                        GhostPageDirectoryEntry::Empty             => res.entries[j as int].is_Empty(),
                    })
            })
    {
        self.lemma_interp_at_aux_facts(layer, ptr, base_vaddr, seq![], pt);
        let res = self.interp_at(layer, ptr, base_vaddr, pt);
        assert(res.pages_match_entry_size());
        assert(res.directories_are_in_next_layer());
        assert(res.directories_match_arch());
        assert(res.directories_obey_invariant());
        assert(res.directories_are_nonempty());
        assert(res.frames_aligned());
        res.lemma_inv_implies_interp_inv();
    }

    proof fn lemma_interp_at_aux_facts(self, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            // aligned(base_vaddr, x86_arch_spec.entry_size(layer) * X86_NUM_ENTRIES),
        ensures
            self.interp_at_aux(layer, ptr, base_vaddr, init, pt).len() == if init.len() > X86_NUM_ENTRIES { init.len() } else { X86_NUM_ENTRIES as nat },
            forall|j: nat| j < init.len() ==> #[trigger] self.interp_at_aux(layer, ptr, base_vaddr, init, pt)[j as int] === init[j as int],
            ({ let res = self.interp_at_aux(layer, ptr, base_vaddr, init, pt);
                &&& (forall|j: nat|
                    #![trigger res[j as int]]
                    init.len() <= j && j < res.len() ==>
                    match self.view_at(layer, ptr, j, pt) {
                        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                            &&& res[j as int].is_Directory()
                            &&& res[j as int].get_Directory_0() === self.interp_at((layer + 1) as nat, dir_addr, x86_arch_spec.entry_base(layer, base_vaddr, j), pt.entries[j as int].get_Some_0())
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => res[j as int].is_Page() && res[j as int].get_Page_0().frame.base == addr,
                        GhostPageDirectoryEntry::Empty             => res[j as int].is_Empty(),
                    })
                &&& (forall|j: nat| init.len() <= j && j < res.len() ==> res[j as int] === #[trigger] self.interp_at_entry(layer, ptr, base_vaddr, j, pt))
            }),
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
    {
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            assert(self.directories_obey_invariant_at(layer, ptr, pt));
            let entry = self.interp_at_entry(layer, ptr, base_vaddr, init.len(), pt);
            let init_next = init.push(entry);

            self.lemma_interp_at_aux_facts(layer, ptr, base_vaddr, init_next, pt);
        }
    }

    fn resolve_aux(&self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: Ghost<PTDir>) -> (res: Result<(usize, PageTableEntryExec), ()>)
        requires
            self.inv_at(layer as nat, ptr, pt@),
            self.interp_at(layer as nat, ptr, base as nat, pt@).inv(),
            self.interp_at(layer as nat, ptr, base as nat, pt@).interp().accepted_resolve(vaddr as nat),
            base <= vaddr < MAX_BASE,
        ensures
            // Refinement of l1
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp_at(layer as nat, ptr, base as nat, pt@).resolve(vaddr as nat),
            // Refinement of l0
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp_at(layer as nat, ptr, base as nat, pt@).interp().resolve(vaddr as nat),
        // decreases X86_NUM_LAYERS - layer
    {
        proof { self.lemma_interp_at_facts(layer as nat, ptr, base as nat, pt@); }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
        let entry      = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = Ghost(self.interp_at(layer as nat, ptr, base as nat, pt@));
        proof {
            assert(entry.can_use_generic_addr_mask());
            interp@.lemma_resolve_structure_assertions(vaddr as nat, idx as nat);
            interp@.lemma_resolve_refines(vaddr as nat);
        }
        if entry.is_mapping() {
            let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
            proof {
                indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
                assert(entry_base <= vaddr);
            }
            if entry.is_dir(layer) {
                assert(entry@.is_Directory());
                let dir_addr = entry.address() as usize;
                assert(pt@.entries[idx as int].is_Some());
                let dir_pt: Ghost<PTDir> = Ghost(pt@.entries.index(idx as int).get_Some_0());
                assert(self.directories_obey_invariant_at(layer as nat, ptr, pt@));
                proof {
                    assert(interp@.inv());
                    assert(interp@.directories_obey_invariant());
                    assert(interp@.entries[idx as int].is_Directory());
                    assert(interp@.entries[idx as int].get_Directory_0().inv());
                    assert(l1::NodeEntry::Directory(self.interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt@)) === interp@.entries[idx as int]);
                    assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt@));
                }
                let res = self.resolve_aux(layer + 1, dir_addr, entry_base, vaddr, dir_pt);
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
                res
            } else {
                assert(entry@.is_Page());
                assert(interp@.entries[idx as int].is_Page());
                let pte = PageTableEntryExec {
                    frame: MemRegionExec { base: entry.address() as usize, size: x86_arch_exec().entry_size(layer) },
                    flags: entry.flags()
                };
                let res = Ok((entry_base, pte));
                proof {
                if interp@.resolve(vaddr as nat).is_Ok() {
                    assert(interp@.entries[idx as int].get_Page_0() === interp@.resolve(vaddr as nat).get_Ok_0().1);
                    assert(interp@.entries[idx as int] === self.interp_at_entry(layer as nat, ptr, base as nat, idx as nat, pt@));
                }
                }
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).0) === l1::result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.0));
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.frame) === l1::result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.1.frame));
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.flags) === l1::result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.1.flags));
                assert(l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
                res
            }
        } else {
            assert(entry@.is_Empty());
            assert(interp@.entries[idx as int].is_Empty());
            assert(l1::result_map_ok(Err(()), |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
            Err(())
        }
    }

    pub fn resolve(&self, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec),()>)
        requires
            self.inv(),
            self.interp().inv(),
            self.interp().interp().accepted_resolve(vaddr as nat),
            vaddr < MAX_BASE,
        ensures
            // Refinement of l1
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp().resolve(vaddr as nat),
            // Refinement of l0
            l1::result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp().interp().resolve(vaddr as nat),
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        let res = self.resolve_aux(0, cr3.base, 0, vaddr, Ghost(self.ghost_pt@));
        res
    }

    pub open spec fn accepted_mapping(self, vaddr: nat, pte: PageTableEntry) -> bool {
        // Can't map pages in PML4, i.e. layer 0
        &&& x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size, 1)
        &&& pte.frame.base <= MAX_PHYADDR
    }

    fn map_frame_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pte: PageTableEntryExec, pt: Ghost<PTDir>)
        -> (res: Result<Ghost<(PTDir,Set<MemRegion>)>,()>)
        requires
            old(self).inv_at(layer as nat, ptr, pt@),
            old(self).interp_at(layer as nat, ptr, base as nat, pt@).inv(),
            old(self).memory.inv(),
            old(self).memory.alloc_available_pages() >= 3 - layer,
            old(self).accepted_mapping(vaddr as nat, pte@),
            old(self).interp_at(layer as nat, ptr, base as nat, pt@).accepted_mapping(vaddr as nat, pte@),
            base <= vaddr < MAX_BASE,
            // aligned(base, old(self).arch@.entry_size(layer) * X86_NUM_ENTRIES),
        ensures
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    // We return the regions that we added
                    &&& self.memory.regions() === old(self).memory.regions().union(new_regions)
                    &&& pt_res.used_regions === pt@.used_regions.union(new_regions)
                    // and only those we added
                    &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)))
                    &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)))
                    // Invariant preserved
                    &&& self.inv_at(layer as nat, ptr, pt_res)
                    // We only touch already allocated regions if they're in pt.used_regions
                    &&& (forall|r: MemRegion| !(#[trigger] pt@.used_regions.contains(r)) && !(new_regions.contains(r))
                        ==> self.memory.region_view(r) === old(self).memory.region_view(r))
                    &&& pt_res.region === pt@.region
                },
                Err(e) => {
                    // If error, unchanged
                    &&& self === old(self)
                },
            },
            // Refinement of l1
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)
                },
                Err(e) =>
                    Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@),
            },
            self.memory.cr3_spec() == old(self).memory.cr3_spec(),
        // decreases X86_NUM_LAYERS - layer
    {
        proof {
            self.lemma_interp_at_facts(layer as nat, ptr, base as nat, pt@);

            // this is the expensive bit of `lemma_interp_at_facts`, split out for further
            // refactoring
            self.lemma_interp_at_facts_entries(layer as nat, ptr, base as nat, pt@);
        }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof {
            assert({
                &&& between(vaddr as nat, x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat), x86_arch_spec.next_entry_base(layer as nat, base as nat, idx as nat))
                &&& aligned(vaddr as nat, x86_arch_spec.entry_size(layer as nat)) ==> vaddr == x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat)
                &&& idx < X86_NUM_ENTRIES }) by
            {
                let es = x86_arch_spec.entry_size(layer as nat);
                assert(aligned(base as nat, es)) by {
                    lib::mod_mult_zero_implies_mod_zero(base as nat, es, X86_NUM_ENTRIES as nat);
                };
                indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, es, X86_NUM_ENTRIES as nat);
            };
        }
        let entry = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = Ghost(self.interp_at(layer as nat, ptr, base as nat, pt@));
        proof {
            interp@.lemma_map_frame_structure_assertions(vaddr as nat, pte@, idx as nat);
            interp@.lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
        }
        let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                if x86_arch_exec().entry_size(layer) == pte.frame.size {
                    assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@));
                    Err(())
                } else {
                    let dir_addr = entry.address() as usize;
                    assert(pt@.entries[idx as int].is_Some());
                    let dir_pt: Ghost<PTDir> = Ghost(pt@.entries.index(idx as int).get_Some_0());
                    assert(self.directories_obey_invariant_at(layer as nat, ptr, pt@));
                    match self.map_frame_aux(layer + 1, dir_addr, entry_base, vaddr, pte, dir_pt) {
                        Ok(rec_res) => {
                            let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                            let new_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);

                            assert(dir_pt_res@.used_regions === dir_pt@.used_regions.union(new_regions@));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] dir_pt@.used_regions.contains(r)));
                            assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt_res@));
                            assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@))
                                   === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt@).map_frame(vaddr as nat, pte@));
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions.union(new_regions@),
                                });

                            assert(idx < pt@.entries.len());
                            assert(pt_res@.region === pt@.region);
                            assert(!new_regions@.contains(pt_res@.region));
                            assert(!dir_pt_res@.used_regions.contains(pt_res@.region));

                            assert(self.inv_at(layer as nat, ptr, pt_res@)
                                && Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)) by
                            {
                                assert forall|i: nat| i < X86_NUM_ENTRIES
                                    implies {
                                        let entry = self.view_at(layer as nat, ptr, i, pt_res@);
                                        entry.is_Directory() == (#[trigger] pt_res@.entries[i as int]).is_Some()
                                    }
                                by {
                                    assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                                    let entry = self.view_at(layer as nat, ptr, i, pt_res@);
                                    if i == idx {
                                    } else {
                                        assert(pt@.entries[i as int] === pt_res@.entries[i as int]);
                                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                                        assert(entry.is_Directory() == pt_res@.entries[i as int].is_Some());
                                    }
                                };
                                assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt_res@));

                                assert(self.ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt_res@));
                                assert(self.ghost_pt_region_notin_used_regions(layer as nat, ptr, pt_res@));
                                assert forall|i: nat, j: nat, r: MemRegion|
                                    i != j &&
                                    i < pt_res@.entries.len() && pt_res@.entries[i as int].is_Some() &&
                                    #[trigger] pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) &&
                                    j < pt_res@.entries.len() && pt_res@.entries[j as int].is_Some()
                                    implies !(#[trigger] pt_res@.entries[j as int].get_Some_0().used_regions.contains(r)) by
                                {
                                    assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt@));
                                    if j == idx {
                                        assert(pt_res@.entries[j as int].get_Some_0() === dir_pt_res@);
                                        assert(pt_res@.entries[i as int] === pt@.entries[i as int]);
                                        if new_regions@.contains(r) {
                                            assert(!dir_pt@.used_regions.contains(r));
                                            assert(!old(self).memory.regions().contains(r));
                                            assert(!dir_pt_res@.used_regions.contains(r));
                                        } else {
                                            if dir_pt@.used_regions.contains(r) {
                                                assert(pt@.used_regions.contains(r));
                                                assert(old(self).memory.regions().contains(r));
                                                assert(!dir_pt_res@.used_regions.contains(r));
                                            }
                                        }
                                    } else {
                                        if i == idx {
                                            assert(pt_res@.entries[i as int].get_Some_0() === dir_pt_res@);
                                            assert(pt_res@.entries[j as int] === pt@.entries[j as int]);
                                            if new_regions@.contains(r) {
                                                assert(dir_pt_res@.used_regions.contains(r));
                                                assert(!dir_pt@.used_regions.contains(r));
                                                assert(!old(self).memory.regions().contains(r));
                                                assert(!pt@.entries[j as int].get_Some_0().used_regions.contains(r));
                                            } else {
                                                assert(dir_pt@.used_regions.contains(r));
                                                assert(!pt@.entries[j as int].get_Some_0().used_regions.contains(r));
                                            }
                                        } else {
                                            assert(pt_res@.entries[i as int] === pt@.entries[i as int]);
                                            assert(pt_res@.entries[j as int] === pt@.entries[j as int]);
                                        }
                                    }
                                };
                                assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_res@));

                                assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                    entry.is_Directory() ==> {
                                        &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0())
                                    }
                                }
                                by {
                                    let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                    let byte_addr = (ptr + i * WORD_SIZE) as nat;
                                    if i == idx {
                                        assert(pt_res@.entries[i as int].get_Some_0() === dir_pt_res@);
                                        assert(entry.get_Directory_addr() === dir_addr);
                                        assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0()));
                                    } else {
                                        assert(old(self).directories_obey_invariant_at(layer as nat, ptr, pt@));
                                        assert(pt@.entries[i as int] === pt_res@.entries[i as int]);
                                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt_res@));
                                        if entry.is_Directory() {
                                            let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                            assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_res@));
                                            assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                   implies !new_regions@.contains(r) by
                                            {
                                                assert(pt_entry.used_regions.contains(r));
                                                assert(old(self).memory.regions().contains(r));
                                            };
                                            assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                   ==> !dir_pt@.used_regions.contains(r));
                                            assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                                   ==> #[trigger] old(self).memory.region_view(r) === self.memory.region_view(r));
                                            assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0()));
                                            assert(forall|r: MemRegion| pt_res@.entries[i as int].get_Some_0().used_regions.contains(r)
                                                   ==> #[trigger] self.memory.region_view(r) === old(self).memory.region_view(r));
                                            assert(pt_res@.entries[i as int].is_Some());
                                            assert(pt_res@.entries[i as int].get_Some_0().used_regions === pt@.entries[i as int].get_Some_0().used_regions);
                                            old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0());
                                            assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0()));
                                        }
                                    }
                                };
                                assert(self.directories_obey_invariant_at(layer as nat, ptr, pt_res@));

                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                    entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
                                } by {
                                    assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                                    let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                    let old_entry = old(self).view_at(layer as nat, ptr, i, pt@);
                                    assert(old_entry == entry);
                                    assert(old(self).directories_have_flags(layer as nat, ptr, pt@));
                                    if old_entry.is_Directory() {
                                        assert(old_entry.get_Directory_flag_RW() && old_entry.get_Directory_flag_US() && !old_entry.get_Directory_flag_XD());
                                    }
                                };
                                assert(self.directories_have_flags(layer as nat, ptr, pt_res@));

                                assert(self.entry_addrs_can_use_generic_addr_mask(layer as nat, ptr, pt_res@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt_res@);
                                        &&& (entry@.is_Page() ==> 0 < entry.layer())
                                        &&& entry.can_use_generic_addr_mask()
                                    } by {
                                        if i == idx {
                                        } else {
                                            assert(self.entry_at_spec(layer as nat, ptr, i, pt_res@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                        }
                                    };
                                };

                                assert(self.entry_mb0_bits_are_zero(layer as nat, ptr, pt_res@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies
                                        #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt_res@).all_mb0_bits_are_zero()
                                    by {
                                        if i == idx {
                                        } else {
                                            assert(self.entry_at_spec(layer as nat, ptr, i, pt_res@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                        }
                                    };
                                };

                                assert(self.inv_at(layer as nat, ptr, pt_res@));

                                assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)) by {
                                    self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_res@);
                                    assert(pt_res@.region === pt@.region);
                                    // recursive postcondition:
                                    assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@))
                                           === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt@).map_frame(vaddr as nat, pte@));
                                    assert(self.inv_at(layer as nat, ptr, pt_res@));
                                    assert(old(self).inv_at(layer as nat, ptr, pt@));
                                    assert(pt_res@.entries[idx as int].is_Some());
                                    assert(pt_res@.entries[idx as int].get_Some_0() === dir_pt_res@);

                                    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt@.entries[i as int] === pt_res@.entries[i as int]);

                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES && i != idx
                                        implies
                                            self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int]
                                            === #[trigger] old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                                    {
                                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).is_Ok());
                                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] === old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int]);
                                        assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int] === self.interp_at_entry(layer as nat, ptr, base as nat, i, pt_res@));
                                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int] === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                                        if pt_res@.entries[i as int].is_Some() {
                                            let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                            assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_res@));
                                            assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                   implies !new_regions@.contains(r) by
                                            {
                                                assert(pt_entry.used_regions.contains(r));
                                                assert(old(self).memory.regions().contains(r));
                                            };
                                            assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                   ==> !dir_pt_res@.used_regions.contains(r));
                                            assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                                   ==> #[trigger] old(self).memory.region_view(r) === self.memory.region_view(r));
                                        }
                                        old(self).lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt@, pt_res@);
                                        assert(self.interp_at_entry(layer as nat, ptr, base as nat, i, pt_res@) === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                                    };

                                    assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[idx as int] === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                                    assert_seqs_equal!(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries, old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                    assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                    assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@));
                                };
                            };

                            // posts
                            assert forall|r: MemRegion| !pt@.used_regions.contains(r) && !new_regions@.contains(r)
                                   implies #[trigger] self.memory.region_view(r) === old(self).memory.region_view(r) by
                            {
                                assert(!dir_pt@.used_regions.contains(r));
                            };
                            assert(self.memory.regions() === old(self).memory.regions().union(new_regions@));
                            assert(pt_res@.used_regions === pt@.used_regions.union(new_regions@));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));
                            assert(pt_res@.region === pt@.region);

                            let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,new_regions@));
                            Ok(res)
                        },
                        Err(e) => {
                            assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@));
                            Err(e)
                        },
                    }
                }
            } else {
                assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@));
                Err(())
            }
        } else {
            if x86_arch_exec().entry_size(layer) == pte.frame.size {
                proof {
                    assert_by_contradiction!(layer > 0, {
                        let iprime = choose|i: nat| 0 < i && i < X86_NUM_LAYERS && #[trigger] x86_arch_spec.entry_size(i) == pte.frame.size;
                        assert(x86_arch_spec.entry_size(0) == pte.frame.size);
                        assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1));
                        assert forall|i: nat|
                            0 < i < X86_NUM_LAYERS
                            implies
                            x86_arch_spec.entry_size(0) >= #[trigger] x86_arch_spec.entry_size(i)
                        by {
                            x86_arch_spec.lemma_entry_sizes_increase(0, i);
                        };
                        assert(false);
                    });
                    let frame_base = pte.frame.base as u64;
                    assert(addr_is_zero_padded(layer as nat, frame_base, true)) by {
                        assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1));
                        assert(x86_arch_spec.entry_size(layer as nat) == pte.frame.size);
                        assert(aligned(pte.frame.base as nat, pte.frame.size as nat));
                        lemma_aligned_addr_mask_facts(frame_base);
                        if layer == 1 {
                            assert(x86_arch_spec.entry_size(1) == L1_ENTRY_SIZE);
                            assert(frame_base & MASK_L1_PG_ADDR == frame_base & MASK_ADDR);
                        } else if layer == 2 {
                            assert(x86_arch_spec.entry_size(2) == L2_ENTRY_SIZE);
                            assert(frame_base & MASK_L2_PG_ADDR == frame_base & MASK_ADDR);
                        } else if layer == 3 {
                            assert(x86_arch_spec.entry_size(3) == L3_ENTRY_SIZE);
                            assert(frame_base & MASK_L3_PG_ADDR == frame_base & MASK_ADDR);
                        } else {
                            assert(false);
                        }
                    };
                    assert(frame_base & MASK_ADDR == frame_base) by {
                        lemma_aligned_addr_mask_facts(frame_base);
                    };
                }
                let new_page_entry = PageDirectoryEntry::new_page_entry(layer, pte);
                let pwmem: Ghost<mem::PageTableMemory> = Ghost(self.memory);
                self.memory.write(ptr, idx, Ghost(pt@.region), new_page_entry.entry);
                assert(self.memory.region_view(pt@.region) === pwmem@.region_view(pt@.region).update(idx as int, new_page_entry.entry));

                assert forall|i: nat| i < X86_NUM_ENTRIES
                    implies {
                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                        entry.is_Directory() == pt@.entries[i as int].is_Some()
                    }
                by {
                    let byte_addr = (ptr + i * WORD_SIZE) as nat;
                    let entry = self.view_at(layer as nat, ptr, i, pt@);
                    if i == idx {
                        assert(entry === new_page_entry@);
                    } else {
                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                    }
                };
                assert(self.inv_at(layer as nat, ptr, pt@)) by {
                    assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt@));

                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                        entry.is_Directory() ==> {
                            &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0())
                        }
                    } by {
                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                        let byte_addr = (ptr + i * WORD_SIZE) as nat;
                        assert(i < self.memory.region_view(pt@.region).len());
                        if i == idx {
                            assert(entry === new_page_entry@);
                            assert(!entry.is_Directory());
                        } else {
                            assert(old(self).directories_obey_invariant_at(layer as nat, ptr, pt@));
                            assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                            if entry.is_Directory() {
                                assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0()));
                                assert(pt@.entries[i as int].is_Some());
                                assert(forall|r: MemRegion| pt@.entries[i as int].get_Some_0().used_regions.contains(r)
                                       ==> #[trigger] self.memory.region_view(r) === old(self).memory.region_view(r));
                                old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0());
                                assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0()));
                            }
                        }
                    };
                    assert(self.directories_obey_invariant_at(layer as nat, ptr, pt@));

                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                        entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
                    }
                    by {
                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                        assert(i < self.memory.region_view(pt@.region).len());
                        if i == idx {
                        } else {
                            assert(old(self).directories_have_flags(layer as nat, ptr, pt@));
                            assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                            if entry.is_Directory() {
                            }
                        }
                    };
                    assert(self.directories_have_flags(layer as nat, ptr, pt@));

                    assert(self.ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt@));
                    assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt@));

                    assert(self.entry_addrs_can_use_generic_addr_mask(layer as nat, ptr, pt@)) by {
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                            let entry = #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt@);
                            &&& (entry@.is_Page() ==> 0 < entry.layer())
                            &&& entry.can_use_generic_addr_mask()
                        } by {
                            if i == idx {
                            } else {
                                assert(self.entry_at_spec(layer as nat, ptr, i, pt@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                            }
                        };
                    };

                    assert(self.entry_mb0_bits_are_zero(layer as nat, ptr, pt@)) by {
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt@).all_mb0_bits_are_zero()
                        by {
                            if i == idx {
                            } else {
                                assert(self.entry_at_spec(layer as nat, ptr, i, pt@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                            }
                        };
                    };
                };


                assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)) by {
                    self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt@);
                    assert(self.inv_at(layer as nat, ptr, pt@));
                    assert(old(self).inv_at(layer as nat, ptr, pt@));
                    assert(pt@.entries[idx as int].is_None());

                    assert forall|i: nat|
                        i < X86_NUM_ENTRIES && i != idx
                        implies
                            self.interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int]
                            === #[trigger] old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                    {
                        let byte_addr = (ptr + i * WORD_SIZE) as nat;
                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).is_Ok());
                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] === old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int]);
                        assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int] === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                        assert(old(self).memory.spec_read(i, pt@.region) === self.memory.spec_read(i, pt@.region));
                        old(self).lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt@, pt@);
                        assert(self.interp_at_entry(layer as nat, ptr, base as nat, i, pt@) === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                    };

                    let new_interp = self.interp_at(layer as nat, ptr, base as nat, pt@);
                    assert(new_interp.entries[idx as int] === self.interp_at_entry(layer as nat, ptr, base as nat, idx as nat, pt@));
                    assert(self.view_at(layer as nat, ptr, idx as nat, pt@) === new_page_entry@);

                    assert(self.interp_at_entry(layer as nat, ptr, base as nat, idx as nat, pt@) === l1::NodeEntry::Page(pte@));

                    assert(new_interp.entries[idx as int] === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                    assert_seqs_equal!(new_interp.entries, old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                    assert(new_interp.entries === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                    assert(Ok(new_interp) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@));
                };


                // posts
                assert(forall|r: MemRegion| !pt@.used_regions.contains(r) ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                proof {
                    // assert_sets_equal!(self.memory.regions(), old(self).memory.regions().union(set![]));
                    // assert(self.memory.regions() === old(self).memory.regions().union(set![]));
                    // assert_sets_equal!(pt@.used_regions, pt@.used_regions.union(set![]));
                    // assert(pt@.used_regions === pt@.used_regions.union(set![]));
                    // Asserting this inline is slow for some reason
                    lemma_set_union_empty_equals_set::<MemRegion>(self.memory.regions());
                    lemma_set_union_empty_equals_set::<MemRegion>(pt@.used_regions);
                }
                assert(forall|r: MemRegion| set![].contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)));
                assert(forall|r: MemRegion| set![].contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));
                assert(pt@.region === pt@.region);

                Ok(Ghost((pt@, set![])))
            } else {
                let new_dir_region = self.memory.alloc_page();
                let new_dir_ptr = new_dir_region.base;
                let new_dir_ptr_u64 = new_dir_ptr as u64;
                let new_dir_pt: Ghost<PTDir> = Ghost(
                    PTDir {
                        region: new_dir_region@,
                        entries: new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None),
                        used_regions: set![new_dir_region@],
                    });
                assert(new_dir_ptr_u64 & MASK_DIR_ADDR == new_dir_ptr_u64) by {
                    lemma_page_aligned_implies_mask_dir_addr_is_identity();
                };
                let new_dir_entry = PageDirectoryEntry::new_dir_entry(layer, new_dir_ptr_u64);
                self.memory.write(ptr, idx, Ghost(pt@.region), new_dir_entry.entry);

                // After writing the new empty directory entry we prove that the resulting state
                // satisfies the invariant and that the interpretation remains unchanged.
                let pt_with_empty: Ghost<PTDir> = Ghost(
                    PTDir {
                        region:       pt@.region,
                        entries:      pt@.entries.update(idx as int, Some(new_dir_pt@)),
                        used_regions: pt@.used_regions.insert(new_dir_pt@.region),
                    });
                // For easier reference we take a snapshot of self here. In the subsequent proofs
                // (after the recursive call) we have old(self), self_with_empty and self to refer
                // to each relevant state.
                let self_with_empty: Ghost<Self> = Ghost(*self);
                proof {
                    assert(pt_with_empty@.region === pt@.region);
                    lemma_new_seq::<u64>(512nat, 0u64);
                    lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
                    assert(new_dir_pt@.entries.len() == 512);
                    assert(new_dir_region@.contains(new_dir_ptr as nat));
                    assert(self_with_empty@.memory.region_view(new_dir_region@) === new_seq(512nat, 0u64));
                    self_with_empty@.lemma_zeroed_page_implies_empty_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@);
                    assert(self_with_empty@.empty_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));
                    assert(self_with_empty@.inv_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));

                    assert(forall|r: MemRegion| r !== new_dir_pt@.region && r !== pt_with_empty@.region
                           ==> self_with_empty@.memory.region_view(r) === old(self).memory.region_view(r));
                    assert(self_with_empty@.memory.region_view(pt_with_empty@.region)
                           === old(self).memory.region_view(pt_with_empty@.region).update(idx as int, new_dir_entry.entry));
                    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt@.entries[i as int] === pt_with_empty@.entries[i as int]);
                    assert(self_with_empty@.inv_at(layer as nat, ptr, pt_with_empty@)) by {
                        assert(self_with_empty@.ghost_pt_matches_structure(layer as nat, ptr, pt_with_empty@)) by {
                            assert forall|i: nat|
                                i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                    entry.is_Directory() == pt_with_empty@.entries[i as int].is_Some()
                                } by
                            {
                                let entry = self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                assert(old(self).directories_obey_invariant_at(layer as nat, ptr, pt@));
                                assert(old(self).ghost_pt_matches_structure(layer as nat, ptr, pt@));
                                if i == idx {
                                } else {
                                    let addr = ptr + (i * WORD_SIZE as nat);
                                    assert(self_with_empty@.memory.spec_read(i, pt_with_empty@.region)
                                           === old(self).memory.spec_read(i, pt@.region));
                                    assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                                    assert(entry.is_Directory() == pt_with_empty@.entries[i as int].is_Some());
                                }
                            };
                        };
                        assert(self_with_empty@.directories_obey_invariant_at(layer as nat, ptr, pt_with_empty@)) by {
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                entry.is_Directory()
                                    ==> self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_with_empty@.entries[i as int].get_Some_0())
                            } by
                            {
                                let entry = self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                assert(old(self).directories_obey_invariant_at(layer as nat, ptr, pt@));
                                assert(old(self).ghost_pt_matches_structure(layer as nat, ptr, pt@));
                                assert(old(self).ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt@));

                                assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt_with_empty@));
                                if i == idx {
                                } else {
                                    if entry.is_Directory() {
                                        let addr = ptr + (i * WORD_SIZE as nat);
                                        assert(self_with_empty@.memory.spec_read(i, pt_with_empty@.region)
                                               === old(self).memory.spec_read(i, pt@.region));
                                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                                        assert(pt@.entries[i as int].is_Some());
                                        let pt_entry = pt@.entries[i as int].get_Some_0();
                                        assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_entry));
                                        assert(pt@.entries[i as int] === pt_with_empty@.entries[i as int]);
                                        assert(old(self).memory.regions().contains(pt_entry.region));
                                        assert(self_with_empty@.memory.regions().contains(pt_entry.region));
                                        old(self).lemma_inv_at_different_memory(self_with_empty@, (layer + 1) as nat, entry.get_Directory_addr(), pt_entry);
                                        assert(self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_with_empty@.entries[i as int].get_Some_0()));
                                    }
                                }
                            };
                        };
                        assert(self_with_empty@.directories_have_flags(layer as nat, ptr, pt_with_empty@)) by {
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
                            } by {
                                let entry = self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@);
                                if i == idx {
                                } else {
                                    if entry.is_Directory() {
                                        assert(self_with_empty@.memory.spec_read(i, pt_with_empty@.region)
                                               === old(self).memory.spec_read(i, pt@.region));
                                        assert(entry === old(self).view_at(layer as nat, ptr, i, pt@));
                                    }
                                }
                            };
                        };
                        assert(self_with_empty@.ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt_with_empty@));
                        assert(self_with_empty@.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_with_empty@));
                        assert(self_with_empty@.ghost_pt_region_notin_used_regions(layer as nat, ptr, pt_with_empty@));

                        assert(self_with_empty@.entry_addrs_can_use_generic_addr_mask(layer as nat, ptr, pt_with_empty@)) by {
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] self_with_empty@.entry_at_spec(layer as nat, ptr, i, pt_with_empty@);
                                &&& (entry@.is_Page() ==> 0 < entry.layer())
                                &&& entry.can_use_generic_addr_mask()
                            } by {
                                if i == idx {
                                } else {
                                    assert(self_with_empty@.entry_at_spec(layer as nat, ptr, i, pt_with_empty@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                }
                            };
                        };

                        assert(self_with_empty@.entry_mb0_bits_are_zero(layer as nat, ptr, pt_with_empty@)) by {
                            assert forall|i: nat| i < X86_NUM_ENTRIES implies
                                #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt_with_empty@).all_mb0_bits_are_zero()
                            by {
                                if i == idx {
                                } else {
                                    assert(self_with_empty@.entry_at_spec(layer as nat, ptr, i, pt_with_empty@) === old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                }
                            };
                        };

                        assert(self_with_empty@.inv_at(layer as nat, ptr, pt_with_empty@));
                    };

                    assert(self_with_empty@.view_at(layer as nat, ptr, idx as nat, pt_with_empty@) === new_dir_entry@);

                    self_with_empty@.lemma_empty_at_interp_at_equal_l1_empty_dir(layer as nat, ptr, base as nat, idx as nat, pt_with_empty@);
                    let new_dir_interp: l1::Directory = self_with_empty@.interp_at((layer + 1) as nat, new_dir_ptr, entry_base as nat, new_dir_pt@);
                    interp@.lemma_new_empty_dir(idx as nat);
                    assert_seqs_equal!(new_dir_interp.entries, interp@.new_empty_dir(idx as nat).entries);
                    assert(new_dir_interp === interp@.new_empty_dir(idx as nat));

                    old(self).lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt@);
                    self_with_empty@.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_with_empty@);

                    assert forall|i: nat|
                        i < X86_NUM_ENTRIES && i != idx
                        implies
                            self_with_empty@.interp_at(layer as nat, ptr, base as nat, pt_with_empty@).entries[i as int]
                            === #[trigger] old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int] by
                    {
                        let prev_interp = old(self).interp_at(layer as nat, ptr, base as nat, pt@);
                        let byte_addr = (ptr + i * WORD_SIZE) as nat;
                        assert(prev_interp.entries[i as int] === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                        assert(old(self).memory.spec_read(i, pt@.region) === self_with_empty@.memory.spec_read(i, pt_with_empty@.region));
                        old(self).lemma_interp_at_entry_different_memory(self_with_empty@, layer as nat, ptr, base as nat, i, pt@, pt_with_empty@);
                        assert(i < X86_NUM_ENTRIES);
                        assert(self_with_empty@.interp_at_entry(layer as nat, ptr, base as nat, i, pt_with_empty@) === old(self).interp_at_entry(layer as nat, ptr, base as nat, i, pt@));
                        assert(self_with_empty@.interp_at_entry(layer as nat, ptr, base as nat, i, pt_with_empty@) === self_with_empty@.interp_at(layer as nat, ptr, base as nat, pt_with_empty@).entries[i as int]);
                        assert(self_with_empty@.interp_at(layer as nat, ptr, base as nat, pt_with_empty@).entries[i as int]
                               === old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int]);
                    };
                    assert(new_dir_interp.inv());
                }

                assert(self.accepted_mapping(vaddr as nat, pte@)) by {
                    reveal(PageTable::accepted_mapping);
                };
                assert(self.memory.alloc_available_pages() >= 2 - layer);
                assert(self.memory.alloc_available_pages() >= 3 - (layer + 1));
                match self.map_frame_aux(layer + 1, new_dir_ptr, entry_base, vaddr, pte, new_dir_pt) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                        let dir_new_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);
                        let pt_final: Ghost<PTDir> = Ghost(
                            PTDir {
                                region:       pt_with_empty@.region,
                                entries:      pt_with_empty@.entries.update(idx as int, Some(dir_pt_res@)),
                                used_regions: pt_with_empty@.used_regions.union(dir_new_regions@),
                            });
                        let new_regions: Ghost<Set<MemRegion>> = Ghost(dir_new_regions@.insert(new_dir_region@));
                        proof {
                            assert(idx < pt_with_empty@.entries.len());
                            assert(!dir_new_regions@.contains(pt_final@.region));
                            assert(!new_dir_pt@.used_regions.contains(pt_final@.region));
                            // Note: Many of these invariant/interp framing proofs are nearly
                            // identical. If I find some time I should extract them into a lemma.
                            // Would clean up this function quite a bit.
                            assert(self.inv_at(layer as nat, ptr, pt_final@)) by {
                                assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES implies {
                                            let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_final@);
                                            entry.is_Directory() == pt_final@.entries[i as int].is_Some()
                                        } by
                                    {
                                        let entry = self.view_at(layer as nat, ptr, i, pt_final@);
                                        assert(self_with_empty@.directories_obey_invariant_at(layer as nat, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_matches_structure(layer as nat, ptr, pt_with_empty@));
                                        if i == idx {
                                        } else {
                                            let addr = ptr + (i * WORD_SIZE as nat);
                                            assert(self.memory.spec_read(i, pt_final@.region)
                                                   === self_with_empty@.memory.spec_read(i, pt_with_empty@.region));
                                            assert(entry === self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@));
                                            assert(entry.is_Directory() == pt_final@.entries[i as int].is_Some());
                                        }
                                    };
                                };

                                assert(self.directories_obey_invariant_at(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_final@);
                                        entry.is_Directory()
                                            ==> self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_final@.entries[i as int].get_Some_0())
                                    } by
                                    {
                                        let entry = self.view_at(layer as nat, ptr, i, pt_final@);
                                        assert(self_with_empty@.directories_obey_invariant_at(layer as nat, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_matches_structure(layer as nat, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt_with_empty@));

                                        assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt_final@));
                                        if i == idx {
                                        } else {
                                            assert(pt_final@.entries[i as int] === pt_with_empty@.entries[i as int]);
                                            if entry.is_Directory() {
                                                let addr = ptr + (i * WORD_SIZE as nat);
                                                assert(self.memory.spec_read(i, pt_final@.region)
                                                       === self_with_empty@.memory.spec_read(i, pt_with_empty@.region));
                                                assert(entry === self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@));
                                                assert(pt_with_empty@.entries[i as int].is_Some());
                                                let pt_entry = pt_with_empty@.entries[i as int].get_Some_0();
                                                assert(self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_entry));
                                                assert(pt_with_empty@.entries[i as int] === pt_final@.entries[i as int]);
                                                assert(self_with_empty@.memory.regions().contains(pt_entry.region));
                                                assert(self.memory.regions().contains(pt_entry.region));
                                                assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                       ==> !dir_new_regions@.contains(r) && !new_dir_pt@.used_regions.contains(r));
                                                assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                                       ==> #[trigger] self_with_empty@.memory.region_view(r) === self.memory.region_view(r));
                                                self_with_empty@.lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt_entry);
                                                assert(pt_final@.entries[i as int].get_Some_0() === pt_entry);
                                                assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_final@.entries[i as int].get_Some_0()));
                                            }
                                        }
                                    };
                                };

                                assert(self.directories_have_flags(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_final@);
                                        entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
                                    } by {
                                        let entry = self.view_at(layer as nat, ptr, i, pt_final@);
                                        if i == idx {
                                        } else {
                                            if entry.is_Directory() {
                                                assert(self.memory.spec_read(i, pt_final@.region)
                                                       === self_with_empty@.memory.spec_read(i, pt_with_empty@.region));
                                                assert(entry === self_with_empty@.view_at(layer as nat, ptr, i, pt_with_empty@));
                                            }
                                        }
                                    };
                                };

                                assert(pt_final@.entries.len() == pt_with_empty@.entries.len());
                                assert(forall|i: nat| i != idx && i < pt_final@.entries.len() ==> pt_final@.entries[i as int] === pt_with_empty@.entries[i as int]);
                                assert(self.ghost_pt_used_regions_rtrancl(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat, r: MemRegion|
                                        i < pt_final@.entries.len() &&
                                        pt_final@.entries[i as int].is_Some() &&
                                        #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(r)
                                        implies pt_final@.used_regions.contains(r)
                                    by
                                    {
                                        if i == idx {
                                            if dir_new_regions@.contains(r) {
                                                assert(pt_final@.used_regions.contains(r));
                                            } else {
                                                assert(pt_with_empty@.entries[i as int].get_Some_0().used_regions.contains(r));
                                                assert(pt_with_empty@.used_regions.contains(r));
                                                assert(pt_final@.used_regions.contains(r));
                                            }
                                        } else {
                                            assert(pt_final@.entries[i as int] === pt_with_empty@.entries[i as int]);
                                        }
                                    };
                                };
                                assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat, j: nat, r: MemRegion|
                                        i != j &&
                                        i < pt_final@.entries.len() && pt_final@.entries[i as int].is_Some() &&
                                        #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(r) &&
                                        j < pt_final@.entries.len() && pt_final@.entries[j as int].is_Some()
                                        implies !(#[trigger] pt_final@.entries[j as int].get_Some_0().used_regions.contains(r))
                                    by
                                    {
                                        assert(self_with_empty@.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_with_empty@));
                                        if j == idx {
                                            assert(pt_final@.entries[j as int].get_Some_0() === dir_pt_res@);
                                            assert(pt_final@.entries[i as int] === pt@.entries[i as int]);
                                            if dir_new_regions@.contains(r) {
                                                assert(!new_dir_pt@.used_regions.contains(r));
                                                assert(!self_with_empty@.memory.regions().contains(r));
                                                assert(!dir_pt_res@.used_regions.contains(r));
                                            } else {
                                                if new_dir_pt@.used_regions.contains(r) {
                                                    assert(pt@.used_regions.contains(r));
                                                    assert(self_with_empty@.memory.regions().contains(r));
                                                    assert(!dir_pt_res@.used_regions.contains(r));
                                                }
                                            }
                                        } else {
                                            if i == idx {
                                                assert(pt_final@.entries[i as int].get_Some_0() === dir_pt_res@);
                                                assert(pt_final@.entries[j as int] === pt@.entries[j as int]);
                                                if dir_new_regions@.contains(r) {
                                                    assert(dir_pt_res@.used_regions.contains(r));
                                                    assert(!new_dir_pt@.used_regions.contains(r));
                                                    assert(!self_with_empty@.memory.regions().contains(r));
                                                    assert(!pt@.entries[j as int].get_Some_0().used_regions.contains(r));
                                                } else {
                                                    assert(new_dir_pt@.used_regions.contains(r));
                                                    assert(!pt@.entries[j as int].get_Some_0().used_regions.contains(r));
                                                }
                                            } else {
                                                assert(pt_final@.entries[i as int] === pt@.entries[i as int]);
                                                assert(pt_final@.entries[j as int] === pt@.entries[j as int]);
                                            }
                                        }

                                    };
                                };
                                assert(self.ghost_pt_matches_structure(layer as nat, ptr, pt_final@));
                                assert(self.ghost_pt_region_notin_used_regions(layer as nat, ptr, pt_final@));

                                assert(self.entry_addrs_can_use_generic_addr_mask(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt_final@);
                                        &&& (entry@.is_Page() ==> 0 < entry.layer())
                                        &&& entry.can_use_generic_addr_mask()
                                    } by {
                                        if i == idx {
                                        } else {
                                            assert(self.entry_at_spec(layer as nat, ptr, i, pt_final@) === self_with_empty@.entry_at_spec(layer as nat, ptr, i, pt_with_empty@));
                                        }
                                    };
                                };

                                assert(self.entry_mb0_bits_are_zero(layer as nat, ptr, pt_final@)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies
                                        #[trigger] self.entry_at_spec(layer as nat, ptr, i, pt_final@).all_mb0_bits_are_zero()
                                    by {
                                        if i == idx {
                                        } else {
                                            assert(self.entry_at_spec(layer as nat, ptr, i, pt_final@) === self_with_empty@.entry_at_spec(layer as nat, ptr, i, pt_with_empty@));
                                        }
                                    };
                                };

                                assert(self.inv_at(layer as nat, ptr, pt_final@));
                            };

                            assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_final@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)) by {
                                self_with_empty@.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_with_empty@);
                                assert(self.inv_at(layer as nat, ptr, pt_final@));
                                assert(self_with_empty@.inv_at(layer as nat, ptr, pt_with_empty@));
                                self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_final@);

                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx
                                    implies
                                        self.interp_at(layer as nat, ptr, base as nat, pt_final@).entries[i as int]
                                        === #[trigger] self_with_empty@.interp_at(layer as nat, ptr, base as nat, pt_with_empty@).entries[i as int] by
                                {
                                    let prev_interp = self_with_empty@.interp_at(layer as nat, ptr, base as nat, pt_with_empty@);
                                    let byte_addr = (ptr + i * WORD_SIZE) as nat;
                                    assert(prev_interp.entries[i as int] === self_with_empty@.interp_at_entry(layer as nat, ptr, base as nat, i, pt_with_empty@));
                                    if pt_final@.entries[i as int].is_Some() {
                                        let pt_entry = pt_final@.entries[i as int].get_Some_0();
                                        assert(self.ghost_pt_used_regions_pairwise_disjoint(layer as nat, ptr, pt_final@));
                                        assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               implies !new_regions@.contains(r) by
                                        {
                                            assert(pt_entry.used_regions.contains(r));
                                            assert(self_with_empty@.memory.regions().contains(r));
                                            assert(old(self).memory.regions().contains(r));
                                            assert(!new_regions@.contains(r));
                                        };
                                        assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               ==> !dir_pt_res@.used_regions.contains(r));
                                        assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                               ==> #[trigger] old(self).memory.region_view(r) === self.memory.region_view(r));
                                    }
                                    assert(self_with_empty@.memory.spec_read(i, pt_with_empty@.region) === self.memory.spec_read(i, pt_final@.region));
                                    self_with_empty@.lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt_with_empty@, pt_final@);
                                    assert(self.interp_at_entry(layer as nat, ptr, base as nat, i, pt_final@) === self_with_empty@.interp_at_entry(layer as nat, ptr, base as nat, i, pt_with_empty@));
                                };

                                let final_interp = self.interp_at(layer as nat, ptr, base as nat, pt_final@);
                                assert(final_interp.entries[idx as int] === self.interp_at_entry(layer as nat, ptr, base as nat, idx as nat, pt_final@));
                                assert(final_interp.entries[idx as int] === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                                assert_seqs_equal!(final_interp.entries, old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                assert(final_interp.entries === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                assert(final_interp.layer === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().layer);
                                assert(final_interp.base_vaddr === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().base_vaddr);
                                assert(final_interp.arch === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@).get_Ok_0().arch);
                                assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_final@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).map_frame(vaddr as nat, pte@)) by {
                                };
                            };
                        }

                        // posts
                        proof {
                            assert(pt_final@.region === pt@.region);
                            // assert_sets_equal!(pt_with_empty@.used_regions, pt@.used_regions.union(new_regions@));
                            assert_sets_equal!(pt_final@.used_regions, pt@.used_regions.union(new_regions@));
                            assert(pt_final@.used_regions === pt@.used_regions.union(new_regions@));
                            assert_sets_equal!(self.memory.regions(), old(self).memory.regions().union(new_regions@));
                            assert(self.memory.regions() === old(self).memory.regions().union(new_regions@));
                            assert forall|r: MemRegion|
                                !(#[trigger] pt@.used_regions.contains(r))
                                && !new_regions@.contains(r)
                                implies self.memory.region_view(r) === old(self).memory.region_view(r) by
                            {
                                assert(r !== new_dir_region@);
                                assert(!pt_with_empty@.used_regions.contains(r));
                                assert(!new_dir_pt@.used_regions.contains(r));
                                assert(!dir_new_regions@.contains(r));
                                assert(self.memory.region_view(r) === self_with_empty@.memory.region_view(r));
                            };
                            assert forall|r: MemRegion|
                                new_regions@.contains(r)
                                implies !(#[trigger] old(self).memory.regions().contains(r)) by
                            {
                                if r === new_dir_region@ {
                                    assert(!old(self).memory.regions().contains(r));
                                } else {
                                    assert(dir_new_regions@.contains(r));
                                    assert(!self_with_empty@.memory.regions().contains(r));
                                    assert(!old(self).memory.regions().contains(r));
                                }
                            };
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));
                        }
                        Ok(Ghost((pt_final@, new_regions@)))
                    },
                    Err(e) => {
                        assert(false); // We always successfully insert into an empty directory
                        Err(e)
                    },
                }
            }
        }
    }

    pub proof fn lemma_zeroed_page_implies_empty_at(self, layer: nat, ptr: usize, pt: PTDir)
        requires
            ptr % PAGE_SIZE == 0,
            self.well_formed(ptr),
            self.memory.inv(),
            self.memory.regions().contains(pt.region),
            pt.region.base == ptr,
            pt.region.size == PAGE_SIZE,
            self.memory.region_view(pt.region).len() == pt.entries.len(),
            pt.region.base == ptr,
            ptr == pt.region.base,
            pt.used_regions === set![pt.region],
            self.layer_in_range(layer),
            pt.entries.len() == X86_NUM_ENTRIES,
            forall|i: nat| i < X86_NUM_ENTRIES ==> self.memory.region_view(pt.region)[i as int] == 0u64,
            forall|i: nat| i < X86_NUM_ENTRIES ==> pt.entries[i as int].is_None(),
        ensures
            self.empty_at(layer, ptr, pt),
            self.inv_at(layer, ptr, pt),
    {
        assert forall|i: nat| i < X86_NUM_ENTRIES implies self.view_at(layer, ptr, i, pt).is_Empty()
        by { self.entry_at_spec(layer, ptr, i, pt).lemma_zero_entry_facts(); };
        // Can't combine with the first assert forall because manually choosing multiple triggers
        // in assert forall is broken.
        assert forall|i: nat| i < X86_NUM_ENTRIES implies
            ((#[trigger] self.entry_at_spec(layer, ptr, i, pt))@.is_Page() ==> 0 < self.entry_at_spec(layer, ptr, i, pt).layer()) &&
            self.entry_at_spec(layer, ptr, i, pt).can_use_generic_addr_mask()
        by {
            self.entry_at_spec(layer, ptr, i, pt).lemma_zero_entry_facts();
            let pt_entry = self.entry_at_spec(layer, ptr, i, pt);
            assert(pt_entry@.is_Page() ==> 0 < pt_entry.layer());
            assert(pt_entry.can_use_generic_addr_mask());
        };
        assert(self.entry_addrs_can_use_generic_addr_mask(layer, ptr, pt));

        assert(self.entry_mb0_bits_are_zero(layer, ptr, pt)) by {
            assert forall|i: nat| i < X86_NUM_ENTRIES implies
                (#[trigger] self.entry_at_spec(layer, ptr, i, pt)).all_mb0_bits_are_zero()
            by {
                assert(0u64 & bit!(0u64) != bit!(0u64)) by (bit_vector);
                reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
                assert(self.entry_at_spec(layer, ptr, i, pt).entry == 0);
                assert(self.entry_at_spec(layer, ptr, i, pt).entry & MASK_FLAG_P != MASK_FLAG_P);
                assert(self.entry_at_spec(layer, ptr, i, pt).all_mb0_bits_are_zero());
            };
        };

        assert(self.directories_obey_invariant_at(layer, ptr, pt));
        assert(self.inv_at(layer, ptr, pt));
    }

    proof fn lemma_empty_at_interp_at_aux_equal_l1_empty_dir(self, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, idx: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            forall|i: nat| i < init.len() ==> init[i as int] === l1::NodeEntry::Empty(),
            init.len() <= X86_NUM_ENTRIES,
            idx < X86_NUM_ENTRIES,
            self.view_at(layer, ptr, idx, pt).is_Directory(),
            self.empty_at((layer + 1) as nat, self.view_at(layer, ptr, idx, pt).get_Directory_addr(), pt.entries[idx as int].get_Some_0()),
        ensures
            ({ let res =
                self.interp_at_aux(
                layer + 1,
                self.view_at(layer, ptr, idx, pt).get_Directory_addr(),
                x86_arch_spec.entry_base(layer, base, idx),
                init,
                pt.entries[idx as int].get_Some_0());
            &&& res.len() === X86_NUM_ENTRIES as nat
            &&& forall|i: nat| i < res.len() ==> res[i as int] === l1::NodeEntry::Empty()
            })
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
    {
        assert(self.directories_obey_invariant_at(layer, ptr, pt));
        let entry_ptr = self.view_at(layer, ptr, idx, pt).get_Directory_addr();
        let entry_base = x86_arch_spec.entry_base(layer, base, idx);
        let entry_pt = pt.entries[idx as int].get_Some_0();

        let res = self.interp_at_aux(layer + 1, entry_ptr, entry_base, init, entry_pt);
        assert(self.inv_at(layer + 1, entry_ptr, entry_pt));

        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            let entry = self.interp_at_entry(layer + 1, entry_ptr, entry_base, init.len(), entry_pt);
            assert(entry === l1::NodeEntry::Empty());
            self.lemma_empty_at_interp_at_aux_equal_l1_empty_dir(layer, ptr, base, init.push(l1::NodeEntry::Empty()), idx, pt);
        }
    }

    proof fn lemma_empty_at_interp_at_equal_l1_empty_dir(self, layer: nat, ptr: usize, base: nat, idx: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            idx < X86_NUM_ENTRIES,
            self.view_at(layer, ptr, idx, pt).is_Directory(),
            self.empty_at((layer + 1) as nat, self.view_at(layer, ptr, idx, pt).get_Directory_addr(), pt.entries[idx as int].get_Some_0()),
        ensures
            ({ let res =
                self.interp_at(
                layer + 1,
                self.view_at(layer, ptr, idx, pt).get_Directory_addr(),
                x86_arch_spec.entry_base(layer, base, idx),
                pt.entries[idx as int].get_Some_0());
            &&& res.entries.len() === X86_NUM_ENTRIES as nat
            &&& forall|i: nat| i < res.entries.len() ==> res.entries[i as int] === l1::NodeEntry::Empty()
            })
    {
        assert(self.directories_obey_invariant_at(layer, ptr, pt));
        self.lemma_empty_at_interp_at_aux_equal_l1_empty_dir(layer, ptr, base, seq![], idx, pt);
    }

    proof fn lemma_not_empty_at_implies_interp_at_aux_not_empty(self, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, nonempty_idx: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            nonempty_idx < X86_NUM_ENTRIES,
            !self.view_at(layer, ptr, nonempty_idx, pt).is_Empty(),
            nonempty_idx < init.len() ==> !init[nonempty_idx as int].is_Empty()
        ensures
            !self.interp_at_aux(layer, ptr, base, init, pt)[nonempty_idx as int].is_Empty()
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
    {
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            let entry = self.interp_at_entry(layer, ptr, base, init.len(), pt);
            let new_init = init.push(entry);
            self.lemma_not_empty_at_implies_interp_at_aux_not_empty(layer, ptr, base, new_init, nonempty_idx, pt);
        }
    }

    proof fn lemma_empty_at_implies_interp_at_empty(self, layer: nat, ptr: usize, base: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            self.empty_at(layer, ptr, pt),
        ensures
            self.interp_at(layer, ptr, base, pt).empty()
    {
        self.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt);
    }

    proof fn lemma_not_empty_at_implies_interp_at_not_empty(self, layer: nat, ptr: usize, base: nat, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            !self.empty_at(layer, ptr, pt),
        ensures
            !self.interp_at(layer, ptr, base, pt).empty()
    {
        assert(exists|i: nat| i < X86_NUM_ENTRIES && !self.view_at(layer, ptr, i, pt).is_Empty());
        let i = choose|i: nat| i < X86_NUM_ENTRIES && !self.view_at(layer, ptr, i, pt).is_Empty();
        self.lemma_not_empty_at_implies_interp_at_aux_not_empty(layer, ptr, base, seq![], i, pt);
    }

    proof fn lemma_inv_at_doesnt_use_ghost_pt(self, other: Self, layer: nat, ptr: usize, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            other.memory === self.memory,
        ensures
            other.inv_at(layer, ptr, pt),
        decreases X86_NUM_LAYERS - layer
    {
        assert(forall|i: nat| i < X86_NUM_ENTRIES ==> other.view_at(layer, ptr, i, pt) === self.view_at(layer, ptr, i, pt));
        assert(forall|i: nat| i < X86_NUM_ENTRIES ==> other.entry_at_spec(layer, ptr, i, pt) === self.entry_at_spec(layer, ptr, i, pt));

        assert(other.well_formed(ptr));
        assert(other.memory.inv());
        assert(other.memory.regions().contains(pt.region));
        assert(pt.region.base == ptr);
        assert(pt.region.size == PAGE_SIZE);
        assert(other.memory.region_view(pt.region).len() == pt.entries.len());
        assert(other.layer_in_range(layer));
        assert(pt.entries.len() == X86_NUM_ENTRIES);
        assert(other.directories_obey_invariant_at(layer, ptr, pt)) by {
            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                let entry = #[trigger] other.view_at(layer, ptr, i, pt);
                entry.is_Directory() ==> {
                    &&& other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0())
                }
            } by {
                let entry = other.view_at(layer, ptr, i, pt);
                if entry.is_Directory() {
                    assert(self.directories_obey_invariant_at(layer, ptr, pt));
                    assert(self.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0()));
                    self.lemma_inv_at_doesnt_use_ghost_pt(other, layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0());
                    assert(other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i as int].get_Some_0()));
                }
            };
        };
        assert(other.ghost_pt_matches_structure(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_rtrancl(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt));
        assert(other.ghost_pt_region_notin_used_regions(layer, ptr, pt));
        assert(pt.used_regions.subset_of(other.memory.regions()));
        assert(other.entry_addrs_can_use_generic_addr_mask(layer, ptr, pt));
    }

    proof fn lemma_interp_at_aux_doesnt_use_ghost_pt(self, other: Self, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            other.memory === self.memory,
        ensures
            self.interp_at_aux(layer, ptr, base, init, pt)
                == other.interp_at_aux(layer, ptr, base, init, pt)
        decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat
    {
        self.lemma_inv_at_doesnt_use_ghost_pt(other, layer, ptr, pt);
        assert(other.inv_at(layer, ptr, pt));
        if init.len() >= X86_NUM_ENTRIES as nat {
        } else {
            let idx = init.len();
            let entry = self.interp_at_entry(layer, ptr, base, idx, pt);
            let entry_o = other.interp_at_entry(layer, ptr, base, idx, pt);

            assert(entry == entry_o) by {
                match self.view_at(layer, ptr, idx, pt) {
                    GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                        let entry_base = x86_arch_spec.entry_base(layer, base, idx);
                        self.lemma_interp_at_aux_doesnt_use_ghost_pt(other, layer + 1, dir_addr, entry_base, seq![], pt.entries[idx as int].get_Some_0());
                    },
                    GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } => { },
                    GhostPageDirectoryEntry::Empty => { },
                }
            };
            self.lemma_interp_at_aux_doesnt_use_ghost_pt(other, layer, ptr, base, init.push(entry), pt);
        }
    }

    pub fn map_frame(&mut self, vaddr: usize, pte: PageTableEntryExec) -> (res: MapResult)
        requires
            old(self).inv(),
            old(self).interp().inv(),
            old(self).memory.inv(),
            old(self).memory.alloc_available_pages() >= 3,
            old(self).accepted_mapping(vaddr as nat, pte@),
            old(self).interp().accepted_mapping(vaddr as nat, pte@),
            vaddr < MAX_BASE,
        ensures
            self.inv(),
            self.interp().inv(),
            self.ghost_pt@.region === old(self).ghost_pt@.region,
            // Refinement of l1
            match res {
                MapResult::Ok => {
                    Ok(self.interp()) === old(self).interp().map_frame(vaddr as nat, pte@)
                },
                MapResult::ErrOverlap =>
                    Err(self.interp()) === old(self).interp().map_frame(vaddr as nat, pte@),
            },
            // Refinement of l0
            match res {
                MapResult::Ok => {
                    Ok(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr as nat, pte@)
                },
                MapResult::ErrOverlap =>
                    Err(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr as nat, pte@),
            },
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        match self.map_frame_aux(0, cr3.base, 0, vaddr, pte, Ghost(self.ghost_pt@)) {
            Ok(res) => {
                let pt_res: Ghost<PTDir> = Ghost(res@.0);
                let new_regions: Ghost<Set<MemRegion>> = Ghost(res@.1);
                assert(self.inv_at(0, cr3.base, pt_res@));
                let self_before_pt_update: Ghost<Self> = Ghost(*self);
                self.ghost_pt = pt_res;
                proof {
                    self_before_pt_update@.lemma_inv_at_doesnt_use_ghost_pt(*self, 0, cr3.base, pt_res@);
                    assert(self.inv_at(0, cr3.base, pt_res@));
                    self_before_pt_update@.lemma_interp_at_aux_doesnt_use_ghost_pt(*self, 0, cr3.base, 0, seq![], pt_res@);
                    assert(self.interp_at(0, cr3.base, 0, self.ghost_pt@) === self_before_pt_update@.interp_at(0, cr3.base, 0, pt_res@));
                    assert(cr3 === self.memory.cr3_spec());
                    assert(self.ghost_pt@.region === cr3@);
                    assert(self.inv_at(0, cr3.base, self.ghost_pt@));
                    assert(self.inv());
                    old(self).interp().lemma_map_frame_preserves_inv(vaddr as nat, pte@);
                    assert(Ok(self.interp()) === old(self).interp().map_frame(vaddr as nat, pte@));
                    old(self).interp().lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
                    assert(Ok(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr as nat, pte@));
                    assert(self.interp().inv());
                }
                MapResult::Ok
            },
            Err(e) => {
                proof {
                    old(self).interp().lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
                }
                MapResult::ErrOverlap
            },
        }
    }

    fn is_directory_empty(&self, layer: usize, ptr: usize, Ghost(pt): Ghost<PTDir>) -> (res: bool)
        requires
            self.inv_at(layer as nat, ptr, pt),
        ensures
            res === self.empty_at(layer as nat, ptr, pt)
    {
        assert(self.directories_obey_invariant_at(layer as nat, ptr, pt));
        let mut idx = 0;
        let num_entries = x86_arch_exec().num_entries(layer);
        while idx < num_entries
            invariant
                num_entries == X86_NUM_ENTRIES,
                self.inv_at(layer as nat, ptr, pt),
                forall|i: nat| i < idx ==> self.view_at(layer as nat, ptr, i, pt).is_Empty(),
        {
            let entry = self.entry_at(layer, ptr, idx, Ghost(pt));
            if entry.is_mapping() {
                assert(!self.view_at(layer as nat, ptr, idx as nat, pt).is_Empty());
                assert(!self.empty_at(layer as nat, ptr, pt));
                return false;
            }
            idx = idx + 1;
        }
        true
    }

    fn unmap_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: Ghost<PTDir>)
        -> (res: Result<Ghost<(PTDir,Set<MemRegion>)>,()>)
        requires
            old(self).inv_at(layer as nat, ptr, pt@),
            old(self).interp_at(layer as nat, ptr, base as nat, pt@).inv(),
            old(self).memory.inv(),
            old(self).interp_at(layer as nat, ptr, base as nat, pt@).accepted_unmap(vaddr as nat),
            base <= vaddr < MAX_BASE,
        ensures
            match res {
                Ok(resv) => {
                    let (pt_res, removed_regions) = resv@;
                    // We return the regions that we removed
                    &&& old(self).memory.regions() === self.memory.regions().union(removed_regions)
                    &&& pt@.used_regions === pt_res.used_regions.union(removed_regions)
                    // and only those we removed
                    &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] self.memory.regions().contains(r)))
                    &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] pt_res.used_regions.contains(r)))
                    // Invariant preserved
                    &&& self.inv_at(layer as nat, ptr, pt_res)
                    // We only touch regions in pt.used_regions
                    &&& (forall|r: MemRegion| !(#[trigger] pt_res.used_regions.contains(r))
                        ==> self.memory.region_view(r) === old(self).memory.region_view(r))
                    &&& pt_res.region === pt@.region
                },
                Err(e) => {
                    // If error, unchanged
                    &&& self === old(self)
                },
            },
            // Refinement of l1
            match res {
                Ok(resv) => {
                    let (pt_res, removed_regions) = resv@;
                    Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat)
                },
                Err(e) =>
                    Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat),
            },
            self.memory.cr3_spec() == old(self).memory.cr3_spec(),
        // decreases X86_NUM_LAYERS - layer
    {
        proof { self.lemma_interp_at_facts(layer as nat, ptr, base as nat, pt@); }
        let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
        proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
        let entry = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = Ghost(self.interp_at(layer as nat, ptr, base as nat, pt@));
        proof {
            interp@.lemma_unmap_structure_assertions(vaddr as nat, idx as nat);
            interp@.lemma_unmap_refines_unmap(vaddr as nat);
        }
        let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                let dir_addr = entry.address() as usize;
                assert(pt@.entries[idx as int].is_Some());
                let dir_pt: Ghost<PTDir> = Ghost(pt@.entries.index(idx as int).get_Some_0());
                assert(self.directories_obey_invariant_at(layer as nat, ptr, pt@));
                assert(forall|r: MemRegion| #![auto] pt@.entries[idx as int].get_Some_0().used_regions.contains(r) ==> pt@.used_regions.contains(r));
                match self.unmap_aux(layer + 1, dir_addr, entry_base, vaddr, dir_pt) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                        let removed_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);

                        assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt_res@));
                        assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@))
                               === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt@).unmap(vaddr as nat));
                        assert(idx < pt@.entries.len());
                        assert(!pt@.entries[idx as int].get_Some_0().used_regions.contains(pt@.region));
                        assert(!removed_regions@.contains(pt@.region));
                        assert(!dir_pt_res@.used_regions.contains(pt@.region));
                        assert(old(self).memory.regions() === self.memory.regions().union(removed_regions@));

                        if self.is_directory_empty(layer + 1, dir_addr, dir_pt_res) {
                            let self_with_empty: Ghost<Self> = Ghost(*self);
                            let pt_with_empty: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region:       pt@.region,
                                    entries:      pt@.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions,
                                });
                            self.memory.write(ptr, idx, Ghost(pt@.region), 0u64);
                            self.memory.dealloc_page(MemRegionExec { base: dir_addr, size: PAGE_SIZE, });

                            let removed_regions: Ghost<Set<MemRegion>> = Ghost(removed_regions@.insert(dir_pt_res@.region));
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx as int, None),
                                    used_regions: pt@.used_regions.difference(removed_regions@),
                                });
                            let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));
                            proof {
                                assert(pt_res@.region === pt@.region);
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt@.entries[i as int]);
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.view_at(layer as nat, ptr, i, pt_res@) == old(self).view_at(layer as nat, ptr, i, pt@));
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.entry_at_spec(layer as nat, ptr, i, pt_res@) == old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt@.entries[idx as int].get_Some_0().used_regions.contains(r));

                                self.entry_at_spec(layer as nat, ptr, idx as nat, pt_res@).lemma_zero_entry_facts();

                                assert(self.inv_at(layer as nat, ptr, pt_res@)) by {
                                    assert(self.directories_obey_invariant_at(layer as nat, ptr, pt_res@)) by {
                                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                            let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                            entry.is_Directory() ==> {
                                                &&& self.inv_at(layer as nat + 1, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0())
                                            }
                                        } by {
                                            let entry = self.view_at(layer as nat, ptr, i, pt_res@);
                                            if i == idx {
                                            } else {
                                                if entry.is_Directory() {
                                                    old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0());
                                                }
                                            }
                                        };
                                    };
                                };

                                // postconditions
                                assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] self.memory.regions().contains(r))));
                                assert_sets_equal!(old(self).memory.regions(), self.memory.regions().union(removed_regions@));
                                assert_sets_equal!(pt@.used_regions, pt_res@.used_regions.union(removed_regions@));
                                assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                                // unstable
                                assume(forall|r: MemRegion| !(#[trigger] pt_res@.used_regions.contains(r))
                                       ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                                assert(self.memory.cr3_spec() == old(self).memory.cr3_spec());

                                // Refinement
                                assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat)) by {
                                    self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_res@);
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES
                                        implies
                                        #[trigger] self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int] ==
                                        old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                                    {
                                        if i == idx {
                                            self_with_empty@.lemma_empty_at_implies_interp_at_empty((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@);
                                            assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[idx as int] ==
                                                   old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                        } else {
                                            old(self).lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt@, pt_res@);
                                            assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int] ==
                                                   old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                        }
                                    }

                                    assert_seqs_equal!(
                                        self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries,
                                        old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries);
                                };
                            }
                            Ok(res)
                        } else {
                            let pt_res: Ghost<PTDir> = Ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx as int, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions.difference(removed_regions@),
                                });
                            let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));

                            proof {
                                assert(pt_res@.region === pt@.region);
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt@.entries[i as int]);
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.view_at(layer as nat, ptr, i, pt_res@) == old(self).view_at(layer as nat, ptr, i, pt@));
                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.entry_at_spec(layer as nat, ptr, i, pt_res@) == old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                                assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt@.entries[idx as int].get_Some_0().used_regions.contains(r));

                                assert(self.inv_at(layer as nat, ptr, pt_res@)) by {
                                    assert(self.directories_obey_invariant_at(layer as nat, ptr, pt_res@)) by {
                                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                            let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt_res@);
                                            entry.is_Directory() ==> {
                                                &&& self.inv_at(layer as nat + 1, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0())
                                            }
                                        } by {
                                            let entry = self.view_at(layer as nat, ptr, i, pt_res@);
                                            if i == idx {
                                            } else {
                                                if entry.is_Directory() {
                                                    old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i as int].get_Some_0());
                                                }
                                            }
                                        };
                                    };
                                };

                                // postconditions
                                assert_sets_equal!(old(self).memory.regions(), self.memory.regions().union(removed_regions@));
                                assert_sets_equal!(pt@.used_regions, pt_res@.used_regions.union(removed_regions@));
                                // unstable
                                assert(forall|r: MemRegion| !(#[trigger] pt_res@.used_regions.contains(r))
                                       ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                                assert(pt_res@.region === pt@.region);
                                assert(self.memory.cr3_spec() == old(self).memory.cr3_spec());
                                // Refinement
                                assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt_res@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat)) by {
                                    self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt_res@);
                                    assert forall|i: nat|
                                        i < X86_NUM_ENTRIES
                                        implies
                                        #[trigger] self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int] ==
                                        old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                                    {
                                        if i == idx {
                                            assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[idx as int]
                                                   == l1::NodeEntry::Directory(self.interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@)));
                                            assert(old(self).interp_at((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt@).unmap(vaddr as nat).is_Ok());
                                            assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).entries[idx as int] == old(self).interp_at_entry(layer as nat, ptr, base as nat, idx as nat, pt@));

                                            self.lemma_not_empty_at_implies_interp_at_not_empty((layer + 1) as nat, dir_addr, entry_base as nat, dir_pt_res@);
                                            assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[idx as int] ==
                                                   old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                        } else {
                                            old(self).lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt@, pt_res@);
                                            assert(self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries[i as int] ==
                                                   old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                        }
                                    }

                                    assert_seqs_equal!(
                                        self.interp_at(layer as nat, ptr, base as nat, pt_res@).entries,
                                        old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries);
                                };
                            }
                            Ok(res)
                        }

                    },
                    Err(e) => {
                        assert(self === old(self));
                        assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat));
                        Err(e)
                    },
                }
            } else {
                if aligned_exec(vaddr, x86_arch_exec().entry_size(layer)) {
                    self.memory.write(ptr, idx, Ghost(pt@.region), 0u64);

                    let removed_regions: Ghost<Set<MemRegion>> = Ghost(Set::empty());
                    let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt@, removed_regions@));

                    proof {
                        assert(self.memory.region_view(pt@.region) === old(self).memory.region_view(pt@.region).update(idx as int, 0));
                        assert(self.memory.spec_read(idx as nat, pt@.region) == 0);
                        let new_entry = self.entry_at_spec(layer as nat, ptr, idx as nat, pt@);
                        new_entry.lemma_zero_entry_facts();
                        assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.entry_at_spec(layer as nat, ptr, i, pt@) == old(self).entry_at_spec(layer as nat, ptr, i, pt@));
                        assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> self.view_at(layer as nat, ptr, i, pt@) == old(self).view_at(layer as nat, ptr, i, pt@));

                        assert(self.inv_at(layer as nat, ptr, pt@)) by {
                            assert(self.directories_obey_invariant_at(layer as nat, ptr, pt@)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] self.view_at(layer as nat, ptr, i, pt@);
                                    entry.is_Directory() ==> {
                                        &&& self.inv_at(layer as nat + 1, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0())
                                    }
                                } by {
                                    let entry = self.view_at(layer as nat, ptr, i, pt@);
                                    if i == idx {
                                    } else {
                                        if entry.is_Directory() {
                                            assert(old(self).directories_obey_invariant_at(layer as nat, ptr, pt@));
                                            old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0());
                                            assert(self.inv_at(layer as nat + 1, entry.get_Directory_addr(), pt@.entries[i as int].get_Some_0()));
                                        }
                                    }
                                };
                            };
                        };

                        // postconditions
                        assert_sets_equal!(old(self).memory.regions(), self.memory.regions().union(removed_regions@));
                        assert_sets_equal!(pt@.used_regions, pt@.used_regions.union(removed_regions@));

                        // Refinement
                        assert(Ok(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat)) by {
                            self.lemma_interp_at_aux_facts(layer as nat, ptr, base as nat, seq![], pt@);
                            assert(self.interp_at(layer as nat, ptr, base as nat, pt@).entries.len() == X86_NUM_ENTRIES);
                            assert(old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries.len() == X86_NUM_ENTRIES);

                            assert forall|i: nat|
                                i < X86_NUM_ENTRIES
                                implies
                                #[trigger] self.interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int] ==
                                old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                            {
                                if i == idx {
                                } else {
                                    old(self).lemma_interp_at_entry_different_memory(*self, layer as nat, ptr, base as nat, i, pt@, pt@);
                                    assert(self.interp_at(layer as nat, ptr, base as nat, pt@).entries[i as int] ==
                                           old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                }
                            }

                            assert_seqs_equal!(
                                self.interp_at(layer as nat, ptr, base as nat, pt@).entries,
                                old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat).get_Ok_0().entries);
                        };
                    }
                    Ok(res)

                } else {
                    assert(self === old(self));
                    assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat));
                    Err(())
                }
            }
        } else {
            assert(self === old(self));
            assert(Err(self.interp_at(layer as nat, ptr, base as nat, pt@)) === old(self).interp_at(layer as nat, ptr, base as nat, pt@).unmap(vaddr as nat));
            Err(())
        }
    }

    pub fn unmap(&mut self, vaddr: usize) -> (res: UnmapResult)
        requires
            old(self).inv(),
            old(self).interp().inv(),
            old(self).memory.inv(),
            old(self).interp().accepted_unmap(vaddr as nat),
            vaddr < MAX_BASE,
        ensures
            self.inv(),
            self.interp().inv(),
            self.ghost_pt@.region === old(self).ghost_pt@.region,
            // Refinement of l1
            match res {
                UnmapResult::Ok => {
                    Ok(self.interp()) === old(self).interp().unmap(vaddr as nat)
                },
                UnmapResult::ErrNoSuchMapping =>
                    Err(self.interp()) === old(self).interp().unmap(vaddr as nat),
            },
            // Refinement of l0
            match res {
                UnmapResult::Ok => {
                    Ok(self.interp().interp()) === old(self).interp().interp().unmap(vaddr as nat)
                },
                UnmapResult::ErrNoSuchMapping =>
                    Err(self.interp().interp()) === old(self).interp().interp().unmap(vaddr as nat),
            },
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        match self.unmap_aux(0, cr3.base, 0, vaddr, Ghost(self.ghost_pt@)) {
            Ok(res) => {
                let pt_res: Ghost<PTDir> = Ghost(res@.0);
                assert(self.inv_at(0, cr3.base, pt_res@));
                let self_before_pt_update: Ghost<Self> = Ghost(*self);
                self.ghost_pt = pt_res;
                proof {
                    self_before_pt_update@.lemma_inv_at_doesnt_use_ghost_pt(*self, 0, cr3.base, pt_res@);
                    assert(self.inv_at(0, cr3.base, pt_res@));
                    self_before_pt_update@.lemma_interp_at_aux_doesnt_use_ghost_pt(*self, 0, cr3.base, 0, seq![], pt_res@);
                    assert(self.interp_at(0, cr3.base, 0, self.ghost_pt@) === self_before_pt_update@.interp_at(0, cr3.base, 0, pt_res@));
                    assert(cr3 === self.memory.cr3_spec());
                    assert(self.ghost_pt@.region === cr3@);
                    assert(self.inv_at(0, cr3.base, self.ghost_pt@));
                    assert(self.inv());
                    old(self).interp().lemma_unmap_preserves_inv(vaddr as nat);
                    assert(Ok(self.interp()) === old(self).interp().unmap(vaddr as nat));
                    old(self).interp().lemma_unmap_refines_unmap(vaddr as nat);
                    assert(Ok(self.interp().interp()) === old(self).interp().interp().unmap(vaddr as nat));
                    assert(self.interp().inv());
                }
                UnmapResult::Ok
            },
            Err(e) => {
                proof {
                    old(self).interp().lemma_unmap_refines_unmap(vaddr as nat);
                }
                UnmapResult::ErrNoSuchMapping
            },
        }
    }
}

pub proof fn lemma_set_union_empty_equals_set<T>(s: Set<T>)
    ensures
        s.union(set![]) === s
{
    assert_sets_equal!(s.union(set![]), s);
}


}
