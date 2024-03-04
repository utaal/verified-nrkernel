use vstd::prelude::*;
use vstd::assert_by_contradiction;

use crate::definitions_t::{ MemRegion, MemRegionExec, PageTableEntry, PageTableEntryExec, Flags,
between, aligned, new_seq, x86_arch_exec, x86_arch_spec, axiom_max_phyaddr_width_facts, MAX_BASE,
WORD_SIZE, PAGE_SIZE, MAX_PHYADDR, MAX_PHYADDR_WIDTH, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
X86_NUM_LAYERS, X86_NUM_ENTRIES, bit, bitmask_inc };
use crate::definitions_u::{ lemma_new_seq, aligned_exec, permissive_flags};
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::impl_u::indexing;
use crate::spec_t::mem;
use crate::spec_t::hardware::{PageDirectoryEntry,GhostPageDirectoryEntry, MASK_FLAG_P,
MASK_FLAG_RW, MASK_FLAG_US, MASK_FLAG_PWT, MASK_FLAG_PCD, MASK_FLAG_XD, MASK_ADDR,
MASK_PG_FLAG_PAT, MASK_L1_PG_FLAG_PS, MASK_DIR_ADDR, MASK_L1_PG_ADDR, MASK_L2_PG_ADDR,
MASK_L3_PG_ADDR};
use crate::extra::{ self, result_map_ok };


verus! {

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
            extra::aligned_transitive(addr as nat, L1_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            assert(aligned(L2_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by(nonlinear_arith);
            extra::aligned_transitive(addr as nat, L2_ENTRY_SIZE as nat, PAGE_SIZE as nat);
            lemma_page_aligned_implies_mask_dir_addr_is_identity();
        }
    };
    assert(addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr)) by {
        if addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) {
            assert(aligned(L3_ENTRY_SIZE as nat, PAGE_SIZE as nat)) by(nonlinear_arith);
            extra::aligned_transitive(addr as nat, L3_ENTRY_SIZE as nat, PAGE_SIZE as nat);
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
    // PAT flag is set to zero for huge pages and super pages
    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@.is_Page() && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@.is_Page() && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }

    pub proof fn lemma_addr_mask_when_hp_pat_is_zero(self)
        requires self.hp_pat_is_zero() && self.all_mb0_bits_are_zero() && self@.is_Page()
        ensures
            self.layer == 1 ==> self.entry & MASK_L1_PG_ADDR == self.entry & MASK_ADDR,
            self.layer == 2 ==> self.entry & MASK_L2_PG_ADDR == self.entry & MASK_ADDR
    {
        let e = self.entry; let mw = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        reveal(PageDirectoryEntry::all_mb0_bits_are_zero);
        if self.layer() == 1 {
            assert(e & bitmask_inc!(12u64, mw - 1) == e & bitmask_inc!(30u64, mw - 1)) by (bit_vector)
                requires e & bit!(12u64) == 0, e & bitmask_inc!(13u64,29u64) == 0, 32 <= mw <= 52;
        } else if self.layer() == 2 {
            assert(e & bitmask_inc!(12u64, mw - 1) == e & bitmask_inc!(21u64, mw - 1)) by (bit_vector)
                requires e & bit!(12u64) == 0, e & bitmask_inc!(13u64,20u64) == 0, 32 <= mw <= 52;
        }
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
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS as u64 } else { 0 };
        let or3 = if is_writable           { MASK_FLAG_RW as u64 }       else { 0 };
        let or4 = if is_supervisor         { 0 }                         else { MASK_FLAG_US as u64 };
        let or5 = if is_writethrough       { MASK_FLAG_PWT as u64 }      else { 0 };
        let or6 = if disable_cache         { MASK_FLAG_PCD as u64 }      else { 0 };
        let or7 = if disable_execute       { MASK_FLAG_XD as u64 }       else { 0 };
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
               &&& (is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0)
               &&& (is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0)

            }),
    {
        let or1 = MASK_FLAG_P;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS as u64 }  else { 0 };
        let or3 = if is_writable           { MASK_FLAG_RW as u64 }        else { 0 };
        let or4 = if is_supervisor         { 0 }                          else { MASK_FLAG_US as u64 };
        let or5 = if is_writethrough       { MASK_FLAG_PWT as u64 }       else { 0 };
        let or6 = if disable_cache         { MASK_FLAG_PCD as u64 }       else { 0 };
        let or7 = if disable_execute       { MASK_FLAG_XD as u64 }        else { 0 };
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: u64 = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        assert(forall|a:u64,x:u64| x < 64 && (a & bit!(x) == 0) ==> a & bit!(x) != bit!(x)) by (bit_vector);
        assert(forall|a:u64| #![auto] a == a | 0) by (bit_vector);
        assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12u64, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;

        assert(forall|a:u64,i:u64| #![auto] i < 12 ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12u64, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:u64,i:u64| #![auto] i < 64 ==> a & bit!(i) == 0 ==> (a | bit!(i)) & bit!(i) == bit!(i)) by (bit_vector);
        assert(forall|a:u64,i:u64,j:u64| #![auto] i != j ==> a & bit!(i) == (a | bit!(j)) & bit!(i)) by (bit_vector);
        assert({
            &&& is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0
            &&& is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0
        }) by {
            if is_page && layer == 1 {
                assert(address & bit!(12u64) == 0) by (bit_vector)
                    requires address & bitmask_inc!(30u64, sub(mw, 1)) == address;
            }
            if is_page && layer == 2 {
                assert(address & bit!(12u64) == 0) by (bit_vector)
                    requires address & bitmask_inc!(21u64, sub(mw, 1)) == address;
            }
        };
    }

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer as nat, pte.frame.base as u64, true),
            pte.frame.base as u64 & MASK_ADDR == pte.frame.base as u64,
        ensures
            r.all_mb0_bits_are_zero(),
            r.hp_pat_is_zero(),
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
            r.hp_pat_is_zero(),
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
            r.hp_pat_is_zero(),
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
            if is_page { e.lemma_addr_mask_when_hp_pat_is_zero(); }
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
            self.hp_pat_is_zero(),
            self.all_mb0_bits_are_zero(),
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
                GhostPageDirectoryEntry::Page { addr, .. }      => self.lemma_addr_mask_when_hp_pat_is_zero(),
                GhostPageDirectoryEntry::Directory { addr, .. } => { },
                GhostPageDirectoryEntry::Empty                  => { },
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

// Page table methods are in a separate module for namespacing, since we can't use a struct + impl
// (To use a struct we'd have to keep a &mut reference to the memory in the struct, which Verus
// doesn't support. Or we keep an owned copy but then can't have an external interface that mutably
// borrows a memory.)
pub mod PT {

use super::*;

pub open spec(checked) fn inv(mem: &mem::PageTableMemory, pt: PTDir) -> bool {
    &&& pt.region == mem.cr3_spec()@
    &&& inv_at(mem, pt, 0, mem.cr3_spec().base)
}

/// Get the view of the entry at address ptr + i * WORD_SIZE
pub open spec fn entry_at_spec(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, i: nat) -> PageDirectoryEntry {
    PageDirectoryEntry {
        entry: mem.spec_read(i, pt.region),
        layer: Ghost(layer),
    }
}

/// Get the view of the entry at address ptr + i * WORD_SIZE
pub open spec fn view_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, i: nat) -> GhostPageDirectoryEntry {
    PageDirectoryEntry {
        entry: mem.spec_read(i, pt.region),
        layer: Ghost(layer),
    }@
}

/// Get the entry at address ptr + i * WORD_SIZE
fn entry_at(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, i: usize) -> (res: PageDirectoryEntry)
    requires
        i < 512,
        inv_at(mem, pt, layer as nat, ptr),
    ensures
        res.layer@ == layer as nat,
        res@ === view_at(mem, pt, layer as nat, ptr, i as nat),
        res == entry_at_spec(mem, pt, layer as nat, ptr, i as nat),
        res.hp_pat_is_zero(),
        (res@.is_Page() ==> 0 < res.layer()),
{
    assert(aligned((ptr + i * WORD_SIZE) as nat, 8)) by {
        assert(inv_at(mem, pt, layer as nat, ptr));
        assert(ptr % PAGE_SIZE == 0);
    };
    // triggering
    proof { let _ = entry_at_spec(mem, pt, layer as nat, ptr, i as nat); }
    PageDirectoryEntry {
        entry: mem.read(ptr, i, Ghost(pt.region)),
        layer: Ghost(layer as nat),
    }
}

pub open spec fn ghost_pt_matches_structure(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![trigger pt.entries[i as int], view_at(mem, pt, layer, ptr, i)]
    i < X86_NUM_ENTRIES ==> {
        let entry = view_at(mem, pt, layer, ptr, i);
        entry.is_Directory() == pt.entries[i as int].is_Some()
    }
}

pub open spec fn directories_obey_invariant_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer, 0nat
        when layer_in_range(layer)
{
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        let entry = #[trigger] view_at(mem, pt, layer, ptr, i);
        entry.is_Directory() ==> {
            &&& inv_at(mem, pt.entries[i as int].get_Some_0(), layer + 1, entry.get_Directory_addr())
        }
    }
}

pub open spec fn empty_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==> view_at(mem, pt, layer, ptr, i).is_Empty()
}

pub open spec(checked) fn layer_in_range(layer: nat) -> bool {
    layer < X86_NUM_LAYERS
}

pub open spec(checked) fn inv_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer
{
    &&& ptr % PAGE_SIZE == 0
    &&& mem.inv()
    &&& mem.regions().contains(pt.region)
    &&& pt.region.base == ptr
    &&& pt.region.size == PAGE_SIZE
    &&& mem.region_view(pt.region).len() == pt.entries.len()
    &&& layer_in_range(layer)
    &&& pt.entries.len() == X86_NUM_ENTRIES
    &&& directories_obey_invariant_at(mem, pt, layer, ptr)
    &&& directories_have_flags(mem, pt, layer, ptr)
    &&& ghost_pt_matches_structure(mem, pt, layer, ptr)
    &&& ghost_pt_used_regions_rtrancl(mem, pt, layer, ptr)
    &&& ghost_pt_used_regions_pairwise_disjoint(mem, pt, layer, ptr)
    &&& ghost_pt_region_notin_used_regions(mem, pt, layer, ptr)
    &&& pt.used_regions.subset_of(mem.regions())
    &&& hp_pat_is_zero(mem, pt, layer, ptr)
    &&& entry_mb0_bits_are_zero(mem, pt, layer, ptr)
}

pub open spec fn directories_have_flags(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        let entry = #[trigger] view_at(mem, pt, layer, ptr, i);
        entry.is_Directory() ==> entry.get_Directory_flag_RW() && entry.get_Directory_flag_US() && !entry.get_Directory_flag_XD()
    }
}

pub open spec fn entry_mb0_bits_are_zero(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==>
        (#[trigger] entry_at_spec(mem, pt, layer, ptr, i)).all_mb0_bits_are_zero()
}

/// Entries for super pages and huge pages use bit 12 to denote the PAT flag. We always set that
/// flag to zero, which allows us to always use the same mask to get the address.
pub open spec fn hp_pat_is_zero(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![auto] i < X86_NUM_ENTRIES ==> entry_at_spec(mem, pt, layer, ptr, i).hp_pat_is_zero()
}

// TODO: should I move some of these ghost_pt things in a invariant defined on PTDir?
pub open spec fn ghost_pt_used_regions_pairwise_disjoint(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat, j: nat, r: MemRegion|
        i != j &&
        i < pt.entries.len() && pt.entries[i as int].is_Some() &&
        #[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(r) &&
        j < pt.entries.len() && pt.entries[j as int].is_Some()
        ==> !(#[trigger] pt.entries[j as int].get_Some_0().used_regions.contains(r))
}

// TODO: this may be implied by the other ones
pub open spec fn ghost_pt_region_notin_used_regions(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat|
        i < pt.entries.len() && pt.entries[i as int].is_Some()
        ==> !(#[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(pt.region))
}

pub open spec fn ghost_pt_used_regions_rtrancl(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize) -> bool {
    // reflexive
    &&& pt.used_regions.contains(pt.region)
    // transitive
    &&& forall|i: nat, r: MemRegion| #![trigger pt.entries[i as int].get_Some_0().used_regions.contains(r), pt.used_regions.contains(r)]
            i < pt.entries.len() && pt.entries[i as int].is_Some() &&
            pt.entries[i as int].get_Some_0().used_regions.contains(r)
            ==> pt.used_regions.contains(r)
}

pub open spec fn interp_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat) -> l1::Directory
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES, 2nat
{
    decreases_when(inv_at(mem, pt, layer, ptr));
    l1::Directory {
        entries: interp_at_aux(mem, pt, layer, ptr, base_vaddr, seq![]),
        layer: layer,
        base_vaddr,
        arch: x86_arch_spec,
        // We don't have to check the flags because we know (from the invariant) that all
        // directories have these flags set.
        flags: permissive_flags,
    }
}

pub open spec fn interp_at_entry(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, idx: nat) -> l1::NodeEntry
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - idx, 0nat
{
    decreases_when(inv_at(mem, pt, layer, ptr));
    match view_at(mem, pt, layer, ptr, idx) {
        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
            let entry_base = x86_arch_spec.entry_base(layer, base_vaddr, idx);
            l1::NodeEntry::Directory(interp_at(mem, pt.entries[idx as int].get_Some_0(), layer + 1, dir_addr, entry_base))
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

pub open spec fn interp_at_aux(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>) -> Seq<l1::NodeEntry>
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat
        when inv_at(mem, pt, layer, ptr)
{
    if init.len() >= X86_NUM_ENTRIES {
        init
    } else {
        let entry = interp_at_entry(mem, pt, layer, ptr, base_vaddr, init.len());
        interp_at_aux(mem, pt, layer, ptr, base_vaddr, init.push(entry))
    }
}

pub open spec fn interp(mem: &mem::PageTableMemory, pt: PTDir) -> l1::Directory {
    interp_at(mem, pt, 0, mem.cr3_spec().base, 0)
}

proof fn lemma_inv_at_different_memory(mem1: &mem::PageTableMemory, mem2: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize)
    requires
        inv_at(mem1, pt, layer, ptr),
        forall|r: MemRegion| pt.used_regions.contains(r)
            ==> #[trigger] mem1.region_view(r) === mem2.region_view(r),
        // Some parts of mem2's invariant that we should already know
        mem2.inv(),
        mem2.regions().contains(pt.region),
        pt.used_regions.subset_of(mem2.regions()),
    ensures inv_at(mem2, pt, layer, ptr),
    decreases X86_NUM_LAYERS - layer
{
    assert forall|i: nat| i < X86_NUM_ENTRIES implies
        view_at(mem2, pt, layer, ptr, i) == view_at(mem1, pt, layer, ptr, i) by { };
    assert forall|i: nat| i < X86_NUM_ENTRIES implies
        entry_at_spec(mem2, pt, layer, ptr, i) == entry_at_spec(mem1, pt, layer, ptr, i) by { };

    // Prove directories_obey_invariant_at(mem2, pt, layer, ptr)
    assert forall|i: nat|
    i < X86_NUM_ENTRIES implies {
        let entry = #[trigger] view_at(mem2, pt, layer, ptr, i);
        entry.is_Directory() ==> inv_at(mem2, pt.entries[i as int].get_Some_0(), layer + 1, entry.get_Directory_addr())
    } by {
        let entry = view_at(mem2, pt, layer, ptr, i);
        if entry.is_Directory() {
            assert(directories_obey_invariant_at(mem1, pt, layer, ptr));
            lemma_inv_at_different_memory(mem1, mem2, pt.entries[i as int].get_Some_0(), layer + 1, entry.get_Directory_addr());
        }
    };
}

proof fn lemma_interp_at_entry_different_memory(mem1: &mem::PageTableMemory, pt1: PTDir, mem2: &mem::PageTableMemory, pt2: PTDir, layer: nat, ptr: usize, base: nat, idx: nat)
    requires
        idx < X86_NUM_ENTRIES,
        pt2.region == pt1.region,
        pt2.entries[idx as int] == pt1.entries[idx as int],
        inv_at(mem1, pt1, layer, ptr),
        inv_at(mem2, pt2, layer, ptr),
        view_at(mem1, pt1, layer, ptr, idx) == view_at(mem2, pt2, layer, ptr, idx),
        pt2.entries[idx as int].is_Some() ==> (forall|r: MemRegion| pt2.entries[idx as int].get_Some_0().used_regions.contains(r)
            ==> #[trigger] mem1.region_view(r) == mem2.region_view(r)),
    ensures
        interp_at_entry(mem1, pt1, layer, ptr, base, idx) == interp_at_entry(mem2, pt2, layer, ptr, base, idx),
    decreases X86_NUM_LAYERS - layer
{
    match view_at(mem1, pt1, layer, ptr, idx) {
        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
            let e_base = x86_arch_spec.entry_base(layer, base, idx);
            let dir_pt = pt1.entries[idx as int].get_Some_0();
            assert(directories_obey_invariant_at(mem1, pt1, layer, ptr));
            assert(directories_obey_invariant_at(mem2, pt2, layer, ptr));
            lemma_interp_at_aux_facts(mem1, dir_pt, layer + 1, dir_addr, e_base, seq![]);
            lemma_interp_at_aux_facts(mem2, dir_pt, layer + 1, dir_addr, e_base, seq![]);

            assert forall|i: nat| i < X86_NUM_ENTRIES implies
                interp_at_entry(mem1, dir_pt, layer + 1, dir_addr, e_base, i)
                    == interp_at_entry(mem2, dir_pt, layer + 1, dir_addr, e_base, i)
                && #[trigger] interp_at(mem1, dir_pt, layer + 1, dir_addr, e_base).entries[i as int]
                    == interp_at(mem2, dir_pt, layer + 1, dir_addr, e_base).entries[i as int] by
            {
                lemma_interp_at_entry_different_memory(mem1, dir_pt, mem2, dir_pt, layer + 1, dir_addr, e_base, i);
            };
            assert(interp_at(mem1, dir_pt, layer + 1, dir_addr, e_base).entries
                   =~= interp_at(mem2, dir_pt, layer + 1, dir_addr, e_base).entries);
        },
        _ => (),
    }
}

pub proof fn lemma_interp_at_facts(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        interp_at(mem, pt, layer, ptr, base_vaddr).inv(),
    ensures
        interp_at(mem, pt, layer, ptr, base_vaddr).base_vaddr     == base_vaddr,
        interp_at(mem, pt, layer, ptr, base_vaddr).upper_vaddr()  == x86_arch_spec.upper_vaddr(layer, base_vaddr),
        interp_at(mem, pt, layer, ptr, base_vaddr).interp().lower == base_vaddr,
        interp_at(mem, pt, layer, ptr, base_vaddr).interp().upper == x86_arch_spec.upper_vaddr(layer, base_vaddr),
        ({ let res = interp_at(mem, pt, layer, ptr, base_vaddr);
           forall|j: nat| j < res.entries.len() ==> res.entries[j as int] === #[trigger] interp_at_entry(mem, pt, layer, ptr, base_vaddr, j)
        }),
{
    lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, seq![]);
    let res = interp_at(mem, pt, layer, ptr, base_vaddr);
    assert(res.pages_match_entry_size());
    assert(res.directories_are_in_next_layer());
    assert(res.directories_match_arch());
    assert(res.directories_obey_invariant());
    assert(res.directories_are_nonempty());
    assert(res.frames_aligned());
    res.lemma_inv_implies_interp_inv();
}

pub proof fn lemma_interp_at_facts_entries(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, i: nat)
    requires
        i < 512,
        inv_at(mem, pt, layer, ptr),
        interp_at(mem, pt, layer, ptr, base_vaddr).inv(),
    ensures
        ({ let res = interp_at(mem, pt, layer, ptr, base_vaddr);
            match view_at(mem, pt, layer, ptr, i) {
                GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                    &&& res.entries[i as int].is_Directory()
                    &&& res.entries[i as int].get_Directory_0() == interp_at(mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, dir_addr, x86_arch_spec.entry_base(layer, base_vaddr, i))
                },
                GhostPageDirectoryEntry::Page { addr, .. } => res.entries[i as int].is_Page() && res.entries[i as int].get_Page_0().frame.base == addr,
                GhostPageDirectoryEntry::Empty             => res.entries[i as int].is_Empty(),
            } })
{ lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, seq![]); }

proof fn lemma_interp_at_aux_facts(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>)
    requires inv_at(mem, pt, layer, ptr),
    ensures
        interp_at_aux(mem, pt, layer, ptr, base_vaddr, init).len() == if init.len() > X86_NUM_ENTRIES { init.len() } else { X86_NUM_ENTRIES as nat },
        forall|j: nat| j < init.len() ==> #[trigger] interp_at_aux(mem, pt, layer, ptr, base_vaddr, init)[j as int] == init[j as int],
        ({ let res = interp_at_aux(mem, pt, layer, ptr, base_vaddr, init);
            &&& (forall|j: nat|
                #![trigger res[j as int]]
                init.len() <= j && j < res.len() ==>
                match view_at(mem, pt, layer, ptr, j) {
                    GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                        &&& res[j as int].is_Directory()
                        &&& res[j as int].get_Directory_0() == interp_at(mem, pt.entries[j as int].get_Some_0(), (layer + 1) as nat, dir_addr, x86_arch_spec.entry_base(layer, base_vaddr, j))
                    },
                    GhostPageDirectoryEntry::Page { addr, .. } => res[j as int].is_Page() && res[j as int].get_Page_0().frame.base == addr,
                    GhostPageDirectoryEntry::Empty             => res[j as int].is_Empty(),
                })
            &&& (forall|j: nat| init.len() <= j && j < res.len() ==> res[j as int] == #[trigger] interp_at_entry(mem, pt, layer, ptr, base_vaddr, j))
        }),
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        assert(directories_obey_invariant_at(mem, pt, layer, ptr));
        let entry = interp_at_entry(mem, pt, layer, ptr, base_vaddr, init.len());
        lemma_interp_at_aux_facts(mem, pt, layer, ptr, base_vaddr, init.push(entry));
    }
}

fn resolve_aux(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec), ()>)
    requires
        inv_at(mem, pt, layer as nat, ptr),
        interp_at(mem, pt, layer as nat, ptr, base as nat).inv(),
        interp_at(mem, pt, layer as nat, ptr, base as nat).interp().accepted_resolve(vaddr as nat),
        base <= vaddr < MAX_BASE,
    ensures
        // Refinement of l1
        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp_at(mem, pt, layer as nat, ptr, base as nat).resolve(vaddr as nat),
        // Refinement of l0
        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp_at(mem, pt, layer as nat, ptr, base as nat).interp().resolve(vaddr as nat),
    // decreases X86_NUM_LAYERS - layer
{
    proof { lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat); }
    let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
    proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
    let entry      = entry_at(mem, Ghost(pt), layer, ptr, idx);
    let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
    proof {
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
            assert(pt.entries[idx as int].is_Some());
            let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
            assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
            proof {
                assert(interp@.inv());
                assert(interp@.directories_obey_invariant());
                assert(interp@.entries[idx as int].is_Directory());
                assert(interp@.entries[idx as int].get_Directory_0().inv());
                assert(l1::NodeEntry::Directory(interp_at(mem, dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat)) === interp@.entries[idx as int]);
                assert(inv_at(mem, dir_pt@, (layer + 1) as nat, dir_addr));
            }
            let res = resolve_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr);
            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
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
                assert(interp@.entries[idx as int] === interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat));
            }
            }
            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).0) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.0));
            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.frame) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.1.frame));
            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.flags) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PageTableEntry)| v.1.flags));
            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
            res
        }
    } else {
        assert(entry@.is_Empty());
        assert(interp@.entries[idx as int].is_Empty());
        assert(result_map_ok(Err(()), |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
        Err(())
    }
}

pub fn resolve(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec),()>)
    requires
        inv(mem, pt),
        interp(mem, pt).inv(),
        interp(mem, pt).interp().accepted_resolve(vaddr as nat),
        vaddr < MAX_BASE,
    ensures
        // Refinement of l1
        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(mem, pt).resolve(vaddr as nat),
        // Refinement of l0
        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(mem, pt).interp().resolve(vaddr as nat),
{
    proof { ambient_arith(); }
    let res = resolve_aux(mem, Ghost(pt), 0, mem.cr3().base, 0, vaddr);
    res
}

pub open spec fn accepted_mapping(vaddr: nat, pte: PageTableEntry) -> bool {
    // Can't map pages in PML4, i.e. layer 0
    &&& x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size, 1)
    &&& pte.frame.base <= MAX_PHYADDR
}

fn map_frame_aux(mem: &mut mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, vaddr: usize, pte: PageTableEntryExec)
    -> (res: Result<Ghost<(PTDir,Set<MemRegion>)>,()>)
    requires
        inv_at(&*old(mem), pt, layer as nat, ptr),
        interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
        old(mem).inv(),
        old(mem).alloc_available_pages() >= 3 - layer,
        accepted_mapping(vaddr as nat, pte@),
        interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).accepted_mapping(vaddr as nat, pte@),
        base <= vaddr < MAX_BASE,
    ensures
        match res {
            Ok(resv) => {
                let (pt_res, new_regions) = resv@;
                // We return the regions that we added
                &&& mem.regions() === old(mem).regions().union(new_regions)
                &&& pt_res.used_regions === pt.used_regions.union(new_regions)
                // and only those we added
                &&& new_regions.disjoint(old(mem).regions())
                &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt.used_regions.contains(r)))
                // Invariant preserved
                &&& inv_at(mem, pt_res, layer as nat, ptr)
                // We only touch already allocated regions if they're in pt.used_regions
                &&& (forall|r: MemRegion| !(#[trigger] pt.used_regions.contains(r)) && !(new_regions.contains(r))
                    ==> mem.region_view(r) === old(mem).region_view(r))
                &&& pt_res.region === pt.region
            },
            Err(e) => {
                // If error, unchanged
                &&& mem === old(mem)
            },
        },
        // Refinement of l1
        match res {
            Ok(resv) => {
                let (pt_res, new_regions) = resv@;
                Ok(interp_at(mem, pt_res, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)
            },
            Err(e) =>
                Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@),
        },
        mem.cr3_spec() == old(mem).cr3_spec(),
    // decreases X86_NUM_LAYERS - layer
{
    proof { lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat); }
    let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
    proof {
        assert({
            &&& between(vaddr as nat, x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat), x86_arch_spec.next_entry_base(layer as nat, base as nat, idx as nat))
            &&& aligned(vaddr as nat, x86_arch_spec.entry_size(layer as nat)) ==> vaddr == x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat)
            &&& idx < X86_NUM_ENTRIES }) by
        {
            let es = x86_arch_spec.entry_size(layer as nat);
            assert(aligned(base as nat, es)) by {
                extra::mod_mult_zero_implies_mod_zero(base as nat, es, X86_NUM_ENTRIES as nat);
            };
            indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, es, X86_NUM_ENTRIES as nat);
        };
        lemma_interp_at_facts_entries(&*old(mem), pt, layer as nat, ptr, base as nat, idx as nat);
    }
    let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
    let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
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
                assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                Err(())
            } else {
                let dir_addr = entry.address() as usize;
                assert(pt.entries[idx as int].is_Some());
                let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
                assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
                match map_frame_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr, pte) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                        let new_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);

                        assert(dir_pt_res@.used_regions === dir_pt@.used_regions.union(new_regions@));
                        assert(inv_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr));
                        assert(Ok(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat))
                               === interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@));
                        let pt_res: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                used_regions: pt.used_regions.union(new_regions@),
                            });

                        assert(idx < pt.entries.len());
                        assert(pt_res@.region === pt.region);
                        assert(!new_regions@.contains(pt_res@.region));
                        assert(!dir_pt_res@.used_regions.contains(pt_res@.region));

                        // None of the entries at this level change
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            view_at(mem, pt_res@, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i) by { };
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            entry_at_spec(mem, pt_res@, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i) by { };

                        assert(inv_at(mem, pt_res@, layer as nat, ptr)
                            && Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by
                        {
                            assert forall|i: nat| i < X86_NUM_ENTRIES
                                implies {
                                    let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                    entry.is_Directory() == (#[trigger] pt_res@.entries[i as int]).is_Some()
                                }
                            by {
                                assert(mem.region_view(pt_res@.region) === mem.region_view(pt_res@.region));
                                let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                if i == idx {
                                } else {
                                    assert(pt.entries[i as int] === pt_res@.entries[i as int]);
                                    assert(entry === view_at(&*old(mem), pt, layer as nat, ptr, i));
                                    assert(entry.is_Directory() == pt_res@.entries[i as int].is_Some());
                                }
                            };
                            assert(ghost_pt_matches_structure(mem, pt_res@, layer as nat, ptr));

                            assert(ghost_pt_used_regions_rtrancl(mem, pt_res@, layer as nat, ptr));
                            assert(ghost_pt_region_notin_used_regions(mem, pt_res@, layer as nat, ptr));
                            assert forall|i: nat, j: nat, r: MemRegion|
                                i != j &&
                                i < pt_res@.entries.len() && pt_res@.entries[i as int].is_Some() &&
                                #[trigger] pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) &&
                                j < pt_res@.entries.len() && pt_res@.entries[j as int].is_Some()
                                implies !(#[trigger] pt_res@.entries[j as int].get_Some_0().used_regions.contains(r)) by
                            {
                                assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt, layer as nat, ptr));
                                if j == idx {
                                    assert(pt_res@.entries[j as int].get_Some_0() === dir_pt_res@);
                                    assert(pt_res@.entries[i as int] === pt.entries[i as int]);
                                    if new_regions@.contains(r) {
                                        assert(!dir_pt@.used_regions.contains(r));
                                        assert(!old(mem).regions().contains(r));
                                        assert(!dir_pt_res@.used_regions.contains(r));
                                    } else {
                                        if dir_pt@.used_regions.contains(r) {
                                            assert(pt.used_regions.contains(r));
                                            assert(old(mem).regions().contains(r));
                                            assert(!dir_pt_res@.used_regions.contains(r));
                                        }
                                    }
                                } else {
                                    if i == idx {
                                        assert(pt_res@.entries[i as int].get_Some_0() === dir_pt_res@);
                                        assert(pt_res@.entries[j as int] === pt.entries[j as int]);
                                        if new_regions@.contains(r) {
                                            assert(dir_pt_res@.used_regions.contains(r));
                                            assert(!dir_pt@.used_regions.contains(r));
                                            assert(!old(mem).regions().contains(r));
                                            assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                        } else {
                                            assert(dir_pt@.used_regions.contains(r));
                                            assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                        }
                                    } else {
                                        assert(pt_res@.entries[i as int] === pt.entries[i as int]);
                                        assert(pt_res@.entries[j as int] === pt.entries[j as int]);
                                    }
                                }
                            };
                            assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt_res@, layer as nat, ptr));

                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                                entry.is_Directory() ==> {
                                    &&& inv_at(mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr())
                                }
                            }
                            by {
                                let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                                if i == idx {
                                    assert(pt_res@.entries[i as int].get_Some_0() === dir_pt_res@);
                                    assert(entry.get_Directory_addr() === dir_addr);
                                    assert(inv_at(mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr()));
                                } else {
                                    assert(directories_obey_invariant_at(&*old(mem), pt, layer as nat, ptr));
                                    assert(pt.entries[i as int] === pt_res@.entries[i as int]);
                                    assert(entry === view_at(&*old(mem), pt, layer as nat, ptr, i));
                                    assert(entry === view_at(&*old(mem), pt_res@, layer as nat, ptr, i));
                                    if entry.is_Directory() {
                                        let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                        assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt_res@, layer as nat, ptr));
                                        assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               implies !new_regions@.contains(r) by
                                        {
                                            assert(pt_entry.used_regions.contains(r));
                                            assert(old(mem).regions().contains(r));
                                        };
                                        assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               ==> !dir_pt@.used_regions.contains(r));
                                        assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                               ==> #[trigger] mem.region_view(r) === mem.region_view(r));
                                        assert(inv_at(&*old(mem), pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr()));
                                        assert(forall|r: MemRegion| pt_res@.entries[i as int].get_Some_0().used_regions.contains(r)
                                               ==> #[trigger] mem.region_view(r) === old(mem).region_view(r));
                                        assert(pt_res@.entries[i as int].is_Some());
                                        assert(pt_res@.entries[i as int].get_Some_0().used_regions === pt.entries[i as int].get_Some_0().used_regions);
                                        lemma_inv_at_different_memory(&*old(mem), mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr());
                                        assert(inv_at(mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr()));
                                    }
                                }
                            };
                            assert(directories_obey_invariant_at(mem, pt_res@, layer as nat, ptr));
                            assert(inv_at(mem, pt_res@, layer as nat, ptr));

                            assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                                lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
                                assert(pt_res@.region === pt.region);
                                // recursive postcondition:
                                assert(Ok(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat))
                                       === interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@));
                                assert(inv_at(mem, pt_res@, layer as nat, ptr));
                                assert(inv_at(&*old(mem), pt, layer as nat, ptr));
                                assert(pt_res@.entries[idx as int].is_Some());
                                assert(pt_res@.entries[idx as int].get_Some_0() === dir_pt_res@);

                                assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt.entries[i as int] === pt_res@.entries[i as int]);

                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES && i != idx
                                    implies
                                        interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int]
                                        === #[trigger] interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                                {
                                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).is_Ok());
                                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[i as int]);
                                    assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] === interp_at_entry(mem, pt_res@, layer as nat, ptr, base as nat, i));
                                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[i as int] === interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, i));
                                    if pt_res@.entries[i as int].is_Some() {
                                        let pt_entry = pt_res@.entries[i as int].get_Some_0();
                                        assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt_res@, layer as nat, ptr));
                                        assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               implies !new_regions@.contains(r) by
                                        {
                                            assert(pt_entry.used_regions.contains(r));
                                            assert(old(mem).regions().contains(r));
                                        };
                                        assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               ==> !dir_pt_res@.used_regions.contains(r));
                                        assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                               ==> #[trigger] old(mem).region_view(r) === mem.region_view(r));
                                    }
                                    lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt_res@, layer as nat, ptr, base as nat, i);
                                    assert(interp_at_entry(mem, pt_res@, layer as nat, ptr, base as nat, i) === interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, i));
                                };

                                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int] === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries =~= interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                            };
                        };

                        // posts
                        assert forall|r: MemRegion| !pt.used_regions.contains(r) && !new_regions@.contains(r)
                               implies #[trigger] mem.region_view(r) === old(mem).region_view(r) by
                        { assert(!dir_pt@.used_regions.contains(r)); };
                        assert(mem.regions() === old(mem).regions().union(new_regions@));
                        assert(pt_res@.used_regions === pt.used_regions.union(new_regions@));
                        assert(pt_res@.region === pt.region);

                        Ok(Ghost((pt_res@,new_regions@)))
                    },
                    Err(e) => {
                        assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                        Err(e)
                    },
                }
            }
        } else {
            assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
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
            let pwmem: Ghost<mem::PageTableMemory> = Ghost(*mem);

            mem.write(ptr, idx, Ghost(pt.region), new_page_entry.entry);

            assert(inv_at(mem, pt, layer as nat, ptr)) by {
                assert(mem.region_view(pt.region) === pwmem@.region_view(pt.region).update(idx as int, new_page_entry.entry));

                assert forall|i: nat| i < X86_NUM_ENTRIES implies
                    #[trigger] view_at(mem, pt, layer as nat, ptr, i) == if i == idx { new_page_entry@ } else { view_at(&*old(mem), pt, layer as nat, ptr, i) } by { };
                assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                    entry_at_spec(mem, pt, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i) by { };

                assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr)) by {
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        let entry = #[trigger] view_at(mem, pt, layer as nat, ptr, i);
                        entry.is_Directory() ==> {
                            &&& inv_at(mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr())
                        }
                    } by {
                        let entry = view_at(mem, pt, layer as nat, ptr, i);
                        if i != idx {
                            assert(directories_obey_invariant_at(&*old(mem), pt, layer as nat, ptr));
                            if entry.is_Directory() {
                                lemma_inv_at_different_memory(&*old(mem), mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr());
                            }
                        }
                    };
                };
            }

            assert(Ok(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                lemma_interp_at_aux_facts(mem, pt, layer as nat, ptr, base as nat, seq![]);
                assert(inv_at(mem, pt, layer as nat, ptr));
                assert(inv_at(&*old(mem), pt, layer as nat, ptr));
                assert(pt.entries[idx as int].is_None());

                assert forall|i: nat|
                    i < X86_NUM_ENTRIES && i != idx
                    implies
                        interp_at(mem, pt, layer as nat, ptr, base as nat).entries[i as int]
                        === #[trigger] interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                {
                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).is_Ok());
                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[i as int]);
                    assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[i as int] === interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, i));
                    lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt, layer as nat, ptr, base as nat, i);
                    assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, i) === interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, i));
                };

                let new_interp = interp_at(mem, pt, layer as nat, ptr, base as nat);
                assert(new_interp.entries[idx as int] === interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat));
                assert(view_at(mem, pt, layer as nat, ptr, idx as nat) === new_page_entry@);

                assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat) === l1::NodeEntry::Page(pte@));

                assert(new_interp.entries[idx as int] == interp@.map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                assert(new_interp.entries =~= interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                assert(Ok(new_interp) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
            };

            // posts
            assert(forall|r: MemRegion| !pt.used_regions.contains(r) ==> #[trigger] mem.region_view(r) === old(mem).region_view(r));
            assert(mem.regions().union(set![]) =~= mem.regions());
            assert(pt.used_regions.union(set![]) =~= pt.used_regions);

            Ok(Ghost((pt, set![])))
        } else {
            let (pt_with_empty, new_dir_region, new_dir_entry) = insert_empty_directory(mem, Ghost(pt), layer, ptr, base, idx);
            let new_dir_pt = Ghost(pt_with_empty@.entries[idx as int].get_Some_0());
            let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);
            match map_frame_aux(mem, new_dir_pt, layer + 1, new_dir_region.base, entry_base, vaddr, pte) {
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

                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            #[trigger] view_at(mem, pt_final@, layer as nat, ptr, i) == if i == idx { new_dir_entry@ } else { view_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr, i) } by { };
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            #[trigger] entry_at_spec(mem, pt_final@, layer as nat, ptr, i) == if i == idx { new_dir_entry } else { entry_at_spec(mem_with_empty@, pt_with_empty@, layer as nat, ptr, i) } by { };
                        assert(inv_at(mem, pt_final@, layer as nat, ptr)) by {
                            assert(ghost_pt_matches_structure(mem, pt_final@, layer as nat, ptr)) by {
                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] view_at(mem, pt_final@, layer as nat, ptr, i);
                                        entry.is_Directory() == pt_final@.entries[i as int].is_Some()
                                } by {
                                    assert(directories_obey_invariant_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                    assert(ghost_pt_matches_structure(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                    if i == idx { } else { }
                                };
                            };

                            assert(directories_obey_invariant_at(mem, pt_final@, layer as nat, ptr)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] view_at(mem, pt_final@, layer as nat, ptr, i);
                                    entry.is_Directory()
                                        ==> inv_at(mem, pt_final@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr())
                                } by {
                                    let entry = view_at(mem, pt_final@, layer as nat, ptr, i);
                                    assert(directories_obey_invariant_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                    assert(ghost_pt_matches_structure(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                    assert(ghost_pt_used_regions_rtrancl(mem_with_empty@, pt_with_empty@, layer as nat, ptr));

                                    if i == idx {
                                    } else {
                                        assert(entry == view_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr, i));
                                        assert(pt_final@.entries[i as int] === pt_with_empty@.entries[i as int]);
                                        if entry.is_Directory() {
                                            assert(pt_with_empty@.entries[i as int].is_Some());
                                            let pt_entry = pt_with_empty@.entries[i as int].get_Some_0();
                                            assert(pt_with_empty@.entries[i as int] === pt_final@.entries[i as int]);
                                            assert(pt_with_empty@.entries[i as int].get_Some_0() === pt_final@.entries[i as int].get_Some_0());
                                            assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                   ==> !dir_new_regions@.contains(r) && !new_dir_pt@.used_regions.contains(r));
                                            assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                                   ==> #[trigger] mem_with_empty@.region_view(r) === mem.region_view(r));
                                            lemma_inv_at_different_memory(mem_with_empty@, mem, pt_entry, (layer + 1) as nat, entry.get_Directory_addr());
                                            assert(inv_at(mem, pt_final@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr()));
                                        }
                                    }
                                };
                            };

                            assert(directories_have_flags(mem, pt_final@, layer as nat, ptr));

                            assert(pt_final@.entries.len() == pt_with_empty@.entries.len());
                            assert(forall|i: nat| i != idx && i < pt_final@.entries.len() ==> pt_final@.entries[i as int] === pt_with_empty@.entries[i as int]);
                            assert(ghost_pt_used_regions_rtrancl(mem, pt_final@, layer as nat, ptr)) by {
                                assert forall|i: nat, r: MemRegion|
                                    i < pt_final@.entries.len() &&
                                    pt_final@.entries[i as int].is_Some() &&
                                    #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(r)
                                    implies pt_final@.used_regions.contains(r)
                                by {
                                    if i == idx {
                                        if dir_new_regions@.contains(r) {
                                            assert(pt_final@.used_regions.contains(r));
                                        } else {
                                            assert(pt_with_empty@.entries[i as int].get_Some_0().used_regions.contains(r));
                                            assert(pt_with_empty@.used_regions.contains(r));
                                            assert(pt_final@.used_regions.contains(r));
                                        }
                                    } else { }
                                };
                            };
                            assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt_final@, layer as nat, ptr)) by {
                                assert forall|i: nat, j: nat, r: MemRegion|
                                    i != j &&
                                    i < pt_final@.entries.len() && pt_final@.entries[i as int].is_Some() &&
                                    #[trigger] pt_final@.entries[i as int].get_Some_0().used_regions.contains(r) &&
                                    j < pt_final@.entries.len() && pt_final@.entries[j as int].is_Some()
                                    implies !(#[trigger] pt_final@.entries[j as int].get_Some_0().used_regions.contains(r))
                                by
                                {
                                    assert(ghost_pt_used_regions_pairwise_disjoint(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                                    if j == idx {
                                        assert(pt_final@.entries[j as int].get_Some_0() === dir_pt_res@);
                                        assert(pt_final@.entries[i as int] === pt.entries[i as int]);
                                        if dir_new_regions@.contains(r) {
                                            assert(!new_dir_pt@.used_regions.contains(r));
                                            assert(!mem_with_empty@.regions().contains(r));
                                            assert(!dir_pt_res@.used_regions.contains(r));
                                        } else {
                                            if new_dir_pt@.used_regions.contains(r) {
                                                assert(pt.used_regions.contains(r));
                                                assert(mem_with_empty@.regions().contains(r));
                                                assert(!dir_pt_res@.used_regions.contains(r));
                                            }
                                        }
                                    } else {
                                        if i == idx {
                                            assert(pt_final@.entries[i as int].get_Some_0() === dir_pt_res@);
                                            assert(pt_final@.entries[j as int] === pt.entries[j as int]);
                                            if dir_new_regions@.contains(r) {
                                                assert(dir_pt_res@.used_regions.contains(r));
                                                assert(!new_dir_pt@.used_regions.contains(r));
                                                assert(!mem_with_empty@.regions().contains(r));
                                                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                            } else {
                                                assert(new_dir_pt@.used_regions.contains(r));
                                                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                            }
                                        } else {
                                            assert(pt_final@.entries[i as int] === pt.entries[i as int]);
                                            assert(pt_final@.entries[j as int] === pt.entries[j as int]);
                                        }
                                    }

                                };
                            };
                            assert(ghost_pt_matches_structure(mem, pt_final@, layer as nat, ptr));
                            assert(ghost_pt_region_notin_used_regions(mem, pt_final@, layer as nat, ptr));
                            assert(entry_mb0_bits_are_zero(mem, pt_final@, layer as nat, ptr));
                            assert(hp_pat_is_zero(mem, pt_final@, layer as nat, ptr));
                        };

                        assert(Ok(interp_at(mem, pt_final@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                            lemma_interp_at_aux_facts(mem_with_empty@, pt_with_empty@, layer as nat, ptr, base as nat, seq![]);
                            assert(inv_at(mem, pt_final@, layer as nat, ptr));
                            assert(inv_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr));
                            lemma_interp_at_aux_facts(mem, pt_final@, layer as nat, ptr, base as nat, seq![]);

                            // The original/old interp is `interp@`
                            let final_interp = interp_at(mem, pt_final@, layer as nat, ptr, base as nat);
                            let prev_interp = interp_at(mem_with_empty@, pt_with_empty@, layer as nat, ptr, base as nat);

                            assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx
                                implies prev_interp.entries[i as int] === #[trigger] interp@.entries[i as int]
                            by { lemma_interp_at_entry_different_memory(&*old(mem), pt, mem_with_empty@, pt_with_empty@, layer as nat, ptr, base as nat, i); };

                            assert forall|i: nat|
                                i < X86_NUM_ENTRIES && i != idx
                                implies final_interp.entries[i as int] === #[trigger] prev_interp.entries[i as int] by
                            {
                                if pt_final@.entries[i as int].is_Some() {
                                    let pt_entry = pt_final@.entries[i as int].get_Some_0();
                                    assert(ghost_pt_used_regions_pairwise_disjoint(mem, pt_final@, layer as nat, ptr));
                                    assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                           implies !new_regions@.contains(r) by
                                    {
                                        assert(pt_entry.used_regions.contains(r));
                                        assert(mem_with_empty@.regions().contains(r));
                                        assert(old(mem).regions().contains(r));
                                        assert(!new_regions@.contains(r));
                                    };
                                    assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                           ==> !dir_pt_res@.used_regions.contains(r));
                                    assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                           ==> #[trigger] old(mem).region_view(r) === mem.region_view(r));
                                }
                                lemma_interp_at_entry_different_memory(mem_with_empty@, pt_with_empty@, mem, pt_final@, layer as nat, ptr, base as nat, i);
                            };

                            assert(final_interp.entries[idx as int] === interp@.map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                            assert(final_interp.entries =~= interp@.map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                            assert(Ok(interp_at(mem, pt_final@, layer as nat, ptr, base as nat)) === interp@.map_frame(vaddr as nat, pte@));
                        };
                    }

                    // posts
                    proof {
                        assert(pt_final@.region === pt.region);
                        assert(pt_final@.used_regions =~= pt.used_regions.union(new_regions@));
                        assert(mem.regions() =~= old(mem).regions().union(new_regions@));
                        assert forall|r: MemRegion|
                            !(#[trigger] pt.used_regions.contains(r))
                            && !new_regions@.contains(r)
                            implies mem.region_view(r) === old(mem).region_view(r) by
                        {
                            assert(r !== new_dir_region@);
                            assert(!pt_with_empty@.used_regions.contains(r));
                            assert(!new_dir_pt@.used_regions.contains(r));
                            assert(!dir_new_regions@.contains(r));
                            assert(mem.region_view(r) === mem_with_empty@.region_view(r));
                        };
                        assert forall|r: MemRegion|
                            new_regions@.contains(r)
                            implies !(#[trigger] old(mem).regions().contains(r)) by
                        {
                            if r === new_dir_region@ {
                                assert(!old(mem).regions().contains(r));
                            } else {
                                assert(dir_new_regions@.contains(r));
                                assert(!mem_with_empty@.regions().contains(r));
                                assert(!old(mem).regions().contains(r));
                            }
                        };
                        assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] pt.used_regions.contains(r)));
                    }
                    Ok(Ghost((pt_final@, new_regions@)))
                },
                Err(e) => {
                    proof {
                        indexing::lemma_index_from_base_and_addr(entry_base as nat, vaddr as nat, x86_arch_spec.entry_size((layer + 1) as nat), X86_NUM_ENTRIES as nat);
                        assert(false); // We always successfully insert into an empty directory
                    }
                    Err(e)
                },
            }
        }
    }
}

pub proof fn lemma_zeroed_page_implies_empty_at(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize)
    requires
        ptr % PAGE_SIZE == 0,
        mem.inv(),
        mem.regions().contains(pt.region),
        pt.region.base == ptr,
        pt.region.size == PAGE_SIZE,
        mem.region_view(pt.region).len() == pt.entries.len(),
        pt.region.base == ptr,
        ptr == pt.region.base,
        pt.used_regions === set![pt.region],
        layer_in_range(layer),
        pt.entries.len() == X86_NUM_ENTRIES,
        forall|i: nat| i < X86_NUM_ENTRIES ==> mem.region_view(pt.region)[i as int] == 0u64,
        forall|i: nat| i < X86_NUM_ENTRIES ==> pt.entries[i as int].is_None(),
    ensures
        empty_at(mem, pt, layer, ptr),
        inv_at(mem, pt, layer, ptr),
{
    assert forall|i: nat| #![auto] i < X86_NUM_ENTRIES implies
        entry_at_spec(mem, pt, layer, ptr, i)@.is_Empty()
        && entry_at_spec(mem, pt, layer, ptr, i).all_mb0_bits_are_zero()
    by { entry_at_spec(mem, pt, layer, ptr, i).lemma_zero_entry_facts(); };
    assert(forall|i: nat| #![auto] entry_at_spec(mem, pt, layer, ptr, i)@ == view_at(mem, pt, layer, ptr, i));
}

proof fn lemma_empty_at_interp_at_aux_equal_l1_empty_dir(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, idx: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        forall|i: nat| i < init.len() ==> init[i as int] === l1::NodeEntry::Empty(),
        init.len() <= X86_NUM_ENTRIES,
        idx < X86_NUM_ENTRIES,
        view_at(mem, pt, layer, ptr, idx).is_Directory(),
        empty_at(mem, pt.entries[idx as int].get_Some_0(), (layer + 1) as nat, view_at(mem, pt, layer, ptr, idx).get_Directory_addr()),
    ensures
        ({ let res =
            interp_at_aux(
                mem,
                pt.entries[idx as int].get_Some_0(),
                layer + 1,
                view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
                x86_arch_spec.entry_base(layer, base, idx),
                init);
        &&& res.len() === X86_NUM_ENTRIES as nat
        &&& forall|i: nat| i < res.len() ==> res[i as int] === l1::NodeEntry::Empty()
        })
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    let e_ptr = view_at(mem, pt, layer, ptr, idx).get_Directory_addr();
    let e_base = x86_arch_spec.entry_base(layer, base, idx);
    let e_pt = pt.entries[idx as int].get_Some_0();

    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        lemma_empty_at_interp_at_aux_equal_l1_empty_dir(
            mem, pt, layer, ptr, base,
            init.push(interp_at_entry(mem, e_pt, layer + 1, e_ptr, e_base, init.len())), idx);
    }
}

proof fn lemma_empty_at_interp_at_equal_l1_empty_dir(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base: nat, idx: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        idx < X86_NUM_ENTRIES,
        view_at(mem, pt, layer, ptr, idx).is_Directory(),
        empty_at(mem, pt.entries[idx as int].get_Some_0(), (layer + 1) as nat, view_at(mem, pt, layer, ptr, idx).get_Directory_addr()),
    ensures
        ({ let res =
            interp_at(
                mem,
                pt.entries[idx as int].get_Some_0(),
                layer + 1,
                view_at(mem, pt, layer, ptr, idx).get_Directory_addr(),
                x86_arch_spec.entry_base(layer, base, idx));
        &&& res.entries.len() === X86_NUM_ENTRIES as nat
        &&& forall|i: nat| i < res.entries.len() ==> res.entries[i as int] === l1::NodeEntry::Empty()
        })
{
    lemma_empty_at_interp_at_aux_equal_l1_empty_dir(mem, pt, layer, ptr, base, seq![], idx);
}

proof fn lemma_not_empty_at_implies_interp_at_aux_not_empty(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, nonempty_idx: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        nonempty_idx < X86_NUM_ENTRIES,
        !view_at(mem, pt, layer, ptr, nonempty_idx).is_Empty(),
        nonempty_idx < init.len() ==> !init[nonempty_idx as int].is_Empty()
    ensures
        !interp_at_aux(mem, pt, layer, ptr, base, init)[nonempty_idx as int].is_Empty()
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        let new_init = init.push(interp_at_entry(mem, pt, layer, ptr, base, init.len()));
        lemma_not_empty_at_implies_interp_at_aux_not_empty(mem, pt, layer, ptr, base, new_init, nonempty_idx);
    }
}

proof fn lemma_empty_at_implies_interp_at_empty(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        empty_at(mem, pt, layer, ptr),
    ensures
        interp_at(mem, pt, layer, ptr, base).empty()
{
    lemma_interp_at_aux_facts(mem, pt, layer, ptr, base, seq![]);
}

proof fn lemma_not_empty_at_implies_interp_at_not_empty(mem: &mem::PageTableMemory, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(mem, pt, layer, ptr),
        !empty_at(mem, pt, layer, ptr),
    ensures
        !interp_at(mem, pt, layer, ptr, base).empty()
{
    let i = choose|i: nat| i < X86_NUM_ENTRIES && !view_at(mem, pt, layer, ptr, i).is_Empty();
    lemma_not_empty_at_implies_interp_at_aux_not_empty(mem, pt, layer, ptr, base, seq![], i);
}

pub fn map_frame(mem: &mut mem::PageTableMemory, pt: &mut Ghost<PTDir>, vaddr: usize, pte: PageTableEntryExec) -> (res: Result<(),()>)
    requires
        inv(&*old(mem), old(pt)@),
        interp(&*old(mem), old(pt)@).inv(),
        old(mem).inv(),
        old(mem).alloc_available_pages() >= 3,
        accepted_mapping(vaddr as nat, pte@),
        interp(&*old(mem), old(pt)@).accepted_mapping(vaddr as nat, pte@),
        vaddr < MAX_BASE,
    ensures
        inv(mem, pt@),
        interp(mem, pt@).inv(),
        // Refinement of l0
        match res {
            Ok(_) => Ok(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().map_frame(vaddr as nat, pte@),
            Err(_) => Err(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().map_frame(vaddr as nat, pte@),
        },
{
    proof { interp(mem, pt@).lemma_map_frame_refines_map_frame(vaddr as nat, pte@); }
    match map_frame_aux(mem, *pt, 0, mem.cr3().base, 0, vaddr, pte) {
        Ok(res) => {
            proof { interp(&*old(mem), pt@).lemma_map_frame_preserves_inv(vaddr as nat, pte@); }
            *pt = Ghost(res@.0);
            Ok(())
        },
        Err(e) => Err(()),
    }
}

fn is_directory_empty(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize) -> (res: bool)
    requires inv_at(mem, pt, layer as nat, ptr),
    ensures res === empty_at(mem, pt, layer as nat, ptr)
{
    assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
    let mut idx = 0;
    let num_entries = x86_arch_exec().num_entries(layer);
    while idx < num_entries
        invariant
            num_entries == X86_NUM_ENTRIES,
            inv_at(mem, pt, layer as nat, ptr),
            forall|i: nat| i < idx ==> view_at(mem, pt, layer as nat, ptr, i).is_Empty(),
    {
        let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
        if entry.is_mapping() {
            assert(!view_at(mem, pt, layer as nat, ptr, idx as nat).is_Empty());
            assert(!empty_at(mem, pt, layer as nat, ptr));
            return false;
        }
        idx = idx + 1;
    }
    true
}

/// Allocates and inserts an empty directory at the given index.
fn insert_empty_directory(mem: &mut mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, idx: usize)
    -> (res: (Ghost<PTDir> /* pt_res */, MemRegionExec /* new_dir_region */, PageDirectoryEntry /* new_dir_entry */))
    requires
        inv_at(&*old(mem), pt, layer as nat, ptr),
        interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
        old(mem).alloc_available_pages() > 0,
        layer < 3,
        idx < 512,
        view_at(&*old(mem), pt, layer as nat, ptr, idx as nat).is_Empty(),
    ensures
        inv_at(mem, res.0@, layer as nat, ptr),
        !old(mem).regions().contains(res.1@),
        mem.regions() == old(mem).regions().insert(res.1@),
        mem.alloc_available_pages() == old(mem).alloc_available_pages() - 1,
        mem.cr3_spec() == old(mem).cr3_spec(),
        forall|i: nat| i < 512 && i != idx ==> view_at(mem, res.0@, layer as nat, ptr, i) == view_at(&*old(mem), res.0@, layer as nat, ptr, i),
        forall|r: MemRegion| r != res.0@.region && r != res.0@.entries[idx as int].get_Some_0().region ==> mem.region_view(r) == old(mem).region_view(r),
        ({ let pt_res = res.0@; let new_dir_region = res.1; let new_dir_entry = res.2;
           let new_dir_pt = pt_res.entries[idx as int].get_Some_0();
           let entry_base = x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat);
           let new_dir_interp = interp_at(mem, pt_res.entries[idx as int].get_Some_0(), (layer + 1) as nat, new_dir_region.base, entry_base);
           let interp = interp_at(&*old(mem), pt, layer as nat, ptr, base as nat);
           &&& entry_at_spec(mem, pt_res, layer as nat, ptr, idx as nat) == new_dir_entry
           &&& view_at(mem, pt_res, layer as nat, ptr, idx as nat).is_Directory()
           &&& view_at(mem, pt_res, layer as nat, ptr, idx as nat).get_Directory_addr() == new_dir_region.base
           &&& new_dir_interp == interp.new_empty_dir(idx as nat)
           &&& new_dir_interp.inv()
           &&& pt_res.region == pt.region
           &&& pt_res.entries == pt.entries.update(idx as int, Some(new_dir_pt))
           &&& pt_res.used_regions == pt.used_regions.insert(new_dir_region@)
           &&& new_dir_pt.region == new_dir_region@
        })
{
    let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
    let new_dir_region = mem.alloc_page();
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
    mem.write(ptr, idx, Ghost(pt.region), new_dir_entry.entry);

    let pt_res: Ghost<PTDir> = Ghost(
        PTDir {
            region:       pt.region,
            entries:      pt.entries.update(idx as int, Some(new_dir_pt@)),
            used_regions: pt.used_regions.insert(new_dir_pt@.region),
        });
    let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);

    proof {
        assert forall|i: nat| i < X86_NUM_ENTRIES implies
            #[trigger] view_at(mem_with_empty@, pt_res@, layer as nat, ptr, i) == if i == idx { new_dir_entry@ } else { view_at(&*old(mem), pt, layer as nat, ptr, i) } by { };
        assert forall|i: nat| i < X86_NUM_ENTRIES implies
            #[trigger] entry_at_spec(mem_with_empty@, pt_res@, layer as nat, ptr, i) == if i == idx { new_dir_entry } else { entry_at_spec(&*old(mem), pt, layer as nat, ptr, i) } by { };
        lemma_new_seq::<u64>(512nat, 0u64);
        lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
        assert(new_dir_pt@.entries.len() == 512);
        assert(new_dir_region@.contains(new_dir_ptr as nat));
        assert(mem_with_empty@.region_view(new_dir_region@) === new_seq(512nat, 0u64));
        lemma_zeroed_page_implies_empty_at(mem_with_empty@, new_dir_pt@, (layer + 1) as nat, new_dir_ptr);
        assert(empty_at(mem_with_empty@, new_dir_pt@, (layer + 1) as nat, new_dir_ptr));
        assert(inv_at(mem_with_empty@, new_dir_pt@, (layer + 1) as nat, new_dir_ptr));

        assert(forall|r: MemRegion| r !== new_dir_pt@.region && r !== pt_res@.region
               ==> mem_with_empty@.region_view(r) === old(mem).region_view(r));
        assert(mem_with_empty@.region_view(pt_res@.region)
               === old(mem).region_view(pt_res@.region).update(idx as int, new_dir_entry.entry));

        assert(ghost_pt_matches_structure(mem_with_empty@, pt_res@, layer as nat, ptr));
        assert(directories_obey_invariant_at(mem_with_empty@, pt_res@, layer as nat, ptr)) by {
            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                let entry = #[trigger] view_at(mem_with_empty@, pt_res@, layer as nat, ptr, i);
                entry.is_Directory()
                    ==> inv_at(mem_with_empty@, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr())
            } by {
                let entry = view_at(mem_with_empty@, pt_res@, layer as nat, ptr, i);
                if i == idx {
                } else {
                    if entry.is_Directory() {
                        let pt_entry = pt.entries[i as int].get_Some_0();
                        assert(inv_at(&*old(mem), pt_entry, (layer + 1) as nat, entry.get_Directory_addr()));
                        assert(pt.entries[i as int] == pt_res@.entries[i as int]);
                        assert(old(mem).regions().contains(pt_entry.region));
                        lemma_inv_at_different_memory(&*old(mem), mem_with_empty@, pt_entry, (layer + 1) as nat, entry.get_Directory_addr());
                        assert(inv_at(mem_with_empty@, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr()));
                    }
                }
            };
        };
        assert(inv_at(mem, pt_res@, layer as nat, ptr));

        lemma_empty_at_interp_at_equal_l1_empty_dir(mem, pt_res@, layer as nat, ptr, base as nat, idx as nat);
        interp@.lemma_new_empty_dir(idx as nat);
        lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
        let entry_base = x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat);
        let new_dir_interp = interp_at(mem, new_dir_pt@, (layer + 1) as nat, new_dir_ptr, entry_base);
        assert(new_dir_interp.entries =~= interp@.new_empty_dir(idx as nat).entries);
        assert(new_dir_interp == interp@.new_empty_dir(idx as nat));
    }

    (pt_res, new_dir_region, new_dir_entry)
}

fn unmap_aux(mem: &mut mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, vaddr: usize)
    -> (res: Result<Ghost<(PTDir,Set<MemRegion>)>,()>)
    requires
        inv_at(&*old(mem), pt, layer as nat, ptr),
        interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
        old(mem).inv(),
        interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).accepted_unmap(vaddr as nat),
        base <= vaddr < MAX_BASE,
    ensures
        match res {
            Ok(resv) => {
                let (pt_res, removed_regions) = resv@;
                // We return the regions that we removed
                &&& old(mem).regions() == mem.regions().union(removed_regions)
                &&& pt.used_regions == pt_res.used_regions.union(removed_regions)
                // and only those we removed
                &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] mem.regions().contains(r)))
                &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] pt_res.used_regions.contains(r)))
                // Invariant preserved
                &&& inv_at(mem, pt_res, layer as nat, ptr)
                // We only touch regions in pt.used_regions
                &&& (forall|r: MemRegion|
                     !(#[trigger] pt_res.used_regions.contains(r))
                     && !(#[trigger] removed_regions.contains(r))
                    ==> mem.region_view(r) === old(mem).region_view(r))
                &&& pt_res.region === pt.region
            },
            Err(e) => {
                // If error, unchanged
                &&& mem === old(mem)
            },
        },
        // Refinement of l1
        match res {
            Ok(resv) => {
                let (pt_res, removed_regions) = resv@;
                Ok(interp_at(mem, pt_res, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)
            },
            Err(e) =>
                Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat),
        },
        mem.cr3_spec() == old(mem).cr3_spec(),
    // decreases X86_NUM_LAYERS - layer
{
    proof { lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat); }
    let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
    proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
    let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
    let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
    proof {
        interp@.lemma_unmap_structure_assertions(vaddr as nat, idx as nat);
        interp@.lemma_unmap_refines_unmap(vaddr as nat);
    }
    let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
    proof {
        indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
        assert(entry_base <= vaddr);
    }
    assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat)
           == interp_at(mem, pt, layer as nat, ptr, base as nat).entries[idx as int]);
    if entry.is_mapping() {
        if entry.is_dir(layer) {
            let dir_addr = entry.address() as usize;
            assert(pt.entries[idx as int].is_Some());
            let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
            assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
            assert(forall|r: MemRegion| #![auto] pt.entries[idx as int].get_Some_0().used_regions.contains(r) ==> pt.used_regions.contains(r));
            match unmap_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr) {
                Ok(rec_res) => {
                    let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                    let removed_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);

                    assert(inv_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr));
                    assert(Ok(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat))
                           === interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).unmap(vaddr as nat));
                    assert(idx < pt.entries.len());
                    assert(!pt.entries[idx as int].get_Some_0().used_regions.contains(pt.region));
                    assert(!removed_regions@.contains(pt.region));
                    assert(!dir_pt_res@.used_regions.contains(pt.region));
                    assert(old(mem).regions() === mem.regions().union(removed_regions@));

                    if is_directory_empty(mem, dir_pt_res, layer + 1, dir_addr) {
                        let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);
                        let pt_with_empty: Ghost<PTDir> = Ghost(
                            PTDir {
                                region:       pt.region,
                                entries:      pt.entries.update(idx as int, Some(dir_pt_res@)),
                                used_regions: pt.used_regions,
                            });
                        mem.write(ptr, idx, Ghost(pt.region), 0u64);
                        mem.dealloc_page(MemRegionExec { base: dir_addr, size: PAGE_SIZE, });

                        let removed_regions: Ghost<Set<MemRegion>> = Ghost(removed_regions@.insert(dir_pt_res@.region));
                        let pt_res: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, None),
                                used_regions: pt.used_regions.difference(removed_regions@),
                            });
                        let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));

                        proof {
                            entry_at_spec(mem, pt_res@, layer as nat, ptr, idx as nat).lemma_zero_entry_facts();
                            assert(pt_res@.region === pt.region);
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt.entries[i as int]);
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt_res@, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt_res@, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                            assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(r));


                            assert(directories_obey_invariant_at(mem, pt_res@, layer as nat, ptr)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                                    entry.is_Directory() ==> {
                                        &&& inv_at(mem, pt_res@.entries[i as int].get_Some_0(), layer as nat + 1, entry.get_Directory_addr())
                                    }
                                } by {
                                    let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                    if i == idx {
                                    } else {
                                        if entry.is_Directory() {
                                            lemma_inv_at_different_memory(&*old(mem), mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr());
                                        }
                                    }
                                };
                            };

                            assert(inv_at(mem, pt_res@, layer as nat, ptr));

                            // postconditions
                            assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] mem.regions().contains(r))));
                            assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                            assert(pt.used_regions =~= pt_res@.used_regions.union(removed_regions@));
                            assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                            assert(forall|r: MemRegion|
                                 !(#[trigger] pt_res@.used_regions.contains(r))
                                 && !(#[trigger] removed_regions@.contains(r))
                                ==> mem.region_view(r) === old(mem).region_view(r));
                            assert(mem.cr3_spec() == old(mem).cr3_spec());

                            // Refinement
                            assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                                lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES
                                    implies
                                    #[trigger] interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                                    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                                {
                                    if i == idx {
                                        lemma_empty_at_implies_interp_at_empty(mem_with_empty@, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat);
                                        assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int] ==
                                               interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                    } else {
                                        lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt_res@, layer as nat, ptr, base as nat, i);
                                        assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                                               interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                    }
                                }

                                assert(
                                    interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries =~=
                                    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                            };
                        }
                        Ok(res)
                    } else {
                        let pt_res: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                used_regions: pt.used_regions.difference(removed_regions@),
                            });
                        let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));

                        proof {
                            assert(pt_res@.region === pt.region);
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt.entries[i as int]);
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt_res@, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                            assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt_res@, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                            assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(r));

                            assert(inv_at(mem, pt_res@, layer as nat, ptr)) by {
                                assert(directories_obey_invariant_at(mem, pt_res@, layer as nat, ptr)) by {
                                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                        let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                                        entry.is_Directory() ==> {
                                            &&& inv_at(mem, pt_res@.entries[i as int].get_Some_0(), layer as nat + 1, entry.get_Directory_addr())
                                        }
                                    } by {
                                        let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                                        if i == idx {
                                        } else {
                                            if entry.is_Directory() {
                                                lemma_inv_at_different_memory(&*old(mem), mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr());
                                            }
                                        }
                                    };
                                };
                            };

                            // postconditions
                            assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                            assert(pt.used_regions =~= pt_res@.used_regions.union(removed_regions@));
                            assert(forall|r: MemRegion|
                                 !(#[trigger] pt_res@.used_regions.contains(r))
                                 && !(#[trigger] removed_regions@.contains(r))
                                ==> mem.region_view(r) === old(mem).region_view(r));
                            assert(pt_res@.region === pt.region);
                            assert(mem.cr3_spec() == old(mem).cr3_spec());
                            // Refinement
                            assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                                lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
                                assert forall|i: nat|
                                    i < X86_NUM_ENTRIES
                                    implies
                                    #[trigger] interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                                    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                                {
                                    if i == idx {
                                        assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int]
                                               == l1::NodeEntry::Directory(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat)));
                                        assert(interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).unmap(vaddr as nat).is_Ok());
                                        assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[idx as int] == interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, idx as nat));

                                        lemma_not_empty_at_implies_interp_at_not_empty(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat);
                                        assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int] ==
                                               interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                                    } else {
                                        lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt_res@, layer as nat, ptr, base as nat, i);
                                        assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                                               interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                                    }
                                }

                                assert(
                                    interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries =~=
                                    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                            };
                        }
                        Ok(res)
                    }

                },
                Err(e) => {
                    assert(mem === old(mem));
                    assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
                    Err(e)
                },
            }
        } else {
            if aligned_exec(vaddr, x86_arch_exec().entry_size(layer)) {
                mem.write(ptr, idx, Ghost(pt.region), 0u64);

                let removed_regions: Ghost<Set<MemRegion>> = Ghost(Set::empty());
                let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt, removed_regions@));

                proof {
                    entry_at_spec(mem, pt, layer as nat, ptr, idx as nat).lemma_zero_entry_facts();
                    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));

                    assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr)) by {
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                            let entry = #[trigger] view_at(mem, pt, layer as nat, ptr, i);
                            entry.is_Directory() ==> {
                                &&& inv_at(mem, pt.entries[i as int].get_Some_0(), layer as nat + 1, entry.get_Directory_addr())
                            }
                        } by {
                            let entry = view_at(mem, pt, layer as nat, ptr, i);
                            if i == idx {
                            } else {
                                if entry.is_Directory() {
                                    assert(directories_obey_invariant_at(&*old(mem), pt, layer as nat, ptr));
                                    lemma_inv_at_different_memory(&*old(mem), mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry.get_Directory_addr());
                                    assert(inv_at(mem, pt.entries[i as int].get_Some_0(), layer as nat + 1, entry.get_Directory_addr()));
                                }
                            }
                        };
                    };

                    assert(inv_at(mem, pt, layer as nat, ptr));

                    // postconditions
                    assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                    assert(pt.used_regions =~= pt.used_regions.union(removed_regions@));

                    // Refinement
                    assert(Ok(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                        lemma_interp_at_aux_facts(mem, pt, layer as nat, ptr, base as nat, seq![]);
                        assert(interp_at(mem, pt, layer as nat, ptr, base as nat).entries.len() == X86_NUM_ENTRIES);
                        assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries.len() == X86_NUM_ENTRIES);

                        assert forall|i: nat|
                            i < X86_NUM_ENTRIES
                            implies
                            #[trigger] interp_at(mem, pt, layer as nat, ptr, base as nat).entries[i as int] ==
                            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                        {
                            if i == idx {
                            } else {
                                lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt, layer as nat, ptr, base as nat, i);
                                assert(interp_at(mem, pt, layer as nat, ptr, base as nat).entries[i as int] ==
                                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                            }
                        }

                        assert(
                            interp_at(mem, pt, layer as nat, ptr, base as nat).entries =~=
                            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                    };
                }
                Ok(res)

            } else {
                assert(mem === old(mem));
                assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
                Err(())
            }
        }
    } else {
        assert(mem === old(mem));
        assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
        Err(())
    }
}

pub fn unmap(mem: &mut mem::PageTableMemory, pt: &mut Ghost<PTDir>, vaddr: usize) -> (res: Result<(),()>)
    requires
        inv(&*old(mem), old(pt)@),
        interp(&*old(mem), old(pt)@).inv(),
        old(mem).inv(),
        interp(&*old(mem), old(pt)@).accepted_unmap(vaddr as nat),
        vaddr < MAX_BASE,
    ensures
        inv(mem, pt@),
        interp(mem, pt@).inv(),
        // Refinement of l0
        match res {
            Ok(_)  => Ok(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().unmap(vaddr as nat),
            Err(_) => Err(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().unmap(vaddr as nat),
        },
{
    proof { interp(mem, pt@).lemma_unmap_refines_unmap(vaddr as nat); }
    match unmap_aux(mem, *pt, 0, mem.cr3().base, 0, vaddr) {
        Ok(res) => {
            proof { interp(&*old(mem), pt@).lemma_unmap_preserves_inv(vaddr as nat); }
            *pt = Ghost(res@.0);
            Ok(())
        },
        Err(e) => Err(()),
    }
}

}

} // verus!
