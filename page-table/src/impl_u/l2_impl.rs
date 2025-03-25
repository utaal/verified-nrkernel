use vstd::prelude::*;
use vstd::assert_by_contradiction;


use crate::spec_t::mmu::defs::{ MemRegion, MemRegionExec, PTE, PageTableEntryExec, Flags,
x86_arch_exec, WORD_SIZE, PAGE_SIZE, MAX_PHYADDR, MAX_PHYADDR_WIDTH, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
L3_ENTRY_SIZE, X86_NUM_LAYERS, X86_NUM_ENTRIES, bit, bitmask_inc };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ between, aligned, new_seq, x86_arch_spec,
axiom_max_phyaddr_width_facts, MAX_BASE, candidate_mapping_overlaps_existing_vmem_usize, usize_keys };
#[cfg(verus_keep_ghost)]
use crate::definitions_u::{ lemma_new_seq };
use crate::definitions_u::{ aligned_exec };
use crate::impl_u::l1;
use crate::impl_u::indexing;
use crate::spec_t::mmu::translation::{ PDE,GPDE, MASK_FLAG_P, MASK_FLAG_RW, MASK_FLAG_US,
MASK_FLAG_PWT, MASK_FLAG_PCD, MASK_FLAG_XD, MASK_ADDR, MASK_PG_FLAG_PAT, MASK_L1_PG_FLAG_PS,
MASK_DIR_ADDR, MASK_L1_PG_ADDR, MASK_L2_PG_ADDR, MASK_L3_PG_ADDR, MASK_NEG_DIRTY_ACCESS };
#[cfg(verus_keep_ghost)]
use crate::extra;
use crate::impl_u::wrapped_token::{ WrappedMapToken, WrappedUnmapToken, WrappedTokenView, OpArgs };


verus! {

broadcast proof fn lemma_union_empty<A>(s: Set<A>)
    ensures #[trigger] s.union(set![]) == s,
{
    assert(s.union(set![]) =~= s);
}


broadcast proof fn lemma_bitvector_facts_simple()
    ensures #![trigger]
        bit!(0usize) == 1,
        0 & MASK_NEG_DIRTY_ACCESS == 0,
        1usize << 0 == 1,
        0usize & 1 == 0,
{
    assert(bit!(0usize) == 1) by (bit_vector);
    assert(0 & !(bit!(5) | bit!(6)) == 0) by (bit_vector);
    assert(1usize << 0 == 1) by (bit_vector);
    assert(0usize & 1 == 0) by (bit_vector);
}

// TODO: Convert to individual broadcast maybe
proof fn lemma_bitvector_facts()
    ensures
        forall|v: usize| v & bit!(5) == 0 && v & bit!(6) == 0 ==> #[trigger] (v & MASK_NEG_DIRTY_ACCESS) == v,
        forall|v: usize, i: usize| i < 64 ==> v & bit!(i) != bit!(i) <==> v & bit!(i) == 0,
        forall|v: usize| 0 & v == 0,
        forall|v: usize, m: usize| v & m & m == v & m,
        forall|v: usize| v & bit!(0) == #[trigger] (v & MASK_NEG_DIRTY_ACCESS & bit!(0)),
        forall|v: usize| v == v | 0,
{
    assert(forall|v: usize| 0 & v == 0) by (bit_vector);
    assert(forall|v: usize| #![auto] v & bit!(0) == (v & !(bit!(5) | bit!(6)) & bit!(0))) by (bit_vector);
    assert(forall|v: usize| v == v | 0) by (bit_vector);
    assert(forall|v: usize| v & bit!(5) == 0 && v & bit!(6) == 0 ==> #[trigger] (v & !(bit!(5) | bit!(6))) == v) by (bit_vector);
    assert(forall|v: usize, i: usize| i < 64 ==> v & bit!(i) != bit!(i) <==> v & bit!(i) == 0) by (bit_vector);
    assert(forall|v: usize, m: usize| v & m & m == v & m) by (bit_vector);
}

proof fn lemma_page_aligned_implies_mask_dir_addr_is_identity()
    ensures forall|addr: usize| addr <= MAX_PHYADDR && #[trigger] aligned(addr as nat, PAGE_SIZE as nat) ==> addr & MASK_DIR_ADDR == addr,
{
    assert forall|addr: usize|
        addr <= MAX_PHYADDR &&
        #[trigger] aligned(addr as nat, PAGE_SIZE as nat)
        implies
        addr & MASK_DIR_ADDR == addr
    by {
        let max_width: usize = MAX_PHYADDR_WIDTH;
        let mask_dir_addr: usize = MASK_DIR_ADDR;
        assert(addr & mask_dir_addr == addr) by (bit_vector)
            requires
                addr <= sub(1usize << max_width, 1usize),
                addr % 4096usize == 0,
                mask_dir_addr == bitmask_inc!(12usize, max_width - 1);
    };
}

proof fn lemma_aligned_addr_mask_facts(addr: usize)
    ensures
        aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr & MASK_ADDR),
        aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr & MASK_ADDR),
        addr & MASK_L3_PG_ADDR == addr & MASK_ADDR,
        addr <= MAX_PHYADDR && aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
        addr <= MAX_PHYADDR && aligned(addr as nat, L3_ENTRY_SIZE as nat) ==> (addr & MASK_ADDR == addr),
{
    axiom_max_phyaddr_width_facts();
    assert(aligned(addr as nat, L1_ENTRY_SIZE as nat) ==> (addr & MASK_L1_PG_ADDR == addr & MASK_ADDR)) by {
        if aligned(addr as nat, L1_ENTRY_SIZE as nat) {
            let max_width: usize = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(30usize, max_width - 1) == addr & bitmask_inc!(12usize, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x40000000usize == 0,
                    32 <= max_width;
        }
    };
    assert(aligned(addr as nat, L2_ENTRY_SIZE as nat) ==> (addr & MASK_L2_PG_ADDR == addr & MASK_ADDR)) by {
        if aligned(addr as nat, L2_ENTRY_SIZE as nat) {
            let max_width: usize = MAX_PHYADDR_WIDTH;
            assert(addr & bitmask_inc!(21usize, max_width - 1) == addr & bitmask_inc!(12usize, max_width - 1)) by (bit_vector)
                requires
                    addr % 0x200000usize == 0,
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

pub open spec fn addr_is_zero_padded(layer: nat, addr: usize, is_page: bool) -> bool {
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

// PDE is defined in crate::spec_t::mmu::defs to define the page table walk
// semantics. Here we reuse it for the implementation and add exec functions to it.
impl PDE {
    // PAT flag is set to zero for huge pages and super pages
    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@ is Page && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@ is Page && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }

    pub proof fn lemma_addr_mask_when_hp_pat_is_zero(self)
        requires
            self.hp_pat_is_zero(),
            self.all_mb0_bits_are_zero(),
            self@ is Page,
        ensures
            self.layer == 1 ==> self.entry & MASK_L1_PG_ADDR == self.entry & MASK_ADDR,
            self.layer == 2 ==> self.entry & MASK_L2_PG_ADDR == self.entry & MASK_ADDR
    {
        let e = self.entry; let mw = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        reveal(PDE::all_mb0_bits_are_zero);
        if self.layer() == 1 {
            assert(e & bitmask_inc!(12usize, mw - 1) == e & bitmask_inc!(30usize, mw - 1)) by (bit_vector)
                requires e & bit!(12usize) == 0, e & bitmask_inc!(13usize,29usize) == 0, 32 <= mw <= 52;
        } else if self.layer() == 2 {
            assert(e & bitmask_inc!(12usize, mw - 1) == e & bitmask_inc!(21usize, mw - 1)) by (bit_vector)
                requires e & bit!(12usize) == 0, e & bitmask_inc!(13usize,20usize) == 0, 32 <= mw <= 52;
        }
    }

    pub proof fn lemma_zero_entry_facts(self)
        requires
            self.entry & MASK_NEG_DIRTY_ACCESS == 0,
            self.layer@ <= 3,
        ensures
            self@ is Invalid,
            self.all_mb0_bits_are_zero(),
    {
        broadcast use lemma_bitvector_facts_simple;
        reveal(PDE::all_mb0_bits_are_zero);
        let e = self.entry;
        axiom_max_phyaddr_width_facts();
        assert(forall|i:usize| #![auto] i != 5 && i != 6 ==> e & bit!(i) == 0) by (bit_vector)
            requires e & !(bit!(5) | bit!(6)) == 0;
        assert(forall|i1: usize, i2: usize| #![auto] 6 < i1 && 6 < i2 ==> e & bitmask_inc!(i1, i2) == 0) by (bit_vector)
            requires e & !(bit!(5) | bit!(6)) == 0;
    }

    pub proof fn lemma_new_entry_mb0_bits_are_zero(
        layer: usize,
        address: usize,
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
               (PDE { entry: e, layer: Ghost(layer as nat) }).all_mb0_bits_are_zero()
            }),
    {
        let or1 = MASK_FLAG_P;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS } else { 0 };
        let or3 = if is_writable           { MASK_FLAG_RW }       else { 0 };
        let or4 = if is_supervisor         { 0 }                  else { MASK_FLAG_US };
        let or5 = if is_writethrough       { MASK_FLAG_PWT }      else { 0 };
        let or6 = if disable_cache         { MASK_FLAG_PCD }      else { 0 };
        let or7 = if disable_execute       { MASK_FLAG_XD }       else { 0 };
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: usize = MAX_PHYADDR_WIDTH;
        assert(forall|a:usize| #![auto] a == a | 0) by (bit_vector);

        axiom_max_phyaddr_width_facts();
        assert(forall|a:usize,i:usize| #![auto] i < 12 ==> a & bitmask_inc!(12usize,sub(mw,1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:usize,i:usize| #![auto] i != 7 && (a & bit!(7usize) == 0) ==> (a | bit!(i)) & bit!(7usize) == 0) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i < 13 && (a & bitmask_inc!(13usize,29usize) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13usize,29usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i > 29 && (a & bitmask_inc!(13usize,29usize) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13usize,29usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i < 13 && (a & bitmask_inc!(13usize,20usize) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13usize,20usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i > 20 && (a & bitmask_inc!(13usize,20usize) == 0) ==> ((a | bit!(i)) & bitmask_inc!(13usize,20usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i < mw && (a & bitmask_inc!(mw,51usize)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i > 51 && (a & bitmask_inc!(mw,51usize)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,51usize) == 0)) by (bit_vector)
            requires mw <= 52;
        assert(address & bitmask_inc!(mw, 51) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12usize, mw - 1) == address,
                32 <= mw <= 52;
        assert(forall|a:usize,i:usize| #![auto] i < mw && (a & bitmask_inc!(mw,62usize)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62usize) == 0)) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i > 62 && (a & bitmask_inc!(mw,62usize)    == 0) ==> ((a | bit!(i)) & bitmask_inc!(mw,62usize) == 0)) by (bit_vector)
            requires mw <= 52;
        assert(address & bitmask_inc!(mw, 62) == 0) by (bit_vector)
            requires
                address & bitmask_inc!(12usize, mw - 1) == address,
                32 <= mw <= 52;
        PDE::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
        if layer == 0 {
            assert(!is_page);
            assert(e & bit!(7usize) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
        } else if layer == 1 {
            if is_page {
                assert(address & bitmask_inc!(30usize,sub(mw,1)) == address ==> address & bitmask_inc!(13usize,29usize) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13usize,29usize) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            } else {
                assert(e & bit!(7usize) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0);
            }
        } else if layer == 2 {
            if is_page {
                assert(address & bitmask_inc!(21usize,sub(mw,1)) == address ==> address & bitmask_inc!(13usize,20usize) == 0) by (bit_vector);
                assert(e & bitmask_inc!(13usize,20usize) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            } else {
                assert(e & bit!(7usize) == 0);
                assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
            }
        } else if layer == 3 {
            assert(is_page);
            // assert(e & bit!(7usize) == 0);
            assert(e & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0);
        } else { assert(false); }

        let pde = PDE { entry: e, layer: Ghost(layer as nat) };
        reveal(PDE::all_mb0_bits_are_zero);
        assert(pde.all_mb0_bits_are_zero());
    }


    pub proof fn lemma_new_entry_addr_mask_is_address(
        layer: usize,
        address: usize,
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
               &&& e & bit!(5) == 0
               &&& e & bit!(6) == 0
            }),
    {
        let or1 = MASK_FLAG_P;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 };
        let or3 = if is_writable           { MASK_FLAG_RW }        else { 0 };
        let or4 = if is_supervisor         { 0 }                   else { MASK_FLAG_US };
        let or5 = if is_writethrough       { MASK_FLAG_PWT }       else { 0 };
        let or6 = if disable_cache         { MASK_FLAG_PCD }       else { 0 };
        let or7 = if disable_execute       { MASK_FLAG_XD }        else { 0 };
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        let mw: usize = MAX_PHYADDR_WIDTH;
        axiom_max_phyaddr_width_facts();
        assert(forall|a:usize,x:usize| x < 64 && (a & bit!(x) == 0) ==> a & bit!(x) != bit!(x)) by (bit_vector);
        assert(forall|a:usize| #![auto] a == a | 0) by (bit_vector);
        assert(forall|a:usize,i:usize| #![auto] i < 12 ==> a & bitmask_inc!(12usize, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12usize, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:usize,i:usize| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12usize, sub(mw, 1)) == (a | bit!(i))  & bitmask_inc!(12usize, sub(mw, 1))) by (bit_vector)
            requires 32 <= mw <= 52;

        assert(forall|a:usize,i:usize| #![auto] i < 12 ==> a & bitmask_inc!(12usize, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:usize,i:usize| #![auto] i > sub(mw, 1) ==> a & bitmask_inc!(12usize, sub(mw, 1)) == a ==> a & bit!(i) == 0) by (bit_vector)
            requires 32 <= mw <= 52;
        assert(forall|a:usize,i:usize| #![auto] i < 64 ==> a & bit!(i) == 0 ==> (a | bit!(i)) & bit!(i) == bit!(i)) by (bit_vector);
        assert(forall|a:usize,i:usize,j:usize| #![auto] i != j ==> a & bit!(i) == (a | bit!(j)) & bit!(i)) by (bit_vector);
        assert({
            &&& is_page && layer == 1 ==> e & MASK_PG_FLAG_PAT == 0
            &&& is_page && layer == 2 ==> e & MASK_PG_FLAG_PAT == 0
        }) by {
            if is_page && layer == 1 {
                assert(address & bit!(12usize) == 0) by (bit_vector)
                    requires address & bitmask_inc!(30usize, sub(mw, 1)) == address;
            }
            if is_page && layer == 2 {
                assert(address & bit!(12usize) == 0) by (bit_vector)
                    requires address & bitmask_inc!(21usize, sub(mw, 1)) == address;
            }
        };
    }

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer as nat, pte.frame.base, true),
            pte.frame.base & MASK_ADDR == pte.frame.base,
        ensures
            r.all_mb0_bits_are_zero(),
            r.hp_pat_is_zero(),
            r@ is Page,
            r.layer@ == layer,
            r@->Page_addr == pte.frame.base,
            r.entry & MASK_ADDR == pte.frame.base,
            r.entry & MASK_FLAG_P == MASK_FLAG_P,
            r.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS <==> layer != 3,
            r.entry & MASK_FLAG_RW == MASK_FLAG_RW <==> pte.flags.is_writable,
            r@->Page_RW == pte.flags.is_writable,
            r.entry & MASK_FLAG_US == MASK_FLAG_US <==> !pte.flags.is_supervisor,
            r@->Page_US == !pte.flags.is_supervisor,
            r.entry & MASK_FLAG_PWT != MASK_FLAG_PWT,
            r.entry & MASK_FLAG_PCD != MASK_FLAG_PCD,
            r.entry & MASK_FLAG_XD == MASK_FLAG_XD <==> pte.flags.disable_execute,
            r@->Page_XD == pte.flags.disable_execute,
            r.entry & bit!(5) == 0,
            r.entry & bit!(6) == 0,
    {
        Self::new_entry(layer, pte.frame.base, true, pte.flags.is_writable, pte.flags.is_supervisor, false, false, pte.flags.disable_execute)
    }

    pub fn new_dir_entry(layer: usize, address: usize) -> (r: Self)
        requires
            layer < 3,
            address & MASK_DIR_ADDR == address
        ensures
            r.all_mb0_bits_are_zero(),
            r.hp_pat_is_zero(),
            r.entry & bit!(5) == 0,
            r.entry & bit!(6) == 0,
            r@ is Directory,
            r.layer@ == layer,
            r@->Directory_addr == address,
            r@->Directory_RW,
            r@->Directory_US,
            !r@->Directory_XD,
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
        address: usize,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> (r: PDE)
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer as nat, address, is_page),
            address & MASK_ADDR == address,
        ensures
            r.all_mb0_bits_are_zero(),
            if is_page { r@ is Page && r@->Page_addr == address } else { r@ is Directory && r@->Directory_addr == address},
            r.hp_pat_is_zero(),
            r.entry & bit!(5) == 0,
            r.entry & bit!(6) == 0,
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
        PDE {
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
            PDE::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            PDE::lemma_new_entry_mb0_bits_are_zero(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            if is_page { e.lemma_addr_mask_when_hp_pat_is_zero(); }
        }
        e
    }

    pub fn flags(&self) -> (res: Flags)
        requires
            self.layer() <= 3,
            self@ is Page
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

    pub fn address(&self) -> (res: usize)
        requires
            self.layer() <= 3,
            self@ is Page ==> 0 < self.layer(),
            self.hp_pat_is_zero(),
            self.all_mb0_bits_are_zero(),
            !(self@ is Invalid),
        ensures
            res == match self@ {
                GPDE::Page { addr, .. }      => addr,
                GPDE::Directory { addr, .. } => addr,
                GPDE::Invalid                  => arbitrary(),
            }
    {
        proof {
            match self@ {
                GPDE::Page { addr, .. }      => self.lemma_addr_mask_when_hp_pat_is_zero(),
                GPDE::Directory { addr, .. } => { },
                GPDE::Invalid                  => { },
            }
        }
        self.entry & MASK_ADDR
    }

    pub fn is_present(&self) -> (r: bool)
        requires
            self.all_mb0_bits_are_zero(),
            self.layer() <= 3
        ensures
            r == !(self@ is Invalid),
    {
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(&self, layer: usize) -> (r: bool)
        requires
            !(self@ is Invalid),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r { self@ is Page } else { self@ is Directory },
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
            !(self@ is Invalid),
            layer as nat == self.layer@,
            layer <= 3,
        ensures
            if r { self@ is Directory } else { self@ is Page },
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

pub open spec(checked) fn inv(tok: WrappedTokenView, pt: PTDir) -> bool {
    &&& pt.region.base == tok.pt_mem.pml4
    &&& inv_at(tok, pt, 0, tok.pt_mem.pml4)
}

/// Get the view of the entry at address ptr + i * WORD_SIZE
pub open spec fn entry_at_spec(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, i: nat) -> PDE {
    PDE {
        entry: tok.read(i as usize, pt.region),
        layer: Ghost(layer),
    }
}

/// Get the entry at address ptr + i * WORD_SIZE
fn entry_at(Tracked(tok): Tracked<&mut WrappedMapToken>, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, i: usize) -> (res: PDE)
    requires
        i < 512,
        old(tok).inv(),
        inv_at(old(tok)@, pt, layer as nat, ptr),
    ensures
        res.layer@ == layer as nat,
        res == entry_at_spec(tok@, pt, layer as nat, ptr, i as nat),
        res.hp_pat_is_zero(),
        tok@ == old(tok)@,
        tok.inv(),
        (res@ is Page ==> 0 < res.layer()),
{
    assert(aligned((ptr + i * WORD_SIZE) as nat, 8)) by {
        assert(inv_at(tok@, pt, layer as nat, ptr));
        assert(ptr % PAGE_SIZE == 0);
    };
    // triggering
    proof { let _ = entry_at_spec(tok@, pt, layer as nat, ptr, i as nat); }
    let e = PDE {
        entry: WrappedMapToken::read(Tracked(tok), ptr, i, Ghost(pt.region)),
        layer: Ghost(layer as nat),
    };
    proof {
        let es = PDE { entry: tok@.read(i, pt.region), layer: Ghost(layer as nat) };
        assert(es == e);
    }
    e
}

// TODO: deduplicate this from the map token one
fn entry_at_unmap(Tracked(tok): Tracked<&mut WrappedUnmapToken>, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, i: usize) -> (res: PDE) {
    let e = PDE {
        entry: WrappedUnmapToken::read(Tracked(tok), ptr, i, Ghost(pt.region)),
        layer: Ghost(layer as nat),
    };
    e
}

pub open spec fn ghost_pt_matches_structure(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![trigger pt.entries[i as int], entry_at_spec(tok, pt, layer, ptr, i)@]
    i < X86_NUM_ENTRIES ==> {
        let entry = entry_at_spec(tok, pt, layer, ptr, i)@;
        entry is Directory == pt.entries[i as int].is_Some()
    }
}

pub open spec fn directories_obey_invariant_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer, 0nat
        when layer_in_range(layer)
{
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        let entry = #[trigger] entry_at_spec(tok, pt, layer, ptr, i)@;
        entry is Directory ==> {
            &&& inv_at(tok, pt.entries[i as int].get_Some_0(), layer + 1, entry->Directory_addr)
        }
    }
}

pub open spec fn empty_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![auto] i < X86_NUM_ENTRIES ==> entry_at_spec(tok, pt, layer, ptr, i)@ is Invalid
}

pub open spec(checked) fn layer_in_range(layer: nat) -> bool {
    layer < X86_NUM_LAYERS
}

pub open spec(checked) fn inv_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer
{
    &&& ptr % PAGE_SIZE == 0
    //&&& mem.inv()
    &&& tok.regions.contains_key(pt.region)
    &&& pt.region.base == ptr
    &&& pt.region.size == PAGE_SIZE
    &&& tok.regions[pt.region].len() == pt.entries.len()
    &&& layer_in_range(layer)
    &&& pt.entries.len() == X86_NUM_ENTRIES
    &&& directories_obey_invariant_at(tok, pt, layer, ptr)
    &&& directories_have_flags(tok, pt, layer, ptr)
    &&& ghost_pt_matches_structure(tok, pt, layer, ptr)
    &&& ghost_pt_used_regions_rtrancl(tok, pt, layer, ptr)
    &&& ghost_pt_used_regions_pairwise_disjoint(tok, pt, layer, ptr)
    &&& ghost_pt_region_notin_used_regions(tok, pt, layer, ptr)
    &&& pt.used_regions.subset_of(tok.regions.dom())
    &&& hp_pat_is_zero(tok, pt, layer, ptr)
    &&& entry_mb0_bits_are_zero(tok, pt, layer, ptr)
}

pub open spec fn directories_have_flags(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i)@) matches GPDE::Directory { RW, US, XD, .. } ==> RW && US && !XD
    }
}

pub open spec fn entry_mb0_bits_are_zero(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==>
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i)).all_mb0_bits_are_zero()
}

/// Entries for super pages and huge pages use bit 12 to denote the PAT flag. We always set that
/// flag to zero, which allows us to always use the same mask to get the address.
pub open spec fn hp_pat_is_zero(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![auto] i < X86_NUM_ENTRIES ==> entry_at_spec(tok, pt, layer, ptr, i).hp_pat_is_zero()
}

// TODO: should I move some of these ghost_pt things in a invariant defined on PTDir?
pub open spec fn ghost_pt_used_regions_pairwise_disjoint(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat, j: nat|
        i != j && i < pt.entries.len() && j < pt.entries.len()
        && #[trigger] pt.entries[j as int] is Some && #[trigger] pt.entries[i as int] is Some
        ==> pt.entries[i as int]->Some_0.used_regions.disjoint(pt.entries[j as int]->Some_0.used_regions)
}

// TODO: this may be implied by the other ones
pub open spec fn ghost_pt_region_notin_used_regions(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat|
        i < pt.entries.len() && pt.entries[i as int].is_Some()
        ==> !(#[trigger] pt.entries[i as int].get_Some_0().used_regions.contains(pt.region))
}

pub open spec fn ghost_pt_used_regions_rtrancl(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    // reflexive
    &&& pt.used_regions.contains(pt.region)
    // transitive
    &&& forall|i: nat, r: MemRegion| #![trigger pt.entries[i as int].get_Some_0().used_regions.contains(r), pt.used_regions.contains(r)]
            i < pt.entries.len() && pt.entries[i as int].is_Some() &&
            pt.entries[i as int].get_Some_0().used_regions.contains(r)
            ==> pt.used_regions.contains(r)
}

pub open spec fn interp_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat) -> l1::Directory
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES, 2nat
        when inv_at(tok, pt, layer, ptr)
{
    l1::Directory {
        entries: interp_at_aux(tok, pt, layer, ptr, base_vaddr, seq![]),
        layer: layer,
        base_vaddr,
        arch: x86_arch_spec,
    }
}

pub open spec fn interp_at_entry(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, idx: nat) -> l1::NodeEntry
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - idx, 0nat
        when inv_at(tok, pt, layer, ptr)
{
    match entry_at_spec(tok, pt, layer, ptr, idx)@ {
        GPDE::Directory { addr: dir_addr, .. } => {
            let entry_base = x86_arch_spec.entry_base(layer, base_vaddr, idx);
            l1::NodeEntry::Directory(interp_at(tok, pt.entries[idx as int].get_Some_0(), layer + 1, dir_addr, entry_base))
        },
        GPDE::Page { addr, RW, US, XD, .. } =>
            l1::NodeEntry::Page(
                PTE {
                    frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(layer) },
                    flags: Flags {
                        is_writable:     RW,
                        is_supervisor:   !US,
                        disable_execute: XD,
                    },
                }),
        GPDE::Invalid => l1::NodeEntry::Invalid,
    }
}

pub open spec fn interp_at_aux(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>) -> Seq<l1::NodeEntry>
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat
        when inv_at(tok, pt, layer, ptr)
{
    if init.len() >= X86_NUM_ENTRIES {
        init
    } else {
        let entry = interp_at_entry(tok, pt, layer, ptr, base_vaddr, init.len());
        interp_at_aux(tok, pt, layer, ptr, base_vaddr, init.push(entry))
    }
}

pub open spec fn interp(tok: WrappedTokenView, pt: PTDir) -> l1::Directory {
    interp_at(tok, pt, 0, tok.pt_mem.pml4, 0)
}

pub open spec fn interp_to_l0(tok: WrappedTokenView, pt: PTDir) -> Map<usize, PTE> {
    usize_keys(interp(tok, pt).interp().map)
}

proof fn lemma_inv_at_different_memory(tok1: WrappedTokenView, tok2: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize)
    requires
        inv_at(tok1, pt, layer, ptr),
        pt.used_regions.subset_of(tok2.regions.dom()),
        forall|r: MemRegion| pt.used_regions.contains(r)
            ==> #[trigger] tok1.regions[r] === tok2.regions[r],
        // Some parts of tok2's invariant that we should already know
        // TODO:
        //tok2.inv(),
        tok2.regions.contains_key(pt.region),
    ensures inv_at(tok2, pt, layer, ptr),
    decreases X86_NUM_LAYERS - layer
{
    assert forall|i: nat| i < X86_NUM_ENTRIES implies
        entry_at_spec(tok2, pt, layer, ptr, i) == entry_at_spec(tok1, pt, layer, ptr, i) by { };

    // Prove directories_obey_invariant_at(tok2, pt, layer, ptr)
    assert forall|i: nat|
    i < X86_NUM_ENTRIES implies {
        let entry = #[trigger] entry_at_spec(tok2, pt, layer, ptr, i)@;
        entry is Directory ==> inv_at(tok2, pt.entries[i as int].get_Some_0(), layer + 1, entry->Directory_addr)
    } by {
        let entry = entry_at_spec(tok2, pt, layer, ptr, i)@;
        if entry is Directory {
            assert(directories_obey_invariant_at(tok1, pt, layer, ptr));
            lemma_inv_at_different_memory(tok1, tok2, pt.entries[i as int].get_Some_0(), layer + 1, entry->Directory_addr);
        }
    };
}

proof fn lemma_interp_at_entry_different_memory(tok1: WrappedTokenView, pt1: PTDir, tok2: WrappedTokenView, pt2: PTDir, layer: nat, ptr: usize, base: nat, idx: nat)
    requires
        idx < X86_NUM_ENTRIES,
        pt2.region == pt1.region,
        pt2.entries[idx as int] == pt1.entries[idx as int],
        inv_at(tok1, pt1, layer, ptr),
        inv_at(tok2, pt2, layer, ptr),
        entry_at_spec(tok1, pt1, layer, ptr, idx)@ == entry_at_spec(tok2, pt2, layer, ptr, idx)@,
        pt2.entries[idx as int].is_Some() ==> (forall|r: MemRegion| pt2.entries[idx as int].get_Some_0().used_regions.contains(r)
            ==> #[trigger] tok1.regions[r] == tok2.regions[r]),
    ensures
        interp_at_entry(tok1, pt1, layer, ptr, base, idx) == interp_at_entry(tok2, pt2, layer, ptr, base, idx),
    decreases X86_NUM_LAYERS - layer
{
    match entry_at_spec(tok1, pt1, layer, ptr, idx)@ {
        GPDE::Directory { addr: dir_addr, .. } => {
            let e_base = x86_arch_spec.entry_base(layer, base, idx);
            let dir_pt = pt1.entries[idx as int].get_Some_0();
            assert(directories_obey_invariant_at(tok1, pt1, layer, ptr));
            assert(directories_obey_invariant_at(tok2, pt2, layer, ptr));
            lemma_interp_at_aux_facts(tok1, dir_pt, layer + 1, dir_addr, e_base, seq![]);
            lemma_interp_at_aux_facts(tok2, dir_pt, layer + 1, dir_addr, e_base, seq![]);

            assert forall|i: nat| i < X86_NUM_ENTRIES implies
                interp_at_entry(tok1, dir_pt, layer + 1, dir_addr, e_base, i)
                    == interp_at_entry(tok2, dir_pt, layer + 1, dir_addr, e_base, i)
                && #[trigger] interp_at(tok1, dir_pt, layer + 1, dir_addr, e_base).entries[i as int]
                    == interp_at(tok2, dir_pt, layer + 1, dir_addr, e_base).entries[i as int] by
            {
                lemma_interp_at_entry_different_memory(tok1, dir_pt, tok2, dir_pt, layer + 1, dir_addr, e_base, i);
            };
            assert(interp_at(tok1, dir_pt, layer + 1, dir_addr, e_base).entries
                   =~= interp_at(tok2, dir_pt, layer + 1, dir_addr, e_base).entries);
        },
        _ => (),
    }
}

pub proof fn lemma_interp_at_facts(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, ne: bool)
    requires
        inv_at(tok, pt, layer, ptr),
        interp_at(tok, pt, layer, ptr, base_vaddr).inv(ne),
    ensures
        interp_at(tok, pt, layer, ptr, base_vaddr).base_vaddr     == base_vaddr,
        interp_at(tok, pt, layer, ptr, base_vaddr).upper_vaddr()  == x86_arch_spec.upper_vaddr(layer, base_vaddr),
        interp_at(tok, pt, layer, ptr, base_vaddr).interp().lower == base_vaddr,
        interp_at(tok, pt, layer, ptr, base_vaddr).interp().upper == x86_arch_spec.upper_vaddr(layer, base_vaddr),
        ({ let res = interp_at(tok, pt, layer, ptr, base_vaddr);
           forall|j: nat| j < res.entries.len() ==> res.entries[j as int] === #[trigger] interp_at_entry(tok, pt, layer, ptr, base_vaddr, j)
        }),
{
    lemma_interp_at_aux_facts(tok, pt, layer, ptr, base_vaddr, seq![]);
    let res = interp_at(tok, pt, layer, ptr, base_vaddr);
    assert(res.pages_match_entry_size());
    assert(res.directories_are_in_next_layer());
    assert(res.directories_match_arch());
    assert(res.directories_obey_invariant(ne));
    //assert(res.directories_are_nonempty());
    assert(res.frames_aligned());
    res.lemma_inv_implies_interp_inv(ne);
}

proof fn lemma_interp_at_aux_facts(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>)
    requires inv_at(tok, pt, layer, ptr),
    ensures
        interp_at_aux(tok, pt, layer, ptr, base_vaddr, init).len() == if init.len() > X86_NUM_ENTRIES { init.len() } else { X86_NUM_ENTRIES as nat },
        forall|j: nat| j < init.len() ==> #[trigger] interp_at_aux(tok, pt, layer, ptr, base_vaddr, init)[j as int] == init[j as int],
        ({ let res = interp_at_aux(tok, pt, layer, ptr, base_vaddr, init);
            &&& (forall|j: nat|
                #![trigger res[j as int]]
                init.len() <= j && j < res.len() ==>
                match entry_at_spec(tok, pt, layer, ptr, j)@ {
                    GPDE::Directory { addr: dir_addr, .. }  => {
                        &&& res[j as int] is Directory
                        &&& res[j as int]->Directory_0 == interp_at(tok, pt.entries[j as int].get_Some_0(), (layer + 1) as nat, dir_addr, x86_arch_spec.entry_base(layer, base_vaddr, j))
                    },
                    GPDE::Page { addr, .. } => res[j as int] is Page && res[j as int]->Page_0.frame.base == addr,
                    GPDE::Invalid             => res[j as int] is Invalid,
                })
            &&& (forall|j: nat| init.len() <= j && j < res.len() ==> res[j as int] == #[trigger] interp_at_entry(tok, pt, layer, ptr, base_vaddr, j))
        }),
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        assert(directories_obey_invariant_at(tok, pt, layer, ptr));
        let entry = interp_at_entry(tok, pt, layer, ptr, base_vaddr, init.len());
        lemma_interp_at_aux_facts(tok, pt, layer, ptr, base_vaddr, init.push(entry));
    }
}

//fn resolve_aux(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec), ()>)
//    requires
//        inv_at(mem, pt, layer as nat, ptr),
//        interp_at(mem, pt, layer as nat, ptr, base as nat).inv(),
//        interp_at(mem, pt, layer as nat, ptr, base as nat).interp().accepted_resolve(vaddr as nat),
//        base <= vaddr < MAX_BASE,
//    ensures
//        // Refinement of l1
//        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp_at(mem, pt, layer as nat, ptr, base as nat).resolve(vaddr as nat),
//        // Refinement of l0
//        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp_at(mem, pt, layer as nat, ptr, base as nat).interp().resolve(vaddr as nat),
//    // decreases X86_NUM_LAYERS - layer
//{
//    proof { lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat); }
//    let idx: usize = x86_arch_exec().index_for_vaddr(layer, base, vaddr);
//    proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
//    let entry      = entry_at(mem, Ghost(pt), layer, ptr, idx);
//    let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
//    proof {
//        interp@.lemma_resolve_structure_assertions(vaddr as nat, idx as nat);
//        interp@.lemma_resolve_refines(vaddr as nat);
//    }
//    if entry.is_present() {
//        let entry_base: usize = x86_arch_exec().entry_base(layer, base, idx);
//        proof {
//            indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
//            assert(entry_base <= vaddr);
//        }
//        if entry.is_dir(layer) {
//            assert(entry@ is Directory);
//            let dir_addr = entry.address();
//            assert(pt.entries[idx as int].is_Some());
//            let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
//            assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
//            proof {
//                assert(interp@.inv());
//                assert(interp@.directories_obey_invariant());
//                assert(interp@.entries[idx as int] is Directory);
//                assert(interp@.entries[idx as int]->Directory_0.inv());
//                assert(l1::NodeEntry::Directory(interp_at(mem, dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat)) === interp@.entries[idx as int]);
//                assert(inv_at(mem, dir_pt@, (layer + 1) as nat, dir_addr));
//            }
//            let res = resolve_aux(mem, dir_pt, layer + 1, dir_addr, entry_base, vaddr);
//            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
//            res
//        } else {
//            assert(entry@ is Page);
//            assert(interp@.entries[idx as int] is Page);
//            let pte = PageTableEntryExec {
//                frame: MemRegionExec { base: entry.address(), size: x86_arch_exec().entry_size(layer) },
//                flags: entry.flags()
//            };
//            let res = Ok((entry_base, pte));
//            proof {
//            if interp@.resolve(vaddr as nat).is_Ok() {
//                assert(interp@.entries[idx as int]->Page_0 === interp@.resolve(vaddr as nat).get_Ok_0().1);
//                assert(interp@.entries[idx as int] === interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat));
//            }
//            }
//            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).0) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PTE)| v.0));
//            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.frame) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PTE)| v.1.frame));
//            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.flags) === result_map_ok(interp@.resolve(vaddr as nat), |v: (nat, PTE)| v.1.flags));
//            assert(result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
//            res
//        }
//    } else {
//        assert(entry@ is Invalid);
//        assert(interp@.entries[idx as int] is Invalid);
//        assert(result_map_ok(Err(()), |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr as nat));
//        Err(())
//    }
//}

//pub fn resolve(mem: &mem::PageTableMemory, Ghost(pt): Ghost<PTDir>, vaddr: usize) -> (res: Result<(usize, PageTableEntryExec),()>)
//    requires
//        inv(mem, pt),
//        interp(mem, pt).inv(),
//        interp(mem, pt).interp().accepted_resolve(vaddr as nat),
//        vaddr < MAX_BASE,
//    ensures
//        // Refinement of l1
//        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(mem, pt).resolve(vaddr as nat),
//        // Refinement of l0
//        result_map_ok(res, |v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp(mem, pt).interp().resolve(vaddr as nat),
//{
//    let res = resolve_aux(mem, Ghost(pt), 0, mem.cr3().base, 0, vaddr);
//    res
//}

spec fn builder_pre(tok_old: WrappedTokenView, pt_old: PTDir, tok_new: WrappedTokenView, pt_new: PTDir, layer: nat, ptr: usize, new_regions: Set<MemRegion>) -> bool {
    &&& tok_new.pt_mem.pml4 === tok_old.pt_mem.pml4
    // We return the regions that we added
    &&& tok_new.regions.dom() === tok_old.regions.dom().union(new_regions)
    &&& pt_new.used_regions === pt_old.used_regions.union(new_regions)
    // and only those we added
    &&& new_regions.disjoint(tok_old.regions.dom())
    &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt_old.used_regions.contains(r)))
    // Invariant preserved
    &&& inv_at(tok_new, pt_new, layer, ptr)
    // We only touch already allocated regions if they're in pt_old.used_regions
    &&& (forall|r: MemRegion| !(#[trigger] pt_old.used_regions.contains(r)) && !new_regions.contains(r)
        ==> tok_new.regions[r] === tok_old.regions[r])
    &&& pt_new.region === pt_old.region
}

pub open spec fn accepted_mapping(vaddr: nat, pte: PTE) -> bool {
    // Can't map pages in PML4, i.e. layer 0
    &&& x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size, 1)
    &&& pte.frame.base <= MAX_PHYADDR
}

fn map_frame_aux(
    Tracked(tok): Tracked<&mut WrappedMapToken>,
    Ghost(pt): Ghost<PTDir>,
    layer: usize,
    ptr: usize,
    base: usize,
    vaddr: usize,
    pte: PageTableEntryExec,
    Ghost(rebuild_root_pt): Ghost<spec_fn(PTDir, Set<MemRegion>) -> PTDir>,
    ) -> (res: Result<Ghost<(PTDir,Set<MemRegion>)>,()>)
    requires
        inv_at(old(tok)@, pt, layer as nat, ptr),
        interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).inv(true),
        old(tok).inv(),
        //old(tok)@.alloc_available_pages() >= 3 - layer,
        accepted_mapping(vaddr as nat, pte@),
        interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).accepted_mapping(vaddr as nat, pte@),
        old(tok)@.args == (OpArgs::Map { base: vaddr, pte: pte@ }),
        base <= vaddr < MAX_BASE,
        forall|tok_new, pt_new, new_regions|
           #[trigger] builder_pre(old(tok)@, pt, tok_new, pt_new, layer as nat, ptr, new_regions)
               ==> {
                   // TODO: do these only hold in the two specific interp cases?
                   //&&& interp(old(tok)@, rebuild_root_pt(pt, set![])).inv()
                   //&&& interp(old(tok)@, rebuild_root_pt(pt, set![])).accepted_mapping(vaddr as nat, pte@)
                   &&& inv(tok_new, rebuild_root_pt(pt_new, new_regions))
                   &&& interp_at(tok_new, pt_new, layer as nat, ptr, base as nat)
                           == interp_at(old(tok)@, pt, layer as nat, ptr, base as nat)
                        ==> interp(tok_new, rebuild_root_pt(pt_new, new_regions))
                                == interp(old(tok)@, rebuild_root_pt(pt, set![]))
                   &&& Ok(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat))
                           === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)
                        ==> Ok(interp(tok_new, rebuild_root_pt(pt_new, new_regions)))
                                === interp(old(tok)@, rebuild_root_pt(pt, set![])).map_frame(vaddr as nat, pte@)
        }
    ensures
        match res {
            Ok(resv) => {
                let (pt_res, new_regions) = resv@;
                // We return the regions that we added
                &&& tok@.regions.dom() === old(tok)@.regions.dom().union(new_regions)
                &&& pt_res.used_regions === pt.used_regions.union(new_regions)
                // and only those we added
                &&& new_regions.disjoint(old(tok)@.regions.dom())
                &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt.used_regions.contains(r)))
                // Invariant preserved
                &&& inv_at(tok@, pt_res, layer as nat, ptr)
                // We only touch already allocated regions if they're in pt.used_regions
                &&& (forall|r: MemRegion| !(#[trigger] pt.used_regions.contains(r)) && !new_regions.contains(r)
                    ==> tok@.regions[r] === old(tok)@.regions[r])
                &&& pt_res.region === pt.region
            },
            Err(e) => {
                // If error, unchanged
                &&& tok@ === old(tok)@
            },
        },
        // Refinement of l1
        match res {
            Ok(resv) => {
                let (pt_res, new_regions) = resv@;
                Ok(interp_at(tok@, pt_res, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)
            },
            Err(e) =>
                Err(interp_at(tok@, pt, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@),
        },
        tok@.pt_mem.pml4 == old(tok)@.pt_mem.pml4,
        tok.inv(),
    // decreases X86_NUM_LAYERS - layer
{
    proof {
        broadcast use lemma_bitvector_facts_simple;
        broadcast use lemma_union_empty;
        broadcast use l1::lemma_inv_true_implies_inv_false;
        lemma_interp_at_facts(tok@, pt, layer as nat, ptr, base as nat, true);
    }
    let idx: usize = x86_arch_exec.index_for_vaddr(layer, base, vaddr);
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
        lemma_interp_at_aux_facts(old(tok)@, pt, layer as nat, ptr, base as nat, seq![]);
    }
    let entry = entry_at(Tracked(tok), Ghost(pt), layer, ptr, idx);
    proof {
        interp_at(tok@, pt, layer as nat, ptr, base as nat)
            .lemma_map_frame_structure_assertions(vaddr as nat, pte@, idx as nat);
        interp_at(tok@, pt, layer as nat, ptr, base as nat)
            .lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
    }
    let entry_base: usize = x86_arch_exec.entry_base(layer, base, idx);
    proof {
        indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
    }
    if entry.is_present() {
        if entry.is_dir(layer) {
            if x86_arch_exec.entry_size(layer) == pte.frame.size {
                assert(Err(interp_at(tok@, pt, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                Err(())
            } else {
                let dir_addr = entry.address();
                assert(pt.entries[idx as int] is Some);
                let ghost dir_pt = pt.entries[idx as int]->Some_0;
                assert(directories_obey_invariant_at(tok@, pt, layer as nat, ptr));

                let ghost rebuild_root_pt_inner = |pt_new_inner: PTDir, new_regions: Set<MemRegion>| {
                    let pt_new = PTDir {
                        entries: pt.entries.update(idx as int, Some(pt_new_inner)),
                        used_regions: pt.used_regions.union(new_regions),
                        ..pt
                    };
                    rebuild_root_pt(pt_new, new_regions)
                };

                assert(pt.entries =~= PTDir {
                    entries: pt.entries.update(idx as int, Some(dir_pt)),
                    used_regions: pt.used_regions.union(set![]),
                    ..pt
                }.entries);
                assert(forall|s: Set<MemRegion>| s.union(set![]) =~= s);
                assert(rebuild_root_pt_inner(dir_pt, set![]) == rebuild_root_pt(pt, set![]));

                assert forall|tok_new, pt_new_inner, new_regions|
                   #[trigger] builder_pre(tok@, dir_pt, tok_new, pt_new_inner, layer as nat + 1, dir_addr, new_regions)
                   implies {
                       &&& inv(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))
                       &&& interp_at(tok_new, pt_new_inner, layer as nat + 1, dir_addr, entry_base as nat)
                               == interp_at(tok@, dir_pt, layer as nat + 1, dir_addr, entry_base as nat)
                            ==> interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))
                                    == interp(tok@, rebuild_root_pt_inner(dir_pt, set![]))
                       &&& Ok(interp_at(tok_new, pt_new_inner, layer as nat + 1, dir_addr, entry_base as nat))
                               === interp_at(tok@, dir_pt, layer as nat + 1, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@)
                            ==> Ok(interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions)))
                                    === interp(tok@, rebuild_root_pt_inner(dir_pt, set![])).map_frame(vaddr as nat, pte@)
                   }
                by {
                    assert(pt_new_inner.used_regions === dir_pt.used_regions.union(new_regions));
                    assert(inv_at(tok_new, pt_new_inner, (layer + 1) as nat, dir_addr));
                    //assert(Ok(interp_at(tok_new, pt_new_inner, (layer + 1) as nat, dir_addr, entry_base as nat))
                    //       === interp_at(old(tok_new)@, dir_pt, (layer + 1) as nat, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@));
                    let ghost pt_new =
                        PTDir {
                            region: pt.region,
                            entries: pt.entries.update(idx as int, Some(pt_new_inner)),
                            used_regions: pt.used_regions.union(new_regions),
                        };

                    assert(!new_regions.contains(pt_new.region));
                    assert(!pt_new_inner.used_regions.contains(pt_new.region));

                    // None of the entries at this level change
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies
                        #[trigger] entry_at_spec(tok_new, pt_new, layer as nat, ptr, i) == entry_at_spec(old(tok)@, pt, layer as nat, ptr, i) by { };

                    assert(inv_at(tok_new, pt_new, layer as nat, ptr)) by {
                        assert(ghost_pt_matches_structure(tok_new, pt_new, layer as nat, ptr));

                        assert(ghost_pt_used_regions_rtrancl(tok_new, pt_new, layer as nat, ptr));
                        assert(ghost_pt_region_notin_used_regions(tok_new, pt_new, layer as nat, ptr));
                        assert(ghost_pt_used_regions_pairwise_disjoint(tok_new, pt_new, layer as nat, ptr));

                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                            let entry = #[trigger] entry_at_spec(tok_new, pt_new, layer as nat, ptr, i)@;
                            entry is Directory ==> {
                                &&& inv_at(tok_new, pt_new.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)
                            }
                        } by {
                            let entry = entry_at_spec(tok_new, pt_new, layer as nat, ptr, i)@;
                            if i != idx && entry is Directory {
                                lemma_inv_at_different_memory(tok@, tok_new, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                            }
                        };
                        assert(directories_obey_invariant_at(tok_new, pt_new, layer as nat, ptr));
                        assert(inv_at(tok_new, pt_new, layer as nat, ptr));
                    };

                    assert(inv_at(tok@, pt, layer as nat, ptr));
                    assert(tok@ == old(tok)@);

                    assert forall |r| !(pt.used_regions.contains(r)) && !(new_regions.contains(r)) implies #[trigger]tok_new.regions[r] === tok@.regions[r] by {
                        assert(!dir_pt.used_regions.contains(r)); 
                        if tok_new.regions.contains_key(r) {
                            assert(tok_new.regions[r] == tok@.regions[r]);
                        } else {
                            assert(!tok@.regions.contains_key(r));
                        }
                    }
                    
                    assert(builder_pre(tok@, pt, tok_new, pt_new, layer as nat, ptr, new_regions));
                    assert(inv(tok_new, rebuild_root_pt(pt_new, new_regions)));

                    // Prove the first interp property for the new builder
                    if interp_at(tok_new, pt_new_inner, layer as nat + 1, dir_addr, entry_base as nat)
                           == interp_at(tok@, dir_pt, layer as nat + 1, dir_addr, entry_base as nat)
                    {
                        assert(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat)
                                == interp_at(old(tok)@, pt, layer as nat, ptr, base as nat))
                        by {
                             lemma_interp_at_aux_facts(tok_new, pt_new, layer as nat, ptr, base as nat, seq![]);
                             assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                                     interp_at(tok_new, pt_new, layer as nat, ptr, base as nat).entries[i as int]
                                     === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).entries[i as int] by
                             {
                                 lemma_interp_at_entry_different_memory(old(tok)@, pt, tok_new, pt_new, layer as nat, ptr, base as nat, i);
                             };
                             assert(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat).entries
                                 =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).entries);
                        };
                        assert(interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions)) == interp(tok@, rebuild_root_pt_inner(dir_pt, set![])));
                    }

                    // Prove the second interp property for the new builder
                    if Ok(interp_at(tok_new, pt_new_inner, layer as nat + 1, dir_addr, entry_base as nat))
                           === interp_at(tok@, dir_pt, layer as nat + 1, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@)
                    {
                         assert(Ok(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat))
                                 === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@))
                         by {
                             lemma_interp_at_aux_facts(tok_new, pt_new, layer as nat, ptr, base as nat, seq![]);

                             assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                                     interp_at(tok_new, pt_new, layer as nat, ptr, base as nat).entries[i as int]
                                     === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                             {
                                 if pt_new.entries[i as int] is Some {
                                     let pt_entry = pt_new.entries[i as int].get_Some_0();
                                     assert(ghost_pt_used_regions_pairwise_disjoint(tok_new, pt_new, layer as nat, ptr));
                                     assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                            implies !new_regions.contains(r)
                                    by {
                                         assert(pt_entry.used_regions.contains(r));
                                         assert(old(tok)@.regions.contains_key(r));
                                     };
                                     assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                            ==> !pt_new_inner.used_regions.contains(r));
                                     assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                            ==> #[trigger] old(tok)@.regions[r] === tok_new.regions[r]);
                                 }
                                 lemma_interp_at_entry_different_memory(old(tok)@, pt, tok_new, pt_new, layer as nat, ptr, base as nat, i);
                                 assert(interp_at_entry(tok_new, pt_new, layer as nat, ptr, base as nat, i) === interp_at_entry(old(tok)@, pt, layer as nat, ptr, base as nat, i));
                             };

                             assert(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat).entries[idx as int] === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                             assert(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat).entries =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                             assert(Ok(interp_at(tok_new, pt_new, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                         };
                    }
                };

                match map_frame_aux(Tracked(tok), Ghost(dir_pt), layer + 1, dir_addr, entry_base, vaddr, pte, Ghost(rebuild_root_pt_inner)) {
                    Ok(rec_res) => {
                        let ghost dir_pt_res = rec_res@.0;
                        let ghost new_regions = rec_res@.1;

                        assert(dir_pt_res.used_regions === dir_pt.used_regions.union(new_regions));
                        assert(inv_at(tok@, dir_pt_res, (layer + 1) as nat, dir_addr));
                        assert(Ok(interp_at(tok@, dir_pt_res, (layer + 1) as nat, dir_addr, entry_base as nat))
                               === interp_at(old(tok)@, dir_pt, (layer + 1) as nat, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@));
                        let ghost pt_res =
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, Some(dir_pt_res)),
                                used_regions: pt.used_regions.union(new_regions),
                            };

                        assert(!new_regions.contains(pt_res.region));
                        assert(!dir_pt_res.used_regions.contains(pt_res.region));

                        // None of the entries at this level change
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            entry_at_spec(tok@, pt_res, layer as nat, ptr, i) == entry_at_spec(old(tok)@, pt, layer as nat, ptr, i) by { };

                        assert(inv_at(tok@, pt_res, layer as nat, ptr)
                            && Ok(interp_at(tok@, pt_res, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by
                        {
                            //assert forall|i: nat| i < X86_NUM_ENTRIES
                            //    implies {
                            //        let entry = entry_at_spec(tok@, pt_res, layer as nat, ptr, i)@;
                            //        entry is Directory == (#[trigger] pt_res.entries[i as int]).is_Some()
                            //    }
                            //by {
                            //    assert(tok@.regions[pt_res.region] === tok@.regions[pt_res.region]);
                            //    let entry = entry_at_spec(tok@, pt_res, layer as nat, ptr, i)@;
                            //    if i == idx {
                            //    } else {
                            //        assert(pt.entries[i as int] === pt_res.entries[i as int]);
                            //        assert(entry === entry_at_spec(old(tok)@, pt, layer as nat, ptr, i)@);
                            //        assert(entry is Directory == pt_res.entries[i as int].is_Some());
                            //    }
                            //};
                            assert(ghost_pt_matches_structure(tok@, pt_res, layer as nat, ptr));

                            assert(ghost_pt_used_regions_rtrancl(tok@, pt_res, layer as nat, ptr));
                            assert(ghost_pt_region_notin_used_regions(tok@, pt_res, layer as nat, ptr));
                            //assert forall|i: nat, j: nat, r: MemRegion|
                            //    i != j &&
                            //    i < pt_res.entries.len() && pt_res.entries[i as int].is_Some() &&
                            //    #[trigger] pt_res.entries[i as int].get_Some_0().used_regions.contains(r) &&
                            //    j < pt_res.entries.len() && pt_res.entries[j as int].is_Some()
                            //    implies !(#[trigger] pt_res.entries[j as int].get_Some_0().used_regions.contains(r)) by
                            //{
                            //    assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt, layer as nat, ptr));
                            //    if j == idx {
                            //        assert(pt_res.entries[j as int].get_Some_0() === dir_pt_res);
                            //        assert(pt_res.entries[i as int] === pt.entries[i as int]);
                            //        if new_regions.contains(r) {
                            //            assert(!dir_pt.used_regions.contains(r));
                            //            assert(!old(tok)@.regions.contains_key(r));
                            //            assert(!dir_pt_res.used_regions.contains(r));
                            //        } else {
                            //            if dir_pt.used_regions.contains(r) {
                            //                assert(pt.used_regions.contains(r));
                            //                assert(old(tok)@.regions.contains_key(r));
                            //                assert(!dir_pt_res.used_regions.contains(r));
                            //            }
                            //        }
                            //    } else {
                            //        if i == idx {
                            //            assert(pt_res.entries[i as int].get_Some_0() === dir_pt_res);
                            //            assert(pt_res.entries[j as int] === pt.entries[j as int]);
                            //            if new_regions.contains(r) {
                            //                assert(dir_pt_res.used_regions.contains(r));
                            //                assert(!dir_pt.used_regions.contains(r));
                            //                assert(!old(tok)@.regions.contains_key(r));
                            //                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                            //            } else {
                            //                assert(dir_pt.used_regions.contains(r));
                            //                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                            //            }
                            //        } else {
                            //            assert(pt_res.entries[i as int] === pt.entries[i as int]);
                            //            assert(pt_res.entries[j as int] === pt.entries[j as int]);
                            //        }
                            //    }
                            //};
                            assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt_res, layer as nat, ptr));

                            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                let entry = #[trigger] entry_at_spec(tok@, pt_res, layer as nat, ptr, i)@;
                                entry is Directory ==> {
                                    &&& inv_at(tok@, pt_res.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)
                                }
                            }
                            by {
                                let entry = entry_at_spec(tok@, pt_res, layer as nat, ptr, i)@;
                                if i != idx && entry is Directory {
                                    lemma_inv_at_different_memory(old(tok)@, tok@, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                                }
                                //if i == idx {
                                //    //assert(pt_res.entries[i as int].get_Some_0() === dir_pt_res);
                                //    //assert(entry->Directory_addr === dir_addr);
                                //    //assert(inv_at(tok@, pt_res.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr));
                                //} else {
                                //    assert(directories_obey_invariant_at(old(tok)@, pt, layer as nat, ptr));
                                //    //assert(pt.entries[i as int] === pt_res.entries[i as int]);
                                //    //assert(entry === entry_at_spec(old(tok)@, pt, layer as nat, ptr, i)@);
                                //    assert(entry === entry_at_spec(old(tok)@, pt_res, layer as nat, ptr, i)@);
                                //    if entry is Directory {
                                //        //let pt_entry = pt_res.entries[i as int].get_Some_0();
                                //        //assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt_res, layer as nat, ptr));
                                //        //assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                //        //       implies !new_regions.contains(r) by
                                //        //{
                                //        //    assert(pt_entry.used_regions.contains(r));
                                //        //    assert(old(tok)@.regions.contains_key(r));
                                //        //};
                                //        //assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                //        //       ==> !dir_pt.used_regions.contains(r));
                                //        //assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                //        //       ==> #[trigger] tok@.regions[r] === tok@.regions[r]);
                                //        //assert(inv_at(old(tok)@, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr));
                                //        //assert(forall|r: MemRegion| pt_res.entries[i as int].get_Some_0().used_regions.contains(r)
                                //        //       ==> #[trigger] tok@.regions[r] === old(tok)@.regions[r]);
                                //        //assert(pt_res.entries[i as int].is_Some());
                                //        //assert(pt_res.entries[i as int].get_Some_0().used_regions === pt.entries[i as int].get_Some_0().used_regions);
                                //        lemma_inv_at_different_memory(old(tok)@, tok@, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                                //        assert(inv_at(tok@, pt_res.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr));
                                //    }
                                //}
                            };
                            assert(directories_obey_invariant_at(tok@, pt_res, layer as nat, ptr));
                            assert(inv_at(tok@, pt_res, layer as nat, ptr));

                            assert(Ok(interp_at(tok@, pt_res, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                                lemma_interp_at_aux_facts(tok@, pt_res, layer as nat, ptr, base as nat, seq![]);
                                assert(pt_res.region === pt.region);
                                // recursive postcondition:
                                assert(Ok(interp_at(tok@, dir_pt_res, (layer + 1) as nat, dir_addr, entry_base as nat))
                                       === interp_at(old(tok)@, dir_pt, (layer + 1) as nat, dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@));
                                //assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt.entries[i as int] === pt_res.entries[i as int]);

                                assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                                        interp_at(tok@, pt_res, layer as nat, ptr, base as nat).entries[i as int]
                                        === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                                {
                                    //assert(interp_at(tok@, pt_res, layer as nat, ptr, base as nat).entries[i as int] === interp_at_entry(tok@, pt_res, layer as nat, ptr, base as nat, i));
                                    //assert(interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).entries[i as int] === interp_at_entry(old(tok)@, pt, layer as nat, ptr, base as nat, i));
                                    if pt_res.entries[i as int] is Some {
                                        let pt_entry = pt_res.entries[i as int].get_Some_0();
                                        assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt_res, layer as nat, ptr));
                                        assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               implies !new_regions.contains(r)
                                       by {
                                            assert(pt_entry.used_regions.contains(r));
                                            assert(old(tok)@.regions.contains_key(r));
                                        };
                                        assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                               ==> !dir_pt_res.used_regions.contains(r));
                                        assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                               ==> #[trigger] old(tok)@.regions[r] === tok@.regions[r]);
                                    }
                                    lemma_interp_at_entry_different_memory(old(tok)@, pt, tok@, pt_res, layer as nat, ptr, base as nat, i);
                                    assert(interp_at_entry(tok@, pt_res, layer as nat, ptr, base as nat, i) === interp_at_entry(old(tok)@, pt, layer as nat, ptr, base as nat, i));
                                };

                                assert(interp_at(tok@, pt_res, layer as nat, ptr, base as nat).entries[idx as int] === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                                assert(interp_at(tok@, pt_res, layer as nat, ptr, base as nat).entries =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                                assert(Ok(interp_at(tok@, pt_res, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                            };
                        };

                        // posts
                        assert forall|r: MemRegion| !pt.used_regions.contains(r) && !new_regions.contains(r)
                           implies #[trigger] tok@.regions[r] === old(tok)@.regions[r]
                           by { assert(!dir_pt.used_regions.contains(r)); };
                        assert(tok@.regions.dom() === old(tok)@.regions.dom().union(new_regions));
                        assert(pt_res.used_regions === pt.used_regions.union(new_regions));
                        assert(pt_res.region === pt.region);

                        Ok(Ghost((pt_res,new_regions)))
                    },
                    Err(e) => {
                        assert(Err(interp_at(tok@, pt, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                        Err(e)
                    },
                }
            }
        } else {
            assert(Err(interp_at(tok@, pt, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
            Err(())
        }
    } else {
        if x86_arch_exec.entry_size(layer) == pte.frame.size {
            proof {
                assert_by_contradiction!(layer > 0, {
                    let iprime = choose|i: nat| 0 < i && i < X86_NUM_LAYERS && #[trigger] x86_arch_spec.entry_size(i) == pte.frame.size;
                    //assert(x86_arch_spec.entry_size(0) == pte.frame.size);
                    //assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1));
                    assert forall|i: nat| 0 < i < X86_NUM_LAYERS implies
                        x86_arch_spec.entry_size(0) >= #[trigger] x86_arch_spec.entry_size(i)
                    by {
                        x86_arch_spec.lemma_entry_sizes_increase(0, i);
                    };
                    assert(false);
                });
                assert(addr_is_zero_padded(layer as nat, pte.frame.base, true)) by {
                    lemma_aligned_addr_mask_facts(pte.frame.base);
                };
                assert(pte.frame.base & MASK_ADDR == pte.frame.base) by {
                    lemma_aligned_addr_mask_facts(pte.frame.base);
                };
            }
            let new_page_entry = PDE::new_page_entry(layer, pte);
            let ghost pwtok = tok@;

            proof {
                lemma_bitvector_facts();
                assert(new_page_entry.entry & 1 == 1);
                assert(tok@.read(idx, pt.region) & 1 == 0);

                // This is the token state we'll have after the write happened
                let tok_after_write = tok@.write(idx, new_page_entry.entry, pt.region);

                // And that state will satisfy the invariant
                assert(inv_at(tok_after_write, pt, layer as nat, ptr)) by {
                    lemma_bitvector_facts();
                    assert(tok_after_write.regions[pt.region] === pwtok.regions[pt.region].update(idx as int, new_page_entry.entry));

                    assert forall|i: nat| #![auto] i < X86_NUM_ENTRIES implies
                        entry_at_spec(tok_after_write, pt, layer as nat, ptr, i)@
                        == if i == idx { new_page_entry@ } else { entry_at_spec(old(tok)@, pt, layer as nat, ptr, i)@ } by { };

                    assert(directories_obey_invariant_at(tok_after_write, pt, layer as nat, ptr)) by {
                        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                            let entry = #[trigger] entry_at_spec(tok_after_write, pt, layer as nat, ptr, i)@;
                            entry is Directory ==>
                                inv_at(tok_after_write, pt.entries[i as int]->Some_0, (layer + 1) as nat, entry->Directory_addr)
                        } by {
                            let entry = entry_at_spec(tok_after_write, pt, layer as nat, ptr, i)@;
                            assert(directories_obey_invariant_at(old(tok)@, pt, layer as nat, ptr));
                            if i != idx && entry is Directory {
                                lemma_inv_at_different_memory(old(tok)@, tok_after_write, pt.entries[i as int]->Some_0, (layer + 1) as nat, entry->Directory_addr);
                            }
                        };
                    };
                }

                assert(tok_after_write.regions.dom() == tok@.regions.dom().union(set![]));
                assert(builder_pre(tok@, pt, tok_after_write, pt, layer as nat, ptr, set![]));

                assert(Ok(interp(tok_after_write, rebuild_root_pt(pt, set![])))
                         === interp(old(tok)@, rebuild_root_pt(pt, set![])).map_frame(vaddr as nat, pte@))
                by {
                    assert(Ok(interp_at(tok_after_write, pt, layer as nat, ptr, base as nat))
                             === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@))
                    by {
                        lemma_interp_at_aux_facts(tok_after_write, pt, layer as nat, ptr, base as nat, seq![]);

                        assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                                interp_at(tok_after_write, pt, layer as nat, ptr, base as nat).entries[i as int]
                                === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                        {
                            lemma_interp_at_entry_different_memory(old(tok)@, pt, tok_after_write, pt, layer as nat, ptr, base as nat, i);
                        };

                        let new_interp = interp_at(tok_after_write, pt, layer as nat, ptr, base as nat);
                        assert(interp_at_entry(tok_after_write, pt, layer as nat, ptr, base as nat, idx as nat) === l1::NodeEntry::Page(pte@));
                        assert(new_interp.entries =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                        assert(Ok(new_interp) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                    };
                };


                // The old and new interps match the MMU interp.
                // We need this because the `write_change` precondition is expressed in terms of
                // the MMU interp.
                assert(interp_to_l0(old(tok)@, rebuild_root_pt(pt, set![])) == old(tok)@.interp()) by {
                    assert(builder_pre(old(tok)@, pt, old(tok)@, pt, layer as nat, ptr, set![]));
                    old(tok)@.lemma_interps_match(rebuild_root_pt(pt, set![]));
                };
                assert(interp_to_l0(tok_after_write, rebuild_root_pt(pt, set![])) == tok_after_write.interp()) by {
                    tok_after_write.lemma_interps_match(rebuild_root_pt(pt, set![]));
                };
                // TODO: These need to be part of the properties the builder provides i think
                // Note after making l1 invariant non-emptiness conditional: This may be a bit
                // trickier now because I'm not sure we can easily use the map_frame refinement to
                // prove this. We may have to instead reason directly about the interpretation and
                // change the map_frame condition.
                assume(interp(old(tok)@, rebuild_root_pt(pt, set![])).inv(true));
                assume(interp(old(tok)@, rebuild_root_pt(pt, set![])).accepted_mapping(vaddr as nat, pte@));
                interp(old(tok)@, rebuild_root_pt(pt, set![])).lemma_map_frame_refines_map_frame(vaddr as nat, pte@);
                assume(interp(tok_after_write, rebuild_root_pt(pt, set![])).inv(true));
                //assume(interp(tok_new@, rebuild_root_pt(pt_new, new_regions)).accepted_mapping(vaddr as nat, pte@));
                //interp(tok_after_write, rebuild_root_pt(pt, set![])).lemma_map_frame_refines_map_frame(vaddr as nat, pte@);

                //assert(Ok(interp(old(tok)@, rebuild_root_pt(pt, set![])).map_frame(vaddr as nat, pte@).get_Ok_0().interp())
                //    === interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().map_frame(vaddr as nat, pte@));
                //assert(Ok(interp(tok_after_write, rebuild_root_pt(pt, set![])))
                //         === interp(old(tok)@, rebuild_root_pt(pt, set![])).map_frame(vaddr as nat, pte@));
                //assert(Ok(interp(tok_after_write, rebuild_root_pt(pt, set![])).interp())
                //    === interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().map_frame(vaddr as nat, pte@));
                interp(old(tok)@, rebuild_root_pt(pt, set![])).lemma_accepted_mapping_implies_interp_accepted_mapping_manual(vaddr as nat, pte@, true);
                //assert(interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().accepted_mapping(vaddr as nat, pte@));
                assert(interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().valid_mapping(vaddr as nat, pte@));
                assert(!candidate_mapping_overlaps_existing_vmem_usize(tok@.interp(), vaddr, pte@));
                //assert(
                //    interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().map_frame(vaddr as nat, pte@).get_Ok_0().map
                //        === interp(old(tok)@, rebuild_root_pt(pt, set![])).interp().map.insert(vaddr as nat, pte@)
                //);
                assert(tok_after_write.interp() == tok@.interp().insert(vaddr, pte@));
            }
            WrappedMapToken::write_change(Tracked(tok), ptr, idx, new_page_entry.entry, Ghost(pt.region));

            // TODO: this is mostly a duplicate from the interp thing above. Can we get rid of the
            // corresponding postcondition? (We shouldn't need it anymore once this thing is fully
            // converted to the new interface)
            assert(Ok(interp_at(tok@, pt, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                lemma_interp_at_aux_facts(tok@, pt, layer as nat, ptr, base as nat, seq![]);

                assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx implies
                        interp_at(tok@, pt, layer as nat, ptr, base as nat).entries[i as int]
                        === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries[i as int] by
                {
                    lemma_interp_at_entry_different_memory(old(tok)@, pt, tok@, pt, layer as nat, ptr, base as nat, i);
                };

                let new_interp = interp_at(tok@, pt, layer as nat, ptr, base as nat);
                assert(interp_at_entry(tok@, pt, layer as nat, ptr, base as nat, idx as nat) === l1::NodeEntry::Page(pte@));
                assert(new_interp.entries =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                assert(Ok(new_interp) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
            };

            // posts
            assert(forall|r: MemRegion| !pt.used_regions.contains(r) ==> #[trigger] tok@.regions[r] === old(tok)@.regions[r]);
            assert(tok@.regions.dom() =~= old(tok)@.regions.dom().union(set![]));
            assert(pt.used_regions.union(set![]) =~= pt.used_regions);

            Ok(Ghost((pt, set![])))
        } else {
            let (Ghost(pt_with_empty), new_dir_region, new_dir_entry) = insert_empty_directory(Tracked(tok), Ghost(pt), layer, ptr, base, idx);
            let ghost new_dir_pt = pt_with_empty.entries[idx as int].get_Some_0();
            let new_dir_addr = new_dir_region.base;
            let ghost tok_with_empty = tok@;
            //assert forall|i: nat| i < X86_NUM_ENTRIES implies
            //    #[trigger] entry_at_spec(tok@, pt_with_empty@, layer as nat, ptr, i)
            //    == if i == idx { new_dir_entry } else { entry_at_spec(tok_with_empty, pt_with_empty@, layer as nat, ptr, i) } by { };
            assert(inv_at(tok_with_empty, pt_with_empty, layer as nat, ptr));

            // TODO: instead of rebuild_root_pt this may have to use a closure we get back from
            // insert_empty_directory above.
            let ghost rebuild_root_pt_inner = |pt_new_inner: PTDir, new_regions: Set<MemRegion>| {
                let pt_new = PTDir {
                    entries: pt_with_empty.entries.update(idx as int, Some(pt_new_inner)),
                    used_regions: pt_with_empty.used_regions.union(new_regions),
                    ..pt_with_empty
                };
                rebuild_root_pt(pt_new, new_regions)
            };

            // these parts of the pre-condition are fine
            assert(inv_at(tok@, new_dir_pt, (layer + 1) as nat, new_dir_addr));
            assert(interp_at(tok@, new_dir_pt, (layer + 1) as nat, new_dir_addr, entry_base as nat).inv(true));
            assert(tok.inv());
            assert(accepted_mapping(vaddr as nat, pte@));
            assert(interp_at(tok@, new_dir_pt, (layer + 1) as nat, new_dir_addr, entry_base as nat).accepted_mapping(vaddr as nat, pte@));
            assert(base <= vaddr < MAX_BASE);

            assert(pt.entries.len() == X86_NUM_ENTRIES);

            
            assert(forall|i: nat| #![auto] i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(tok_with_empty, pt_with_empty, layer as nat, ptr, i)@ == entry_at_spec(old(tok)@, pt, layer as nat, ptr, i)@) by {};
            assert(entry_at_spec(tok_with_empty, pt_with_empty, layer as nat, ptr, idx as nat) == new_dir_entry);
            assert(entry_at_spec(tok_with_empty, pt_with_empty, layer as nat, ptr, idx as nat)@ is Directory);
            assert(entry_at_spec(old(tok)@, pt, layer as nat, ptr, idx as nat)@ is Invalid);

            assert(pt_with_empty.entries =~= PTDir {
                entries: pt_with_empty.entries.update(idx as int, Some(new_dir_pt)),
                used_regions: pt_with_empty.used_regions.union(set![new_dir_region@]),
                ..pt_with_empty
            }.entries);
            assert(forall|s: Set<MemRegion>| s.union(set![]) =~= s);
            assert(rebuild_root_pt_inner(new_dir_pt, set![]) == rebuild_root_pt(pt_with_empty, set![]));

            assert forall|tok_new, pt_new_inner, new_regions|
               #[trigger] builder_pre(tok@, new_dir_pt, tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, new_regions)
               implies {
                   &&& inv(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))
                   &&& interp_at(tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, entry_base as nat)
                           == interp_at(tok@, new_dir_pt, layer as nat + 1, new_dir_addr, entry_base as nat)
                        ==> interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))
                                === interp(tok@, rebuild_root_pt_inner(new_dir_pt, set![]))
                   &&& Ok(interp_at(tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, entry_base as nat))
                           === interp_at(tok@, new_dir_pt, layer as nat + 1, new_dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@)
                        ==> Ok(interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions)))
                                === interp(tok@, rebuild_root_pt_inner(new_dir_pt, set![])).map_frame(vaddr as nat, pte@)
               }
            by {
            //     assert(builder_pre(tok@, new_dir_pt, tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, new_regions));
            //     assert(pt_new_inner.used_regions === new_dir_pt.used_regions.union(new_regions));
            //     assert(inv_at(tok_new, pt_new_inner, (layer + 1) as nat, new_dir_addr));

                let ghost pt_new =
                PTDir {
                    region: pt_with_empty.region,
                    entries: pt_with_empty.entries.update(idx as int, Some(pt_new_inner)),
                    used_regions: pt_with_empty.used_regions.union(new_regions),
                };

                assert(!new_regions.contains(pt_new.region));
                assert(!pt_new_inner.used_regions.contains(pt_new.region));

                // none of the entries changed, except the one we've updated
                assert(forall|i: nat| #![auto] i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(tok_new, pt_new, layer as nat, ptr, i)@ == entry_at_spec(tok_with_empty, pt_with_empty, layer as nat, ptr, i)@) by {};
                
                assert(entry_at_spec(tok_new, pt_new, layer as nat, ptr, idx as nat) == new_dir_entry);
                assert(entry_at_spec(tok_new, pt_new, layer as nat, ptr, idx as nat)@ is Directory);
                assert(entry_at_spec(old(tok)@, pt, layer as nat, ptr, idx as nat)@ is Invalid);
 

                assert(inv_at(tok_new, pt_new, layer as nat, ptr)) by {
                    assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        let entry = #[trigger] entry_at_spec(tok_new, pt_new, layer as nat, ptr, i)@;
                        entry is Directory ==> {
                            &&& inv_at(tok_new, pt_new.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)
                        }
                    } by {
                        let entry = entry_at_spec(tok_new, pt_new, layer as nat, ptr, i)@;
                        if i == idx {
                            // updated entry
                            assert(entry is Directory);
                            assert(inv_at(tok@, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)) by { admit(); }
                            assert(tok_new.regions.contains_key(pt.entries[i as int].get_Some_0().region)) by { admit(); };

                            assert(forall|r: MemRegion| pt.entries[i as int].get_Some_0().used_regions.contains(r) ==> #[trigger] tok@.regions[r] === tok_new.regions[r]) by { admit(); };

                            // assert(tok_new.regions == tok@.regions) by { admit(); }
                            lemma_inv_at_different_memory(tok@, tok_new, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr) 
                        } else {
                            if entry is Directory {
                                assert(tok_new.regions.contains_key(pt.entries[i as int].get_Some_0().region)) by { admit(); };
                                lemma_inv_at_different_memory(tok@, tok_new, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                            }
                        }
                    }
                    assert(directories_obey_invariant_at(tok_new, pt_new, layer as nat, ptr));
                }


            //     assert(inv_at(old(tok)@, pt, layer as nat, ptr));
            //     assert(tok@ == tok_with_empty);

            //     assert forall |r| !(pt_with_empty.used_regions.contains(r)) && !(new_regions.contains(r)) implies #[trigger]tok_new.regions[r] === tok_with_empty.regions[r] by {
            //         assert(!new_dir_pt.used_regions.contains(r)); 
            //         if tok_new.regions.contains_key(r) {
            //             assert(tok_new.regions[r] == tok_with_empty.regions[r]);
            //         } else {
            //             assert(!tok_with_empty.regions.contains_key(r));
            //         }
            //     }

            //     assert(builder_pre(tok_with_empty, pt_with_empty, tok_new, pt_new, layer as nat, ptr, new_regions));
            //     assert(inv(tok_new, rebuild_root_pt(pt_new, new_regions))) by {
            //         assert(rebuild_root_pt(pt_new, new_regions).region.size == PAGE_SIZE) by { admit(); } 
            //         assert(tok_new.pt_mem.pml4 % PAGE_SIZE == 0) by { admit(); }
            //         assert(tok_new.regions.contains_key(rebuild_root_pt(pt_new, new_regions).region)) by { admit(); };
            //     }
 
            //     assert(inv(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))) by { }
                assert(inv(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))) by { admit(); }
                
                if interp_at(tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, entry_base as nat)
                        == interp_at(tok@, new_dir_pt, layer as nat + 1, new_dir_addr, entry_base as nat) {

                    assert(interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions))  == interp(tok@, rebuild_root_pt_inner(new_dir_pt, set![]))) by {  
                        lemma_interp_at_aux_facts(tok_new, pt_new, layer as nat, ptr, base as nat, seq![]);
                        admit();
                    }
                }

            //     if Ok(interp_at(tok_new, pt_new_inner, layer as nat + 1, new_dir_addr, entry_base as nat))
            //             === interp_at(tok@, new_dir_pt, layer as nat + 1, new_dir_addr, entry_base as nat).map_frame(vaddr as nat, pte@) {
                    
            //         assert(Ok(interp(tok_new, rebuild_root_pt_inner(pt_new_inner, new_regions)))
            //             === interp(tok@, rebuild_root_pt_inner(new_dir_pt, set![])).map_frame(vaddr as nat, pte@)) by { admit(); }
            //     }                    
                admit();
            };



            match map_frame_aux(Tracked(tok), Ghost(new_dir_pt), layer + 1, new_dir_addr, entry_base, vaddr, pte, Ghost(rebuild_root_pt_inner)) {
                Ok(rec_res) => {
                    //let ghost dir_new_regions = rec_res@.1;
                    let ghost pt_final =
                        PTDir {
                            region:       pt_with_empty.region,
                            entries:      pt_with_empty.entries.update(idx as int, Some(rec_res@.0)),
                            used_regions: pt_with_empty.used_regions.union(rec_res@.1),
                        };
                    let ghost new_regions = rec_res@.1.insert(new_dir_region@);
                    proof {
                        //assert(!dir_new_regions.contains(pt_final.region));
                        assert(!new_dir_pt.used_regions.contains(pt_final.region));

                        assert forall|i: nat| i < X86_NUM_ENTRIES implies
                            #[trigger] entry_at_spec(tok@, pt_final, layer as nat, ptr, i)
                            == if i == idx { new_dir_entry } else { entry_at_spec(tok_with_empty, pt_with_empty, layer as nat, ptr, i) } by { };
                        assert(inv_at(tok@, pt_final, layer as nat, ptr)) by {
                            //assert(ghost_pt_matches_structure(tok@, pt_final, layer as nat, ptr)) by {
                            //    assert forall|i: nat|
                            //        i < X86_NUM_ENTRIES implies {
                            //            let entry = #[trigger] entry_at_spec(tok@, pt_final, layer as nat, ptr, i)@;
                            //            entry is Directory == pt_final.entries[i as int].is_Some()
                            //    } by {
                            //        assert(directories_obey_invariant_at(tok_with_empty, pt_with_empty@, layer as nat, ptr));
                            //        assert(ghost_pt_matches_structure(tok_with_empty, pt_with_empty@, layer as nat, ptr));
                            //        if i == idx { } else { }
                            //    };
                            //};

                            assert(directories_obey_invariant_at(tok@, pt_final, layer as nat, ptr)) by {
                                assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                                    let entry = #[trigger] entry_at_spec(tok@, pt_final, layer as nat, ptr, i)@;
                                    entry is Directory
                                        ==> inv_at(tok@, pt_final.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)
                                } by {
                                    let entry = entry_at_spec(tok@, pt_final, layer as nat, ptr, i)@;
                                    assert(directories_obey_invariant_at(tok_with_empty, pt_with_empty, layer as nat, ptr));
                                    if i != idx && entry is Directory {
                                        lemma_inv_at_different_memory(tok_with_empty, tok@, pt_with_empty.entries[i as int]->Some_0, (layer + 1) as nat, entry->Directory_addr);
                                    }
                                    //assert(directories_obey_invariant_at(tok_with_empty, pt_with_empty@, layer as nat, ptr));
                                    //assert(ghost_pt_matches_structure(tok_with_empty, pt_with_empty@, layer as nat, ptr));
                                    //assert(ghost_pt_used_regions_rtrancl(tok_with_empty, pt_with_empty@, layer as nat, ptr));

                                    //if i == idx {
                                    //} else {
                                    //    assert(entry == entry_at_spec(tok_with_empty, pt_with_empty@, layer as nat, ptr, i)@);
                                    //    assert(pt_final.entries[i as int] === pt_with_empty@.entries[i as int]);
                                    //    if entry is Directory {
                                    //        assert(pt_with_empty@.entries[i as int].is_Some());
                                    //        let pt_entry = pt_with_empty@.entries[i as int].get_Some_0();
                                    //        assert(pt_with_empty@.entries[i as int] === pt_final.entries[i as int]);
                                    //        assert(pt_with_empty@.entries[i as int].get_Some_0() === pt_final.entries[i as int].get_Some_0());
                                    //        assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                    //               ==> !dir_new_regions.contains(r) && !new_dir_pt.used_regions.contains(r));
                                    //        assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                    //               ==> #[trigger] tok_with_empty.regions[r] === tok@.regions[r]);
                                    //        lemma_inv_at_different_memory(tok_with_empty, tok@, pt_entry, (layer + 1) as nat, entry->Directory_addr);
                                    //        assert(inv_at(tok@, pt_final.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr));
                                    //    }
                                    //}
                                };
                            };

                            assert(directories_have_flags(tok@, pt_final, layer as nat, ptr));

                            assert(pt_final.entries.len() == pt_with_empty.entries.len());
                            assert(forall|i: nat| i != idx && i < pt_final.entries.len() ==> pt_final.entries[i as int] === pt_with_empty.entries[i as int]);
                            assert(ghost_pt_used_regions_rtrancl(tok@, pt_final, layer as nat, ptr)) by {
                                //assert forall|i: nat, r: MemRegion|
                                //    i < pt_final.entries.len() &&
                                //    pt_final.entries[i as int].is_Some() &&
                                //    #[trigger] pt_final.entries[i as int].get_Some_0().used_regions.contains(r)
                                //    implies pt_final.used_regions.contains(r)
                                //by {
                                //    if i == idx {
                                //        if dir_new_regions.contains(r) {
                                //            assert(pt_final.used_regions.contains(r));
                                //        } else {
                                //            assert(pt_with_empty@.entries[i as int].get_Some_0().used_regions.contains(r));
                                //            assert(pt_with_empty@.used_regions.contains(r));
                                //            assert(pt_final.used_regions.contains(r));
                                //        }
                                //    } else { }
                                //};
                            };
                            assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt_final, layer as nat, ptr)) by {
                                //assert forall|i: nat, j: nat, r: MemRegion|
                                //    i != j &&
                                //    i < pt_final.entries.len() && pt_final.entries[i as int].is_Some() &&
                                //    #[trigger] pt_final.entries[i as int].get_Some_0().used_regions.contains(r) &&
                                //    j < pt_final.entries.len() && pt_final.entries[j as int].is_Some()
                                //    implies !(#[trigger] pt_final.entries[j as int].get_Some_0().used_regions.contains(r))
                                //by
                                //{
                                //    assert(ghost_pt_used_regions_pairwise_disjoint(tok_with_empty, pt_with_empty@, layer as nat, ptr));
                                //    if j == idx {
                                //        assert(pt_final.entries[j as int].get_Some_0() === dir_pt_res);
                                //        assert(pt_final.entries[i as int] === pt.entries[i as int]);
                                //        if dir_new_regions.contains(r) {
                                //            assert(!new_dir_pt.used_regions.contains(r));
                                //            assert(!tok_with_empty.regions.contains_key(r));
                                //            assert(!dir_pt_res.used_regions.contains(r));
                                //        } else {
                                //            if new_dir_pt.used_regions.contains(r) {
                                //                assert(pt.used_regions.contains(r));
                                //                assert(tok_with_empty.regions.contains_key(r));
                                //                assert(!dir_pt_res.used_regions.contains(r));
                                //            }
                                //        }
                                //    } else {
                                //        if i == idx {
                                //            assert(pt_final.entries[i as int].get_Some_0() === dir_pt_res);
                                //            assert(pt_final.entries[j as int] === pt.entries[j as int]);
                                //            if dir_new_regions.contains(r) {
                                //                assert(dir_pt_res.used_regions.contains(r));
                                //                assert(!new_dir_pt.used_regions.contains(r));
                                //                assert(!tok_with_empty.regions.contains_key(r));
                                //                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                //            } else {
                                //                assert(new_dir_pt.used_regions.contains(r));
                                //                assert(!pt.entries[j as int].get_Some_0().used_regions.contains(r));
                                //            }
                                //        } else {
                                //            assert(pt_final.entries[i as int] === pt.entries[i as int]);
                                //            assert(pt_final.entries[j as int] === pt.entries[j as int]);
                                //        }
                                //    }
                                //
                                //};
                            };
                            assert(ghost_pt_matches_structure(tok@, pt_final, layer as nat, ptr));
                            assert(ghost_pt_region_notin_used_regions(tok@, pt_final, layer as nat, ptr));
                            assert(entry_mb0_bits_are_zero(tok@, pt_final, layer as nat, ptr));
                            assert(hp_pat_is_zero(tok@, pt_final, layer as nat, ptr));
                        };

                        assert(Ok(interp_at(tok@, pt_final, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@)) by {
                            lemma_interp_at_aux_facts(tok_with_empty, pt_with_empty, layer as nat, ptr, base as nat, seq![]);
                            assert(inv_at(tok@, pt_final, layer as nat, ptr));
                            assert(inv_at(tok_with_empty, pt_with_empty, layer as nat, ptr));
                            lemma_interp_at_aux_facts(tok@, pt_final, layer as nat, ptr, base as nat, seq![]);

                            // The original/old interp is `interp`
                            let interp_with_empty = interp_at(tok_with_empty, pt_with_empty, layer as nat, ptr, base as nat);
                            let final_interp = interp_at(tok@, pt_final, layer as nat, ptr, base as nat);

                            assert forall|i: nat| i < X86_NUM_ENTRIES && i != idx
                                implies interp_with_empty.entries[i as int] === #[trigger] interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).entries[i as int]
                            by { lemma_interp_at_entry_different_memory(old(tok)@, pt, tok_with_empty, pt_with_empty, layer as nat, ptr, base as nat, i); };

                            assert forall|i: nat|
                                i < X86_NUM_ENTRIES && i != idx
                                implies final_interp.entries[i as int] === #[trigger] interp_with_empty.entries[i as int] by
                            {
                                //if pt_final.entries[i as int].is_Some() {
                                //    let pt_entry = pt_final.entries[i as int].get_Some_0();
                                //    assert(ghost_pt_used_regions_pairwise_disjoint(tok@, pt_final, layer as nat, ptr));
                                //    assert forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                //           implies !new_regions.contains(r) by
                                //    {
                                //        assert(pt_entry.used_regions.contains(r));
                                //        assert(tok_with_empty.regions.contains_key(r));
                                //        assert(old(tok)@.regions.contains_key(r));
                                //        assert(!new_regions.contains(r));
                                //    };
                                //    assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                //           ==> !dir_pt_res.used_regions.contains(r));
                                //    assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                //           ==> #[trigger] old(tok)@.regions[r] === tok@.regions[r]);
                                //}
                                lemma_interp_at_entry_different_memory(tok_with_empty, pt_with_empty, tok@, pt_final, layer as nat, ptr, base as nat, i);
                            };

                            //assert(final_interp.entries[idx as int] === interp.map_frame(vaddr as nat, pte@).get_Ok_0().entries[idx as int]);
                            assert(final_interp.entries =~= interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@).get_Ok_0().entries);
                            assert(Ok(interp_at(tok@, pt_final, layer as nat, ptr, base as nat)) === interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).map_frame(vaddr as nat, pte@));
                        };

                        // posts
                        assert(pt_final.region === pt.region);
                        assert(pt_final.used_regions =~= pt.used_regions.union(new_regions));
                        assert(tok@.regions.dom() =~= old(tok)@.regions.dom().union(new_regions));
                        assert forall|r: MemRegion|
                            !(#[trigger] pt.used_regions.contains(r))
                            && !new_regions.contains(r)
                            implies tok@.regions[r] === old(tok)@.regions[r] by
                        {
                            assert(r !== new_dir_region@);
                            assert(!pt_with_empty.used_regions.contains(r));
                            assert(!new_dir_pt.used_regions.contains(r));
                            assert(tok@.regions[r] === tok_with_empty.regions[r]);
                        };
                        //assert forall|r: MemRegion|
                        //    new_regions.contains(r)
                        //    implies !(#[trigger] old(tok)@.regions.contains_key(r)) by
                        //{
                        //    if r === new_dir_region@ {
                        //        assert(!old(tok)@.regions.contains_key(r));
                        //    } else {
                        //        assert(dir_new_regions.contains(r));
                        //        assert(!tok_with_empty.regions.contains_key(r));
                        //        assert(!old(tok)@.regions.contains_key(r));
                        //    }
                        //};
                        assert(forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt.used_regions.contains(r)));
                    }
                    Ok(Ghost((pt_final, new_regions)))
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

pub proof fn lemma_zeroed_page_implies_empty_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize)
    requires
        ptr % PAGE_SIZE == 0,
        // TODO:
        //tok.inv(),
        tok.regions.contains_key(pt.region),
        pt.region.base == ptr,
        pt.region.size == PAGE_SIZE,
        tok.regions[pt.region].len() == pt.entries.len(),
        pt.region.base == ptr,
        ptr == pt.region.base,
        pt.used_regions === set![pt.region],
        layer_in_range(layer),
        pt.entries.len() == X86_NUM_ENTRIES,
        forall|i: nat| i < X86_NUM_ENTRIES ==> tok.regions[pt.region][i as int] == 0,
        forall|i: nat| i < X86_NUM_ENTRIES ==> pt.entries[i as int] is None,
    ensures
        empty_at(tok, pt, layer, ptr),
        inv_at(tok, pt, layer, ptr),
{
    broadcast use lemma_bitvector_facts_simple;
    lemma_bitvector_facts();
    assert forall|i: nat| #![auto] i < X86_NUM_ENTRIES implies
        entry_at_spec(tok, pt, layer, ptr, i)@ is Invalid
        && entry_at_spec(tok, pt, layer, ptr, i).all_mb0_bits_are_zero()
    by { entry_at_spec(tok, pt, layer, ptr, i).lemma_zero_entry_facts(); };
}

proof fn lemma_empty_at_interp_at_aux_equal_l1_empty_dir(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, idx: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        forall|i: nat| i < init.len() ==> init[i as int] === l1::NodeEntry::Invalid,
        init.len() <= X86_NUM_ENTRIES,
        idx < X86_NUM_ENTRIES,
        entry_at_spec(tok, pt, layer, ptr, idx)@ is Directory,
        empty_at(tok, pt.entries[idx as int].get_Some_0(), (layer + 1) as nat, entry_at_spec(tok, pt, layer, ptr, idx)@->Directory_addr),
    ensures
        ({ let res =
            interp_at_aux(
                tok,
                pt.entries[idx as int].get_Some_0(),
                layer + 1,
                entry_at_spec(tok, pt, layer, ptr, idx)@->Directory_addr,
                x86_arch_spec.entry_base(layer, base, idx),
                init);
        &&& res.len() === X86_NUM_ENTRIES as nat
        &&& forall|i: nat| i < res.len() ==> res[i as int] === l1::NodeEntry::Invalid
        })
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    let e_ptr = entry_at_spec(tok, pt, layer, ptr, idx)@->Directory_addr;
    let e_base = x86_arch_spec.entry_base(layer, base, idx);
    let e_pt = pt.entries[idx as int].get_Some_0();

    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        lemma_empty_at_interp_at_aux_equal_l1_empty_dir(
            tok, pt, layer, ptr, base,
            init.push(interp_at_entry(tok, e_pt, layer + 1, e_ptr, e_base, init.len())), idx);
    }
}

proof fn lemma_empty_at_interp_at_equal_l1_empty_dir(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat, idx: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        idx < X86_NUM_ENTRIES,
        entry_at_spec(tok, pt, layer, ptr, idx)@ is Directory,
        empty_at(tok, pt.entries[idx as int].get_Some_0(), (layer + 1) as nat, entry_at_spec(tok, pt, layer, ptr, idx)@->Directory_addr),
    ensures
        ({ let res =
            interp_at(
                tok,
                pt.entries[idx as int].get_Some_0(),
                layer + 1,
                entry_at_spec(tok, pt, layer, ptr, idx)@->Directory_addr,
                x86_arch_spec.entry_base(layer, base, idx));
        &&& res.entries.len() === X86_NUM_ENTRIES as nat
        &&& forall|i: nat| i < res.entries.len() ==> res.entries[i as int] === l1::NodeEntry::Invalid
        })
{
    lemma_empty_at_interp_at_aux_equal_l1_empty_dir(tok, pt, layer, ptr, base, seq![], idx);
}

proof fn lemma_not_empty_at_implies_interp_at_aux_not_empty(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat, init: Seq<l1::NodeEntry>, nonempty_idx: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        nonempty_idx < X86_NUM_ENTRIES,
        !(entry_at_spec(tok, pt, layer, ptr, nonempty_idx)@ is Invalid),
        nonempty_idx < init.len() ==> !(init[nonempty_idx as int] is Invalid)
    ensures
        !(interp_at_aux(tok, pt, layer, ptr, base, init)[nonempty_idx as int] is Invalid)
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 0nat
{
    if init.len() >= X86_NUM_ENTRIES as nat {
    } else {
        let new_init = init.push(interp_at_entry(tok, pt, layer, ptr, base, init.len()));
        lemma_not_empty_at_implies_interp_at_aux_not_empty(tok, pt, layer, ptr, base, new_init, nonempty_idx);
    }
}

proof fn lemma_empty_at_implies_interp_at_empty(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        empty_at(tok, pt, layer, ptr),
    ensures
        interp_at(tok, pt, layer, ptr, base).empty()
{
    lemma_interp_at_aux_facts(tok, pt, layer, ptr, base, seq![]);
}

proof fn lemma_not_empty_at_implies_interp_at_not_empty(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        !empty_at(tok, pt, layer, ptr),
    ensures
        !interp_at(tok, pt, layer, ptr, base).empty()
{
    let i = choose|i: nat| #![auto] i < X86_NUM_ENTRIES && !(entry_at_spec(tok, pt, layer, ptr, i)@ is Invalid);
    lemma_not_empty_at_implies_interp_at_aux_not_empty(tok, pt, layer, ptr, base, seq![], i);
}

pub fn map_frame(Tracked(tok): Tracked<&mut WrappedMapToken>, pt: &mut Ghost<PTDir>, pml4: usize, vaddr: usize, pte: PageTableEntryExec) -> (res: Result<(),()>)
    requires
        inv(old(tok)@, old(pt)@),
        interp(old(tok)@, old(pt)@).inv(true),
        old(tok).inv(),
        //old(tok)@.alloc_available_pages() >= 3,
        accepted_mapping(vaddr as nat, pte@),
        interp(old(tok)@, old(pt)@).accepted_mapping(vaddr as nat, pte@),
        vaddr < MAX_BASE,
        pml4 == old(tok)@.pt_mem.pml4,
        old(tok)@.args == (OpArgs::Map { base: vaddr, pte: pte@ }),
    ensures
        inv(tok@, pt@),
        interp(tok@, pt@).inv(true),
        // Refinement of l0
        match res {
            Ok(_) => Ok(interp(tok@, pt@).interp()) === interp(old(tok)@, old(pt)@).interp().map_frame(vaddr as nat, pte@),
            Err(_) => Err(interp(tok@, pt@).interp()) === interp(old(tok)@, old(pt)@).interp().map_frame(vaddr as nat, pte@),
        },
        tok.inv(),
{
    proof { interp(tok@, pt@).lemma_map_frame_refines_map_frame(vaddr as nat, pte@); }
    let ghost rebuild_root_pt = |pt_new, new_regions| pt_new;
    match map_frame_aux(Tracked(tok), *pt, 0, pml4, 0, vaddr, pte, Ghost(rebuild_root_pt)) {
        Ok(res) => {
            proof { interp(old(tok)@, pt@).lemma_map_frame_preserves_inv(vaddr as nat, pte@); }
            *pt = Ghost(res@.0);
            Ok(())
        },
        Err(e) => Err(()),
    }
}


fn is_directory_empty(Tracked(tok): Tracked<&mut WrappedUnmapToken>, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize) -> (res: bool)
    //requires
    //    old(tok).inv(),
    //    inv_at(old(tok)@, pt, layer as nat, ptr),
    //ensures
    //   tok.inv(),
    //   res === empty_at(tok@, pt, layer as nat, ptr),
{
    proof { admit(); }
    //assert(directories_obey_invariant_at(tok@, pt, layer as nat, ptr));
    let mut idx = 0;
    let num_entries = x86_arch_exec.num_entries(layer);
    while idx < num_entries
        //invariant
        //    num_entries == X86_NUM_ENTRIES,
        //    inv_at(tok@, pt, layer as nat, ptr),
        //    tok.inv(),
        //    forall|i: nat| #![auto] i < idx ==> entry_at_spec(tok@, pt, layer as nat, ptr, i)@ is Invalid,
    {
        let entry = entry_at_unmap(Tracked(tok), Ghost(pt), layer, ptr, idx);
        proof { admit(); }
        if entry.is_present() {
            //assert(!(entry_at_spec(tok@, pt, layer as nat, ptr, idx as nat)@ is Invalid));
            //assert(!empty_at(tok@, pt, layer as nat, ptr));
            return false;
        }
        idx = idx + 1;
        //assert(inv_at(tok@, pt, layer as nat, ptr));
    }
    true
}

/// Allocates and inserts an empty directory at the given index.
fn insert_empty_directory(Tracked(tok): Tracked<&mut WrappedMapToken>, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, idx: usize)
    -> (res: (Ghost<PTDir> /* pt_res */, MemRegionExec /* new_dir_region */, PDE /* new_dir_entry */))
    requires
        old(tok).inv(),
        inv_at(old(tok)@, pt, layer as nat, ptr),
        interp_at(old(tok)@, pt, layer as nat, ptr, base as nat).inv(true),
        //old(tok)@.alloc_available_pages() > 0,
        layer < 3,
        idx < X86_NUM_ENTRIES,
        entry_at_spec(old(tok)@, pt, layer as nat, ptr, idx as nat)@ is Invalid,
    ensures
        tok.inv(),
        inv_at(tok@, res.0@, layer as nat, ptr),
        !old(tok)@.regions.contains_key(res.1@),
        tok@.regions.dom() == old(tok)@.regions.dom().insert(res.1@),
        tok@.pt_mem.pml4 == old(tok)@.pt_mem.pml4,
        tok@.args == old(tok)@.args,
        tok@.orig_st == old(tok)@.orig_st,
        //tok.alloc_available_pages() == old(tok)@.alloc_available_pages() - 1,
        forall|i: nat| #![auto] i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(tok@, res.0@, layer as nat, ptr, i)@ == entry_at_spec(old(tok)@, res.0@, layer as nat, ptr, i)@,
        forall|r: MemRegion| r != res.0@.region && r != res.0@.entries[idx as int].get_Some_0().region ==> tok@.regions[r] == old(tok)@.regions[r],
        ({ let pt_res = res.0@; let new_dir_region = res.1; let new_dir_entry = res.2;
           let new_dir_pt = pt_res.entries[idx as int].get_Some_0();
           let entry_base = x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat);
           let new_dir_interp = interp_at(tok@, pt_res.entries[idx as int].get_Some_0(), (layer + 1) as nat, new_dir_region.base, entry_base);
           let interp = interp_at(old(tok)@, pt, layer as nat, ptr, base as nat);
           &&& entry_at_spec(tok@, pt_res, layer as nat, ptr, idx as nat) == new_dir_entry
           &&& entry_at_spec(tok@, pt_res, layer as nat, ptr, idx as nat)@ is Directory
           &&& entry_at_spec(tok@, pt_res, layer as nat, ptr, idx as nat)@->Directory_addr == new_dir_region.base
           &&& new_dir_interp == interp.new_empty_dir(idx as nat)
           &&& new_dir_interp.inv(true)
           &&& pt_res.region == pt.region
           &&& pt_res.entries == pt.entries.update(idx as int, Some(new_dir_pt))
           &&& pt_res.used_regions == pt.used_regions.insert(new_dir_region@)
           &&& new_dir_pt.region == new_dir_region@
        })
{
    let ghost interp = interp_at(tok@, pt, layer as nat, ptr, base as nat);
    let new_dir_region = WrappedMapToken::allocate(Tracked(tok), layer);
    let ghost tok_with_alloc = tok@;
    let new_dir_ptr = new_dir_region.base;
    let ghost new_dir_pt =
        PTDir {
            region: new_dir_region@,
            entries: new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None),
            used_regions: set![new_dir_region@],
        };
    assert(new_dir_ptr & MASK_DIR_ADDR == new_dir_ptr) by {
        lemma_page_aligned_implies_mask_dir_addr_is_identity();
    };
    let new_dir_entry = PDE::new_dir_entry(layer, new_dir_ptr);

    assert forall|i: nat| i < X86_NUM_ENTRIES implies
        entry_at_spec(tok@, pt, layer as nat, ptr, i) == entry_at_spec(old(tok)@, pt, layer as nat, ptr, i) by { };
    proof {
        broadcast use lemma_bitvector_facts_simple;
        lemma_bitvector_facts();
    }
    //assert(tok@.write(idx, new_dir_entry.entry, pt.region).interp() == tok@.interp());

    let ghost pt_res =
        PTDir {
            region:       pt.region,
            entries:      pt.entries.update(idx as int, Some(new_dir_pt)),
            used_regions: pt.used_regions.insert(new_dir_pt.region),
        };
    let ghost tok_with_empty = tok@.write(idx, new_dir_entry.entry, pt.region);


    proof {
        assert forall|i: nat| i < X86_NUM_ENTRIES implies
            #[trigger] entry_at_spec(tok_with_empty, pt_res, layer as nat, ptr, i)
            == if i == idx { new_dir_entry } else { entry_at_spec(old(tok)@, pt, layer as nat, ptr, i) } by { };
        lemma_new_seq::<u64>(512nat, 0u64);
        lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
        assert(new_dir_pt.entries.len() == 512);
        assert(new_dir_region@.contains(new_dir_ptr as nat));
        assert(tok_with_empty.regions[new_dir_region@] === new_seq(512nat, 0usize));
        lemma_zeroed_page_implies_empty_at(tok_with_empty, new_dir_pt, (layer + 1) as nat, new_dir_ptr);
        assert(empty_at(tok_with_empty, new_dir_pt, (layer + 1) as nat, new_dir_ptr));
        assert(inv_at(tok_with_empty, new_dir_pt, (layer + 1) as nat, new_dir_ptr));

        assert(forall|r: MemRegion| #![auto] r !== new_dir_pt.region && r !== pt_res.region
               ==> tok_with_empty.regions[r] === old(tok)@.regions[r]);
        assert(tok_with_empty.regions[pt_res.region]
               === old(tok)@.regions[pt_res.region].update(idx as int, new_dir_entry.entry));
        //assert(new_dir_pt.region != pt_res.region);
        assert(tok_with_empty.regions.dom() =~= old(tok)@.regions.dom().insert(new_dir_region@));
        //assert(tok_with_empty.regions =~=
        //    old(tok)@.regions
        //    .insert(new_dir_region@, new_seq(512, 0))
        //    .insert(pt_res.region, old(tok)@.regions[pt_res.region].update(idx as int, new_dir_entry.entry)));
        //assert(tok_with_empty.regions =~= old(tok)@.regions.insert(new_dir_region@, new_seq(512, 0)));

        assert(ghost_pt_matches_structure(tok_with_empty, pt_res, layer as nat, ptr));
        assert(directories_obey_invariant_at(tok_with_empty, pt_res, layer as nat, ptr)) by {
            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                let entry = #[trigger] entry_at_spec(tok_with_empty, pt_res, layer as nat, ptr, i)@;
                entry is Directory
                    ==> inv_at(tok_with_empty, pt_res.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr)
            } by {
                let entry = entry_at_spec(tok_with_empty, pt_res, layer as nat, ptr, i)@;
                if i != idx && entry is Directory {
                    //assert(inv_at(old(tok)@, pt_entry, (layer + 1) as nat, entry->Directory_addr));
                    //assert(pt.entries[i as int] == pt_res.entries[i as int]);
                    //assert(old(tok)@.regions.contains_key(pt_entry.region));
                    lemma_inv_at_different_memory(old(tok)@, tok_with_empty, pt.entries[i as int]->Some_0, (layer + 1) as nat, entry->Directory_addr);
                    //assert(inv_at(tok_with_empty, pt_res.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr));
                }
            };
        };
        assert(inv_at(tok_with_empty, pt_res, layer as nat, ptr));
    }

    assume(tok@.write(idx, new_dir_entry.entry, pt.region).interp() == tok@.interp());
    WrappedMapToken::write_stutter(Tracked(tok), ptr, idx, new_dir_entry.entry, Ghost(pt.region));
    assert(tok@ == tok_with_empty);

    proof {
        lemma_empty_at_interp_at_equal_l1_empty_dir(tok@, pt_res, layer as nat, ptr, base as nat, idx as nat);
        interp.lemma_new_empty_dir(idx as nat, true);
        lemma_interp_at_aux_facts(tok@, pt_res, layer as nat, ptr, base as nat, seq![]);
        let entry_base = x86_arch_spec.entry_base(layer as nat, base as nat, idx as nat);
        let new_dir_interp = interp_at(tok@, new_dir_pt, (layer + 1) as nat, new_dir_ptr, entry_base);
        assert(new_dir_interp.entries =~= interp.new_empty_dir(idx as nat).entries);
        assert(new_dir_interp == interp.new_empty_dir(idx as nat));
    }
    (Ghost(pt_res), new_dir_region, new_dir_entry)
}

fn unmap_aux(Tracked(tok): Tracked<&mut WrappedUnmapToken>, Ghost(pt): Ghost<PTDir>, layer: usize, ptr: usize, base: usize, vaddr: usize)
    -> (res: Result<(MemRegionExec, Ghost<(PTDir,Set<MemRegion>)>),()>)
    //requires
    //    inv_at(&*old(mem), pt, layer as nat, ptr),
    //    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).inv(),
    //    old(mem).inv(),
    //    interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).accepted_unmap(vaddr as nat),
    //    base <= vaddr < MAX_BASE,
    //ensures
    //    match res {
    //        Ok(resv) => {
    //            let (pt_res, removed_regions) = resv@;
    //            // We return the regions that we removed
    //            &&& old(mem).regions() == mem.regions().union(removed_regions)
    //            &&& pt.used_regions == pt_res.used_regions.union(removed_regions)
    //            // and only those we removed
    //            &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] mem.regions().contains(r)))
    //            &&& (forall|r: MemRegion| removed_regions.contains(r) ==> !(#[trigger] pt_res.used_regions.contains(r)))
    //            // Invariant preserved
    //            &&& inv_at(mem, pt_res, layer as nat, ptr)
    //            // We only touch regions in pt.used_regions
    //            &&& (forall|r: MemRegion|
    //                 !(#[trigger] pt_res.used_regions.contains(r))
    //                 && !(#[trigger] removed_regions.contains(r))
    //                ==> mem.regions[r] === old(mem).regions[r])
    //            &&& pt_res.region === pt.region
    //        },
    //        Err(e) => {
    //            // If error, unchanged
    //            &&& mem === old(mem)
    //        },
    //    },
    //    // Refinement of l1
    //    match res {
    //        Ok(resv) => {
    //            let (pt_res, removed_regions) = resv@;
    //            Ok(interp_at(mem, pt_res, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)
    //        },
    //        Err(e) =>
    //            Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat),
    //    },
    //    mem.cr3_spec() == old(mem).cr3_spec(),
    //// decreases X86_NUM_LAYERS - layer
{
    proof { admit(); }
    //proof { lemma_interp_at_facts(mem, pt, layer as nat, ptr, base as nat); }
    let idx: usize = x86_arch_exec.index_for_vaddr(layer, base, vaddr);
    //proof { indexing::lemma_index_from_base_and_addr(base as nat, vaddr as nat, x86_arch_spec.entry_size(layer as nat), X86_NUM_ENTRIES as nat); }
    let entry = entry_at_unmap(Tracked(tok), Ghost(pt), layer, ptr, idx);
    //let interp: Ghost<l1::Directory> = Ghost(interp_at(mem, pt, layer as nat, ptr, base as nat));
    //proof {
    //    interp@.lemma_unmap_structure_assertions(vaddr as nat, idx as nat);
    //    interp@.lemma_unmap_refines_unmap(vaddr as nat);
    //}
    let entry_base: usize = x86_arch_exec.entry_base(layer, base, idx);
    //proof {
    //    indexing::lemma_entry_base_from_index(base as nat, idx as nat, x86_arch_spec.entry_size(layer as nat));
    //    assert(entry_base <= vaddr);
    //}
    //assert(interp_at_entry(mem, pt, layer as nat, ptr, base as nat, idx as nat)
    //       == interp_at(mem, pt, layer as nat, ptr, base as nat).entries[idx as int]);
    if entry.is_present() {
        if entry.is_dir(layer) {
            let dir_addr = entry.address();
            //assert(pt.entries[idx as int].is_Some());
            let dir_pt: Ghost<PTDir> = Ghost(pt.entries.index(idx as int).get_Some_0());
            //assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr));
            //assert(forall|r: MemRegion| #![auto] pt.entries[idx as int].get_Some_0().used_regions.contains(r) ==> pt.used_regions.contains(r));
            match unmap_aux(Tracked(tok), dir_pt, layer + 1, dir_addr, entry_base, vaddr) {
                Ok((unmapped_region, rec_res)) => {
                    let dir_pt_res: Ghost<PTDir> = Ghost(rec_res@.0);
                    let removed_regions: Ghost<Set<MemRegion>> = Ghost(rec_res@.1);

                    //assert(inv_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr));
                    //assert(Ok(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat))
                    //       === interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).unmap(vaddr as nat));
                    //assert(idx < pt.entries.len());
                    //assert(!pt.entries[idx as int].get_Some_0().used_regions.contains(pt.region));
                    //assert(!removed_regions@.contains(pt.region));
                    //assert(!dir_pt_res@.used_regions.contains(pt.region));
                    //assert(old(mem).regions() === mem.regions().union(removed_regions@));

                    if is_directory_empty(Tracked(tok), dir_pt_res, layer + 1, dir_addr) {
                        //let mem_with_empty: Ghost<&mem::PageTableMemory> = Ghost(mem);
                        //let pt_with_empty: Ghost<PTDir> = Ghost(
                        //    PTDir {
                        //        region:       pt.region,
                        //        entries:      pt.entries.update(idx as int, Some(dir_pt_res@)),
                        //        used_regions: pt.used_regions,
                        //    });
                        WrappedUnmapToken::write_stutter(Tracked(tok), ptr, idx, 0usize, Ghost(pt.region));
                        WrappedUnmapToken::deallocate(Tracked(tok), layer, MemRegionExec { base: dir_addr, size: PAGE_SIZE, });

                        let removed_regions: Ghost<Set<MemRegion>> = Ghost(removed_regions@.insert(dir_pt_res@.region));
                        let pt_res: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, None),
                                used_regions: pt.used_regions.difference(removed_regions@),
                            });
                        let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));

                        //proof {
                        //    entry_at_spec(mem, pt_res@, layer as nat, ptr, idx as nat).lemma_zero_entry_facts();
                        //    assert(pt_res@.region === pt.region);
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt.entries[i as int]);
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt_res@, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt_res@, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                        //    assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(r));
                        //
                        //
                        //    assert(directories_obey_invariant_at(mem, pt_res@, layer as nat, ptr)) by {
                        //        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        //            let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                        //            entry is Directory ==> {
                        //                &&& inv_at(mem, pt_res@.entries[i as int].get_Some_0(), layer as nat + 1, entry->Directory_addr)
                        //            }
                        //        } by {
                        //            let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                        //            if i == idx {
                        //            } else {
                        //                if entry is Directory {
                        //                    lemma_inv_at_different_memory(&*old(mem), mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                        //                }
                        //            }
                        //        };
                        //    };
                        //
                        //    assert(inv_at(mem, pt_res@, layer as nat, ptr));
                        //
                        //    // postconditions
                        //    assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] mem.regions().contains(r))));
                        //    assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                        //    assert(pt.used_regions =~= pt_res@.used_regions.union(removed_regions@));
                        //    assert((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                        //    assert(forall|r: MemRegion|
                        //         !(#[trigger] pt_res@.used_regions.contains(r))
                        //         && !(#[trigger] removed_regions@.contains(r))
                        //        ==> mem.regions[r] === old(mem).regions[r]);
                        //    assert(mem.cr3_spec() == old(mem).cr3_spec());
                        //
                        //    // Refinement
                        //    assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                        //        lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
                        //        assert forall|i: nat|
                        //            i < X86_NUM_ENTRIES
                        //            implies
                        //            #[trigger] interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                        //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                        //        {
                        //            if i == idx {
                        //                lemma_empty_at_implies_interp_at_empty(mem_with_empty@, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat);
                        //                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int] ==
                        //                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                        //            } else {
                        //                lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt_res@, layer as nat, ptr, base as nat, i);
                        //                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                        //                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                        //            }
                        //        }
                        //
                        //        assert(
                        //            interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries =~=
                        //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                        //    };
                        //}
                        Ok((unmapped_region, res))
                    } else {
                        let pt_res: Ghost<PTDir> = Ghost(
                            PTDir {
                                region: pt.region,
                                entries: pt.entries.update(idx as int, Some(dir_pt_res@)),
                                used_regions: pt.used_regions.difference(removed_regions@),
                            });
                        let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt_res@,removed_regions@));

                        //proof {
                        //    assert(pt_res@.region === pt.region);
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> pt_res@.entries[i as int] == pt.entries[i as int]);
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt_res@, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                        //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt_res@, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                        //    assert(forall|i: nat, r: MemRegion| i < X86_NUM_ENTRIES && i != idx && pt_res@.entries[i as int].is_Some() && pt_res@.entries[i as int].get_Some_0().used_regions.contains(r) ==> !pt.entries[idx as int].get_Some_0().used_regions.contains(r));
                        //
                        //    assert(inv_at(mem, pt_res@, layer as nat, ptr)) by {
                        //        assert(directories_obey_invariant_at(mem, pt_res@, layer as nat, ptr)) by {
                        //            assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                        //                let entry = #[trigger] view_at(mem, pt_res@, layer as nat, ptr, i);
                        //                entry is Directory ==> {
                        //                    &&& inv_at(mem, pt_res@.entries[i as int].get_Some_0(), layer as nat + 1, entry->Directory_addr)
                        //                }
                        //            } by {
                        //                let entry = view_at(mem, pt_res@, layer as nat, ptr, i);
                        //                if i == idx {
                        //                } else {
                        //                    if entry is Directory {
                        //                        lemma_inv_at_different_memory(&*old(mem), mem, pt_res@.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                        //                    }
                        //                }
                        //            };
                        //        };
                        //    };
                        //
                        //    // postconditions
                        //    assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                        //    assert(pt.used_regions =~= pt_res@.used_regions.union(removed_regions@));
                        //    assert(forall|r: MemRegion|
                        //         !(#[trigger] pt_res@.used_regions.contains(r))
                        //         && !(#[trigger] removed_regions@.contains(r))
                        //        ==> mem.regions[r] === old(mem).regions[r]);
                        //    assert(pt_res@.region === pt.region);
                        //    assert(mem.cr3_spec() == old(mem).cr3_spec());
                        //    // Refinement
                        //    assert(Ok(interp_at(mem, pt_res@, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                        //        lemma_interp_at_aux_facts(mem, pt_res@, layer as nat, ptr, base as nat, seq![]);
                        //        assert forall|i: nat|
                        //            i < X86_NUM_ENTRIES
                        //            implies
                        //            #[trigger] interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                        //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                        //        {
                        //            if i == idx {
                        //                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int]
                        //                       == l1::NodeEntry::Directory(interp_at(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat)));
                        //                assert(interp_at(&*old(mem), dir_pt@, (layer + 1) as nat, dir_addr, entry_base as nat).unmap(vaddr as nat).is_Ok());
                        //                assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).entries[idx as int] == interp_at_entry(&*old(mem), pt, layer as nat, ptr, base as nat, idx as nat));
                        //
                        //                lemma_not_empty_at_implies_interp_at_not_empty(mem, dir_pt_res@, (layer + 1) as nat, dir_addr, entry_base as nat);
                        //                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[idx as int] ==
                        //                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[idx as int]);
                        //            } else {
                        //                lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt_res@, layer as nat, ptr, base as nat, i);
                        //                assert(interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries[i as int] ==
                        //                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                        //            }
                        //        }
                        //
                        //        assert(
                        //            interp_at(mem, pt_res@, layer as nat, ptr, base as nat).entries =~=
                        //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                        //    };
                        //}
                        Ok((unmapped_region, res))
                    }

                },
                Err(e) => {
                    //assert(mem === old(mem));
                    //assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
                    Err(e)
                },
            }
        } else {
            if aligned_exec(vaddr, x86_arch_exec.entry_size(layer)) {
                WrappedUnmapToken::write_change(Tracked(tok), ptr, idx, 0usize, Ghost(pt.region));

                let removed_regions: Ghost<Set<MemRegion>> = Ghost(Set::empty());
                let res: Ghost<(PTDir,Set<MemRegion>)> = Ghost((pt, removed_regions@));

                //proof {
                //    entry_at_spec(mem, pt, layer as nat, ptr, idx as nat).lemma_zero_entry_facts();
                //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> entry_at_spec(mem, pt, layer as nat, ptr, i) == entry_at_spec(&*old(mem), pt, layer as nat, ptr, i));
                //    assert(forall|i: nat| i < X86_NUM_ENTRIES && i != idx ==> view_at(mem, pt, layer as nat, ptr, i) == view_at(&*old(mem), pt, layer as nat, ptr, i));
                //
                //    assert(directories_obey_invariant_at(mem, pt, layer as nat, ptr)) by {
                //        assert forall|i: nat| i < X86_NUM_ENTRIES implies {
                //            let entry = #[trigger] view_at(mem, pt, layer as nat, ptr, i);
                //            entry is Directory ==> {
                //                &&& inv_at(mem, pt.entries[i as int].get_Some_0(), layer as nat + 1, entry->Directory_addr)
                //            }
                //        } by {
                //            let entry = view_at(mem, pt, layer as nat, ptr, i);
                //            if i == idx {
                //            } else {
                //                if entry is Directory {
                //                    assert(directories_obey_invariant_at(&*old(mem), pt, layer as nat, ptr));
                //                    lemma_inv_at_different_memory(&*old(mem), mem, pt.entries[i as int].get_Some_0(), (layer + 1) as nat, entry->Directory_addr);
                //                    assert(inv_at(mem, pt.entries[i as int].get_Some_0(), layer as nat + 1, entry->Directory_addr));
                //                }
                //            }
                //        };
                //    };
                //
                //    assert(inv_at(mem, pt, layer as nat, ptr));
                //
                //    // postconditions
                //    assert(old(mem).regions() =~= mem.regions().union(removed_regions@));
                //    assert(pt.used_regions =~= pt.used_regions.union(removed_regions@));
                //
                //    // Refinement
                //    assert(Ok(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat)) by {
                //        lemma_interp_at_aux_facts(mem, pt, layer as nat, ptr, base as nat, seq![]);
                //        assert(interp_at(mem, pt, layer as nat, ptr, base as nat).entries.len() == X86_NUM_ENTRIES);
                //        assert(interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries.len() == X86_NUM_ENTRIES);
                //
                //        assert forall|i: nat|
                //            i < X86_NUM_ENTRIES
                //            implies
                //            #[trigger] interp_at(mem, pt, layer as nat, ptr, base as nat).entries[i as int] ==
                //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int] by
                //        {
                //            if i == idx {
                //            } else {
                //                lemma_interp_at_entry_different_memory(&*old(mem), pt, mem, pt, layer as nat, ptr, base as nat, i);
                //                assert(interp_at(mem, pt, layer as nat, ptr, base as nat).entries[i as int] ==
                //                       interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries[i as int]);
                //            }
                //        }
                //
                //        assert(
                //            interp_at(mem, pt, layer as nat, ptr, base as nat).entries =~=
                //            interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat).get_Ok_0().entries);
                //    };
                //}
                let unmapped_region = MemRegionExec { base: vaddr, size: x86_arch_exec.entry_size(layer) };
                Ok((unmapped_region, res))
            } else {
                //assert(mem === old(mem));
                //assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
                Err(())
            }
        }
    } else {
        //assert(mem === old(mem));
        //assert(Err(interp_at(mem, pt, layer as nat, ptr, base as nat)) === interp_at(&*old(mem), pt, layer as nat, ptr, base as nat).unmap(vaddr as nat));
        Err(())
    }
}

pub fn unmap(Tracked(tok): Tracked<&mut WrappedUnmapToken>, pt: &mut Ghost<PTDir>, pml4: usize, vaddr: usize) -> (res: Result<MemRegionExec,()>)
    //requires
    //    inv(&*old(mem), old(pt)@),
    //    interp(&*old(mem), old(pt)@).inv(),
    //    old(mem).inv(),
    //    interp(&*old(mem), old(pt)@).accepted_unmap(vaddr as nat),
    //    vaddr < MAX_BASE,
    //ensures
    //    inv(mem, pt@),
    //    interp(mem, pt@).inv(),
    //    // Refinement of l0
    //    match res {
    //        Ok(_)  => Ok(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().unmap(vaddr as nat),
    //        Err(_) => Err(interp(mem, pt@).interp()) === interp(&*old(mem), old(pt)@).interp().unmap(vaddr as nat),
    //    },
{
    proof { admit(); }
    //proof { interp(mem, pt@).lemma_unmap_refines_unmap(vaddr as nat); }
    match unmap_aux(Tracked(tok), *pt, 0, pml4, 0, vaddr) {
        Ok(res) => {
            //proof { interp(&*old(mem), pt@).lemma_unmap_preserves_inv(vaddr as nat); }
            *pt = Ghost(res.1@.0);
            Ok(res.0)
        },
        Err(e) => Err(()),
    }
}

//#[cfg(feature = "noreclaim")]
//#[verus::line_count::ignore]
//#[verifier(external_body)]
//fn unmap_noreclaim_aux(mem: &mut mem::PageTableMemory, layer: usize, ptr: usize, base: usize, vaddr: usize)
//    -> (res: Result<(),()>)
//{
//    let idx: usize = x86_arch_exec.index_for_vaddr(layer, base, vaddr);
//    let entry = entry_at(mem, Ghost(pt), layer, ptr, idx);
//    let entry_base: usize = x86_arch_exec.entry_base(layer, base, idx);
//    if entry.is_mapping() {
//        if entry.is_dir(layer) {
//            let dir_addr = entry.address() as usize;
//            unmap_noreclaim_aux(mem, layer + 1, dir_addr, entry_base, vaddr)
//        } else {
//            if aligned_exec(vaddr, x86_arch_exec.entry_size(layer)) {
//                mem.write(ptr, idx, Ghost(pt.region), 0u64);
//                Ok(())
//            } else {
//                Err(())
//            }
//        }
//    } else {
//        Err(())
//    }
//}

///// An unverified version of the unmap function that doesn't reclaim empty directories. For
///// benchmarking purposes.
//#[cfg(feature = "noreclaim")]
//#[verus::line_count::ignore]
//#[verifier(external_body)]
//pub fn unmap_noreclaim(mem: &mut mem::PageTableMemory, vaddr: usize) -> Result<(),()> {
//    unmap_noreclaim_aux(mem, 0, mem.cr3().base, 0, vaddr)
//}

}

} // verus!
