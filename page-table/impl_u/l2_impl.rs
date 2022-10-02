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

use result::{*, Result::*};

use crate::definitions_t::{ Arch, ArchExec, MemRegion, MemRegionExec, PageTableEntry, PageTableEntryExec, Flags, overlap, between, aligned, aligned_exec, new_seq, lemma_new_seq, MapResult, UnmapResult, candidate_mapping_in_bounds };
use crate::definitions_t::{ x86_arch, MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::spec_t::mem;
use crate::spec_t::mem::{ word_index_spec };
use crate::impl_u::indexing;

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
    ensures forall|addr: u64| addr <= MAXPHYADDR ==> #[trigger] aligned(addr, PAGE_SIZE) ==> addr & MASK_DIR_ADDR == addr,
{
    assert forall|addr: u64|
        addr <= MAXPHYADDR &&
        #[trigger] aligned(addr, PAGE_SIZE)
        implies
        addr & MASK_DIR_ADDR == addr
    by {
        assert(addr <= 0xFFFFFFFFFFFFFu64 && addr % 4096u64 == 0 ==> addr & bitmask_inc!(12u64,52u64) == addr) by(bit_vector);
    };
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table


// MASK_FLAG_* are flags valid for all entries.
pub const MASK_FLAG_P:    u64 = bit!(0u64);
pub const MASK_FLAG_RW:   u64 = bit!(1u64);
pub const MASK_FLAG_US:   u64 = bit!(2u64);
pub const MASK_FLAG_PWT:  u64 = bit!(3u64);
pub const MASK_FLAG_PCD:  u64 = bit!(4u64);
pub const MASK_FLAG_A:    u64 = bit!(5u64);
pub const MASK_FLAG_XD:   u64 = bit!(63u64);
// We can use the same address mask for all layers as long as we preserve the invariant that the
// lower bits that *should* be masked off are already zero.
pub const MASK_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);
// const MASK_ADDR:      u64 = 0b0000000000001111111111111111111111111111111111111111000000000000;

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
pub const MASK_PG_FLAG_D:    u64 = bit!(6u64);
pub const MASK_PG_FLAG_G:    u64 = bit!(8u64);
pub const MASK_PG_FLAG_PAT:  u64 = bit!(12u64);

pub const MASK_L1_PG_FLAG_PS:   u64 = bit!(7u64);
pub const MASK_L2_PG_FLAG_PS:   u64 = bit!(7u64);

pub const MASK_L3_PG_FLAG_PAT:  u64 = bit!(7u64);

// const MASK_DIR_REFC:           u64 = bitmask_inc!(52u64,62u64); // Ignored bits for storing refcount in L3 and L2
// const MASK_DIR_L1_REFC:        u64 = bitmask_inc!(8u64,12u64); // Ignored bits for storing refcount in L1
// const MASK_DIR_REFC_SHIFT:     u64 = 52u64;
// const MASK_DIR_L1_REFC_SHIFT:  u64 = 8u64;
pub const MASK_DIR_ADDR:           u64 = MASK_ADDR;

// We should be able to always use the 12:52 mask and have the invariant state that in the
// other cases, the lower bits are already zero anyway.
pub const MASK_L1_PG_ADDR:      u64 = bitmask_inc!(30u64,MAXPHYADDR_BITS);
pub const MASK_L2_PG_ADDR:      u64 = bitmask_inc!(21u64,MAXPHYADDR_BITS);
pub const MASK_L3_PG_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);

proof fn lemma_addr_masks_facts(address: u64)
    ensures
        MASK_L2_PG_ADDR & address == address ==> MASK_L3_PG_ADDR & address == address,
        MASK_L1_PG_ADDR & address == address ==> MASK_L3_PG_ADDR & address == address,
{
    // TODO: can we get support for consts in bit vector reasoning?
    assert((bitmask_inc!(21u64, 52u64) & address == address) ==> (bitmask_inc!(12u64, 52u64) & address == address)) by (bit_vector);
    assert((bitmask_inc!(30u64, 52u64) & address == address) ==> (bitmask_inc!(12u64, 52u64) & address == address)) by (bit_vector);
}

proof fn lemma_addr_masks_facts2(address: u64)
    ensures
        (address & MASK_L3_PG_ADDR) & MASK_L2_PG_ADDR == address & MASK_L2_PG_ADDR,
        (address & MASK_L3_PG_ADDR) & MASK_L1_PG_ADDR == address & MASK_L1_PG_ADDR,
{
    assert(((address & bitmask_inc!(12u64, 52u64)) & bitmask_inc!(21u64, 52u64)) == (address & bitmask_inc!(21u64, 52u64))) by (bit_vector);
    assert(((address & bitmask_inc!(12u64, 52u64)) & bitmask_inc!(30u64, 52u64)) == (address & bitmask_inc!(30u64, 52u64))) by (bit_vector);
}

// // MASK_PD_* are flags valid for all entries pointing to another directory
// const MASK_PD_ADDR:      u64 = bitmask!(12,52);

pub open spec fn addr_is_zero_padded(layer: nat, addr: u64, is_page: bool) -> bool {
    is_page ==> {
        if layer == 1 {
            addr & MASK_L1_PG_ADDR == addr & MASK_ADDR
        } else if layer == 2 {
            addr & MASK_L2_PG_ADDR == addr & MASK_ADDR
        } else if layer == 3 {
            addr & MASK_L3_PG_ADDR == addr & MASK_ADDR
        } else {
            true
        }
    }
}


// FIXME: We can probably remove bits from here that we don't use, e.g. accessed, dirty, PAT. (And
// set them to zero when we create a new entry.)
#[is_variant]
pub ghost enum GhostPageDirectoryEntry {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// Dirty; indicates whether software has written to the page referenced by this entry
        flag_D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // flag_PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        flag_G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        flag_PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    Empty,
}


// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PageDirectoryEntry {
    pub entry: u64,
    // pub view: Ghost<GhostPageDirectoryEntry>,
    pub ghost layer: nat,
}

impl PageDirectoryEntry {

    pub open spec fn view(self) -> GhostPageDirectoryEntry {
        if self.layer() <= 3 {
            let v = self.entry;
            if v & MASK_FLAG_P == MASK_FLAG_P {
                let flag_P   = v & MASK_FLAG_P   == MASK_FLAG_P;
                let flag_RW  = v & MASK_FLAG_RW  == MASK_FLAG_RW;
                let flag_US  = v & MASK_FLAG_US  == MASK_FLAG_US;
                let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
                let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
                let flag_A   = v & MASK_FLAG_A   == MASK_FLAG_A;
                let flag_XD  = v & MASK_FLAG_XD  == MASK_FLAG_XD;
                if (self.layer() == 3) || (v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) {
                    let addr     =
                        if self.layer() == 3 {
                            (v & MASK_L3_PG_ADDR) as usize
                        } else if self.layer() == 2 {
                            (v & MASK_L2_PG_ADDR) as usize
                        } else {
                            (v & MASK_L1_PG_ADDR) as usize
                        };
                    let flag_D   = v & MASK_PG_FLAG_D   == MASK_PG_FLAG_D;
                    let flag_G   = v & MASK_PG_FLAG_G   == MASK_PG_FLAG_G;
                    let flag_PAT = if self.layer() == 3 { v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT } else { v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT };
                    GhostPageDirectoryEntry::Page {
                        addr,
                        flag_P, flag_RW, flag_US, flag_PWT, flag_PCD,
                        flag_A, flag_D, flag_G, flag_PAT, flag_XD,
                    }
                } else {
                    let addr = (v & MASK_ADDR) as usize;
                    GhostPageDirectoryEntry::Directory {
                        addr, flag_P, flag_RW, flag_US, flag_PWT, flag_PCD, flag_A, flag_XD,
                    }
                }
            } else {
                GhostPageDirectoryEntry::Empty
            }
        } else {
            arbitrary()
        }
    }

    pub open spec fn addr_is_zero_padded(self) -> bool {
        addr_is_zero_padded(self.layer, self.entry, self@.is_Page())
    }

    pub open spec fn layer(self) -> nat {
        self.layer
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
            addr_is_zero_padded(layer, address, is_page),
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
                &&& addr_is_zero_padded(layer, e, is_page)
            }),
    {
        assert(address & MASK_ADDR == address);
        let or1 = MASK_FLAG_P;
        let a1 = address | or1;
        let or2 = if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 };
        let a2 = a1 | or2;
        let or3 = if is_writable           { MASK_FLAG_RW }        else { 0 };
        let a3 = a2 | or3;
        let or4 = if is_supervisor         { 0 }                   else { MASK_FLAG_US };
        let a4 = a3 | or4;
        let or5 = if is_writethrough       { MASK_FLAG_PWT }       else { 0 };
        let a5 = a4 | or5;
        let or6 = if disable_cache         { MASK_FLAG_PCD }       else { 0 };
        let a6 = a5 | or6;
        let or7 = if disable_execute       { MASK_FLAG_XD }        else { 0 };
        let a7 = a6 | or7;
        let e = address | or1 | or2 | or3 | or4 | or5 | or6 | or7;
        assert(forall|a:u64,x:u64| x < 64 && (a & bit!(x) == 0) ==> ((a & bit!(x) == bit!(x)) == false)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | 0)           & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(0u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(7u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(1u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(2u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(3u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(4u64))  & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == (a | bit!(63u64)) & bitmask_inc!(12u64,52u64)) by(bit_vector);
        assert(e & MASK_ADDR == address) by {
        };
        assert(e & MASK_FLAG_P == MASK_FLAG_P) by {
            assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(0u64) == 0) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == 0 ==> (a | bit!(0u64)) & bit!(0u64) == bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | 0)           & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(7u64))  & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(1u64))  & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(2u64))  & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(3u64))  & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(4u64))  & bit!(0u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(0u64) == (a | bit!(63u64)) & bit!(0u64)) by(bit_vector);
        };
        assert((e & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) == (is_page && layer != 3)) by {
            assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(0u64) == 0) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(7u64) == 0) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == 0 ==> (a | bit!(7u64)) & bit!(7u64) == bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | 0)           & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(0u64))  & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(1u64))  & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(2u64))  & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(3u64))  & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(4u64))  & bit!(7u64)) by(bit_vector);
            assert(forall|a:u64| #![auto] a & bit!(7u64) == (a | bit!(63u64)) & bit!(7u64)) by(bit_vector);
        };
        assert((e & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable) by {
            // FIXME: bitvector
            assume(false);
            // assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(0u64) == 0) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(7u64) == 0) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bitmask_inc!(12u64,52u64) == a ==> a & bit!(1u64) == 0) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == 0 ==> (a | bit!(1u64)) & bit!(1u64) == bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | 0)           & bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | bit!(0u64))  & bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | bit!(2u64))  & bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | bit!(3u64))  & bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | bit!(4u64))  & bit!(1u64)) by(bit_vector);
            // assert(forall|a:u64| #![auto] a & bit!(1u64) == (a | bit!(63u64)) & bit!(1u64)) by(bit_vector);
            // assert(a1 & MASK_FLAG_RW == 0);
            // assert(a2 & MASK_FLAG_RW == 0);
            // assert((a3 & MASK_FLAG_RW == MASK_FLAG_RW) == is_writable);
        };
        assert((e & MASK_FLAG_US == MASK_FLAG_US) == !is_supervisor) by {
            // FIXME: bitvector
            assume(false);
        };
        assert((e & MASK_FLAG_PWT == MASK_FLAG_PWT) == is_writethrough) by {
            // FIXME: bitvector
            assume(false);
        };
        assert((e & MASK_FLAG_PCD == MASK_FLAG_PCD) == disable_cache) by {
            // FIXME: bitvector
            assume(false);
        };
        assert((e & MASK_FLAG_XD == MASK_FLAG_XD) == disable_execute) by {
            // FIXME: bitvector
            assume(false);
        };
        assert(addr_is_zero_padded(layer, e, is_page)) by {
            // FIXME: bitvector
            assume(false);
        };
    }

    pub fn new_page_entry(layer: usize, pte: PageTableEntryExec) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer, pte.frame.base as u64, true),
            pte.frame.base as u64 & MASK_ADDR == pte.frame.base as u64,
        ensures
            r.addr_is_zero_padded(),
            r@.is_Page(),
            r.layer == layer,
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
            r.addr_is_zero_padded(),
            r@.is_Directory(),
            r.layer == layer,
            r@.get_Directory_addr() == address,
    {
        // FIXME: check what flags we want here
        Self::new_entry(layer, address, false, true, false, false, false, false)
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
            addr_is_zero_padded(layer, address, is_page),
            address & MASK_ADDR == address,
        ensures
            if is_page { r@.is_Page() && r@.get_Page_addr() == address } else { r@.is_Directory() && r@.get_Directory_addr() == address},
            r.addr_is_zero_padded(),
            r.layer == layer,
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
            layer: layer as nat,
        };

        proof {
            PageDirectoryEntry::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            assert(e.layer() <= 3);
            // if is_page {
            //     if layer == 1 {
            //     } else if layer == 2 {
            //     } else if layer == 3 {
            //     } else {
            //         assert(false);
            //     }
            // } else {
            // }
            assert(e@.is_Page() ==> 0 < e.layer());
            assert(e.addr_is_zero_padded());
            assert(if is_page { e@.is_Page() } else { e@.is_Directory() });

        }
        e
    }

    pub fn flags(&self) -> (res: Flags)
        requires
            self.layer() <= 3,
            self@.is_Page()
        ensures
            true
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
            self.addr_is_zero_padded(),
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
                GhostPageDirectoryEntry::Page { addr, .. }      => 
                    if self.layer() == 1 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else if self.layer() == 2 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else if self.layer() == 3 {
                        assert(addr == self.entry & MASK_ADDR);
                    } else {
                        assert(false);
                    },
                GhostPageDirectoryEntry::Directory { addr, .. } => assert(addr == self.entry & MASK_ADDR),
                GhostPageDirectoryEntry::Empty                  => (),
            }
        }
        self.entry & MASK_ADDR
    }

    pub fn is_mapping(&self) -> (r: bool)
        requires
            self.layer() <= 3
        ensures
            r == !self@.is_Empty(),
    {
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer,
            layer <= 3,
        ensures
            if r { self@.is_Page() } else { self@.is_Directory() },
    {
        (layer == 3) || ((self.entry & MASK_L1_PG_FLAG_PS) == MASK_L1_PG_FLAG_PS)
    }

    pub fn is_dir(&self, layer: usize) -> (r: bool)
        requires
            !self@.is_Empty(),
            layer as nat == self.layer,
            layer <= 3,
        ensures
            if r { self@.is_Directory() } else { self@.is_Page() },
    {
        !self.is_page(layer)
    }
}

pub struct PTDir {
    pub region: MemRegion,
    pub entries: Seq<Option<PTDir>>,
    /// reflexive-transitive closure of `region` over `entries`
    pub used_regions: Set<MemRegion>,
}

pub struct PageTable {
    pub memory: mem::PageTableMemory,
    pub arch: ArchExec,
    pub ghost_pt: Ghost<PTDir>,
}

impl PageTable {
    pub open spec(checked) fn well_formed(self, layer: nat, ptr: usize) -> bool {
        &&& self.arch@.inv()
        // Make sure each page directory fits in one page:
        &&& forall|layer: nat| layer < self.arch@.layers.len() ==> self.arch@.num_entries(layer) == 512
        &&& aligned(ptr, PAGE_SIZE)
    }

    pub open spec(checked) fn inv(&self) -> bool {
        let cr3 = self.memory.cr3_spec();
        &&& self.ghost_pt@.region === cr3@
        &&& self.inv_at(0, cr3.base, self.ghost_pt@)
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn entry_at_spec(self, layer: nat, ptr: usize, i: nat, pt: PTDir) -> PageDirectoryEntry {
        PageDirectoryEntry {
            entry: self.memory.spec_read(ptr as nat + (i * WORD_SIZE as nat), pt.region),
            layer,
        }
    }

    /// Get the view of the entry at address ptr + i * WORD_SIZE
    pub open spec fn view_at(self, layer: nat, ptr: usize, i: nat, pt: PTDir) -> GhostPageDirectoryEntry {
        PageDirectoryEntry {
            entry: self.memory.spec_read(ptr as nat + (i * WORD_SIZE as nat), pt.region),
            layer,
        }@
    }

    /// Get the entry at address ptr + i * WORD_SIZE
    #[verifier(nonlinear)]
    fn entry_at(&self, layer: usize, ptr: usize, i: usize, pt: Ghost<PTDir>) -> (res: PageDirectoryEntry)
        requires
            self.inv_at(layer, ptr, pt@)
        ensures
            res.layer == layer,
            res@ === self.view_at(layer, ptr, i, pt@),
            res.addr_is_zero_padded(),
            (res@.is_Page() ==> 0 < res.layer()),
    {
        assume(ptr <= 100);
        assume(i * WORD_SIZE <= 100000);
        assume(aligned((ptr + i * WORD_SIZE) as nat, 8));
        assume(pt@.region.contains((ptr + i * WORD_SIZE) as nat));
        assert(self.memory.inv());
        proof {
            // triggering
            let x = self.entry_at_spec(layer, ptr, i, pt@);
        }
        PageDirectoryEntry {
            entry: self.memory.read(ptr + i * WORD_SIZE, ghost(pt@.region)),
            layer,
        }
    }

    pub open spec fn ghost_pt_matches_structure(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| #![trigger pt.entries.index(i), self.view_at(layer, ptr, i, pt)]
        i < self.arch@.num_entries(layer) ==> {
            let entry = self.view_at(layer, ptr, i, pt);
            entry.is_Directory() == pt.entries[i].is_Some()
        }
    }

    pub open spec fn directories_obey_invariant_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        decreases (self.arch@.layers.len() - layer, 0nat)
    {
        decreases_when(self.well_formed(layer, ptr) && self.layer_in_range(layer));
        forall|i: nat| i < self.arch@.num_entries(layer) ==> {
            let entry = #[trigger] self.view_at(layer, ptr, i, pt);
            entry.is_Directory() ==> {
                &&& self.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0())
            }
        }
    }

    pub open spec fn empty_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        recommends self.well_formed(layer, ptr)
    {
        forall|i: nat| i < self.arch@.num_entries(layer) ==> self.view_at(layer, ptr, i, pt).is_Empty()
    }

    pub open spec(checked) fn layer_in_range(self, layer: nat) -> bool {
        layer < self.arch@.layers.len()
    }

    pub open spec(checked) fn inv_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        decreases self.arch@.layers.len() - layer
    {
        &&& self.well_formed(layer, ptr)
        &&& self.memory.inv()
        &&& self.memory.regions().contains(pt.region)
        &&& pt.region.base == ptr
        &&& pt.region.size == PAGE_SIZE
        &&& self.memory.region_view(pt.region).len() == pt.entries.len()
        &&& self.layer_in_range(layer)
        &&& pt.entries.len() == self.arch@.num_entries(layer)
        &&& self.directories_obey_invariant_at(layer, ptr, pt)
        &&& self.ghost_pt_matches_structure(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_rtrancl(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt)
        &&& self.ghost_pt_region_notin_used_regions(layer, ptr, pt)
        &&& pt.used_regions.subset_of(self.memory.regions())
        &&& self.entry_addrs_are_zero_padded(layer, ptr, pt)
    }

    pub open spec fn entry_addrs_are_zero_padded(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat| i < self.arch@.num_entries(layer) ==> {
            let entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt);
            &&& (entry@.is_Page() ==> 0 < entry.layer())
            &&& entry.addr_is_zero_padded()
        }
    }

    pub open spec fn ghost_pt_used_regions_pairwise_disjoint(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat, j: nat, r: MemRegion|
            i != j &&
            i < pt.entries.len() && pt.entries[i].is_Some() &&
            #[trigger] pt.entries[i].get_Some_0().used_regions.contains(r) &&
            j < pt.entries.len() && pt.entries[j].is_Some()
            ==> !(#[trigger] pt.entries[j].get_Some_0().used_regions.contains(r))
    }

    // TODO: this may be implied by the other ones
    pub open spec fn ghost_pt_region_notin_used_regions(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat|
            i < pt.entries.len() && pt.entries[i].is_Some()
            ==> !(#[trigger] pt.entries[i].get_Some_0().used_regions.contains(pt.region))
    }

    pub open spec fn ghost_pt_used_regions_rtrancl(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        // reflexive
        &&& pt.used_regions.contains(pt.region)
        // TODO: May not be necessary. Technically it's already implied by "memory contains pt.region" in the main invariant
        // &&& (forall|r: MemRegion| pt.used_regions.contains(r) ==> #[trigger] self.memory.regions().contains(r))
        // transitive
        &&& forall|i: nat, r: MemRegion| #![trigger pt.entries.index(i).get_Some_0().used_regions.contains(r), pt.used_regions.contains(r)]
                i < pt.entries.len() && pt.entries[i].is_Some() &&
                pt.entries[i].get_Some_0().used_regions.contains(r)
                ==> pt.used_regions.contains(r)
    }

    pub open spec fn interp_at(self, layer: nat, ptr: usize, base_vaddr: nat, pt: PTDir) -> l1::Directory
        decreases (self.arch@.layers.len() - layer, self.arch@.num_entries(layer), 2nat)
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        l1::Directory {
            entries: self.interp_at_aux(layer, ptr, base_vaddr, seq![], pt),
            layer: layer,
            base_vaddr,
            arch: self.arch@,
        }
    }

    pub open spec fn interp_at_entry(self, layer: nat, ptr: usize, base_vaddr: nat, idx: nat, pt: PTDir) -> l1::NodeEntry
        decreases (self.arch@.layers.len() - layer, self.arch@.num_entries(layer) - idx, 0nat)
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        match self.view_at(layer, ptr, idx, pt) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let entry_base = self.arch@.entry_base(layer, base_vaddr, idx);
                l1::NodeEntry::Directory(self.interp_at(layer + 1, dir_addr, entry_base, pt.entries[idx].get_Some_0()))
            },
            GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } =>
                l1::NodeEntry::Page(
                    PageTableEntry {
                        frame: MemRegion { base: addr, size: self.arch@.entry_size(layer) },
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
        decreases (self.arch@.layers.len() - layer, self.arch@.num_entries(layer) - init.len(), 1nat)
    {
        decreases_when(self.inv_at(layer, ptr, pt));
        decreases_by(Self::termination_interp_at_aux);
        if init.len() >= self.arch@.num_entries(layer) {
            init
        } else {
            let entry = self.interp_at_entry(layer, ptr, base_vaddr, init.len(), pt);
            self.interp_at_aux(layer, ptr, base_vaddr, init.add(seq![entry]), pt)
        }
    }

    #[proof] #[verifier(decreases_by)]
    spec fn termination_interp_at_aux(self, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, pt: PTDir) {
        assert(self.directories_obey_invariant_at(layer, ptr, pt));
        assert(self.arch@.layers.len() - (layer + 1) < self.arch@.layers.len() - layer);
        // FIXME: why isn't this going through?
        // Can I somehow assert the decreases here or assert an inequality between tuples?
        assume(false);
    }

    pub open spec fn interp(self) -> l1::Directory {
        let cr3 = self.memory.cr3_spec();
        self.interp_at(0, cr3.base, 0, self.ghost_pt@)
    }

    proof fn lemma_inv_at_different_memory(self, other: PageTable, layer: nat, ptr: usize, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            self.arch === other.arch,
            forall|r: MemRegion| pt.used_regions.contains(r)
                ==> #[trigger] self.memory.region_view(r) === other.memory.region_view(r),
            // Some parts of other's invariant that we should already know
            other.memory.inv(),
            other.memory.regions().contains(pt.region),
            pt.used_regions.subset_of(other.memory.regions()),
        ensures
            other.inv_at(layer, ptr, pt),
        decreases self.arch@.layers.len() - layer
    {
        assert(other.well_formed(layer, ptr));
        assert(other.memory.inv());
        assert(other.memory.regions().contains(pt.region));
        assert(pt.region.base == ptr);
        assert(other.layer_in_range(layer));
        assert(pt.entries.len() == other.arch@.num_entries(layer));
        assert(other.ghost_pt_used_regions_rtrancl(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt));
        assert(other.ghost_pt_region_notin_used_regions(layer, ptr, pt));
        assert(pt.used_regions.subset_of(other.memory.regions()));

        assert forall|i: nat|
        i < other.arch@.num_entries(layer) implies {
            let entry = #[trigger] other.entry_at_spec(layer, ptr, i, pt);
            &&& (entry@.is_Page() ==> 0 < entry.layer())
            &&& entry.addr_is_zero_padded()
        } by
        {
            let entry = #[trigger] other.entry_at_spec(layer, ptr, i, pt);
            let self_entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt);
            assert(entry === self_entry);
        };
        assert(other.entry_addrs_are_zero_padded(layer, ptr, pt));

        assert forall|i: nat|
        i < other.arch@.num_entries(layer) implies {
            let entry = #[trigger] other.view_at(layer, ptr, i, pt);
            &&& entry.is_Directory() == pt.entries[i].is_Some()
            &&& entry.is_Directory() ==> other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0())
        } by
        {
            let entry = other.view_at(layer, ptr, i, pt);
            assert(entry === self.view_at(layer, ptr, i, pt));
            assert(entry.is_Directory() == pt.entries[i].is_Some());
            if entry.is_Directory() {
                let entry_pt = pt.entries[i].get_Some_0();
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
            idx < self.arch@.num_entries(layer),
            pt2.region === pt1.region,
            pt2.entries[idx] === pt1.entries[idx],
            self.inv_at(layer, ptr, pt1),
            other.inv_at(layer, ptr, pt2),
            self.arch === other.arch,
            self.memory.spec_read(ptr as nat + (idx * WORD_SIZE as nat), pt1.region) === other.memory.spec_read(ptr as nat + (idx * WORD_SIZE as nat), pt2.region),
            pt2.entries[idx].is_Some() ==> (forall|r: MemRegion| pt2.entries[idx].get_Some_0().used_regions.contains(r)
                ==> #[trigger] self.memory.region_view(r) === other.memory.region_view(r)),
        ensures
            self.interp_at_entry(layer, ptr, base, idx, pt1) === other.interp_at_entry(layer, ptr, base, idx, pt2),
        decreases self.arch@.layers.len() - layer
    {
        assert(self.view_at(layer, ptr, idx, pt1) === other.view_at(layer, ptr, idx, pt2));
        let next_layer = (layer + 1) as nat;
        match self.view_at(layer, ptr, idx, pt1) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let entry_base = self.arch@.entry_base(layer, base, idx);
                let dir_pt = pt1.entries[idx].get_Some_0();
                assert(dir_pt === pt2.entries[idx].get_Some_0());
                assert(self.directories_obey_invariant_at(layer, ptr, pt1));
                assert(other.directories_obey_invariant_at(layer, ptr, pt2));
                assert(self.inv_at(next_layer, dir_addr, dir_pt));
                self.lemma_interp_at_aux_facts(next_layer, dir_addr, entry_base, seq![], dir_pt);
                other.lemma_interp_at_aux_facts(next_layer, dir_addr, entry_base, seq![], dir_pt);

                assert forall|i: nat| i < self.arch@.num_entries(next_layer) implies
                    self.interp_at_entry(next_layer, dir_addr, entry_base, i, dir_pt)
                        === other.interp_at_entry(next_layer, dir_addr, entry_base, i, dir_pt)
                    && #[trigger] self.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries.index(i)
                        === other.interp_at(next_layer, dir_addr, entry_base, dir_pt).entries.index(i) by
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
            self.interp_at(layer, ptr, base_vaddr, pt).upper_vaddr()  == self.arch@.upper_vaddr(layer, base_vaddr),
            self.interp_at(layer, ptr, base_vaddr, pt).interp().lower == base_vaddr,
            self.interp_at(layer, ptr, base_vaddr, pt).interp().upper == self.arch@.upper_vaddr(layer, base_vaddr),
            ({ let res = self.interp_at(layer, ptr, base_vaddr, pt);
                &&& (forall|j: nat|
                    #![trigger res.entries.index(j)]
                    j < res.entries.len() ==>
                    match self.view_at(layer, ptr, j, pt) {
                        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                            &&& res.entries.index(j).is_Directory()
                            &&& res.entries.index(j).get_Directory_0() === self.interp_at((layer + 1) as nat, dir_addr, self.arch@.entry_base(layer, base_vaddr, j), pt.entries[j].get_Some_0())
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => res.entries.index(j).is_Page() && res.entries.index(j).get_Page_0().frame.base == addr,
                        GhostPageDirectoryEntry::Empty             => res.entries.index(j).is_Empty(),
                    })
                &&& (forall|j: nat| j < res.entries.len() ==> res.entries.index(j) === #[trigger] self.interp_at_entry(layer, ptr, base_vaddr, j, pt))
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

    proof fn lemma_interp_at_aux_facts(self, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            // aligned(base_vaddr, self.arch@.entry_size(layer) * self.arch@.num_entries(layer)),
        ensures
            self.interp_at_aux(layer, ptr, base_vaddr, init, pt).len() == if init.len() > self.arch@.num_entries(layer) { init.len() } else { self.arch@.num_entries(layer) },
            forall|j: nat| j < init.len() ==> #[trigger] self.interp_at_aux(layer, ptr, base_vaddr, init, pt).index(j) === init.index(j),
            ({ let res = self.interp_at_aux(layer, ptr, base_vaddr, init, pt);
                &&& (forall|j: nat|
                    #![trigger res.index(j)]
                    init.len() <= j && j < res.len() ==>
                    match self.view_at(layer, ptr, j, pt) {
                        GhostPageDirectoryEntry::Directory { addr: dir_addr, .. }  => {
                            &&& res.index(j).is_Directory()
                            &&& res.index(j).get_Directory_0() === self.interp_at((layer + 1) as nat, dir_addr, self.arch@.entry_base(layer, base_vaddr, j), pt.entries[j].get_Some_0())
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => res.index(j).is_Page() && res.index(j).get_Page_0().frame.base == addr,
                        GhostPageDirectoryEntry::Empty             => res.index(j).is_Empty(),
                    })
                &&& (forall|j: nat| init.len() <= j && j < res.len() ==> res.index(j) === #[trigger] self.interp_at_entry(layer, ptr, base_vaddr, j, pt))
            }),
        decreases (self.arch@.layers.len() - layer, self.arch@.num_entries(layer) - init.len(), 0nat)
    {
        if init.len() >= self.arch@.num_entries(layer) {
        } else {
            assert(self.directories_obey_invariant_at(layer, ptr, pt));
            let entry = self.interp_at_entry(layer, ptr, base_vaddr, init.len(), pt);
            let init_next = init.add(seq![entry]);

            self.lemma_interp_at_aux_facts(layer, ptr, base_vaddr, init_next, pt);
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn resolve_aux(&self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: Ghost<PTDir>) -> (res: (Result<(usize, PageTableEntryExec), ()>))
        requires
            self.inv_at(layer, ptr, pt@),
            self.interp_at(layer, ptr, base, pt@).inv(),
            self.interp_at(layer, ptr, base, pt@).interp().accepted_resolve(vaddr),
            base <= vaddr < MAX_BASE,
        ensures
            // Refinement of l1
            res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp_at(layer, ptr, base, pt@).resolve(vaddr),
            // Refinement of l0
            res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp_at(layer, ptr, base, pt@).interp().resolve(vaddr),
        // decreases self.arch@.layers.len() - layer
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let entry      = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = ghost(self.interp_at(layer, ptr, base, pt@));
        assert(entry.addr_is_zero_padded());
        proof {
            interp@.lemma_resolve_structure_assertions(vaddr, idx);
            self.lemma_interp_at_facts(layer, ptr, base, pt@);
            indexing::lemma_index_from_base_and_addr(base, vaddr, self.arch@.entry_size(layer), self.arch@.num_entries(layer));
            interp@.lemma_resolve_refines(vaddr);
        }
        if entry.is_mapping() {
            let entry_base: usize = self.arch.entry_base(layer, base, idx);
            proof {
                indexing::lemma_entry_base_from_index(base, idx, self.arch@.entry_size(layer));
                assert(entry_base <= vaddr);
            }
            if entry.is_dir(layer) {
                assert(entry@.is_Directory());
                let dir_addr = entry.address() as usize;
                assert(pt@.entries[idx].is_Some());
                let dir_pt: Ghost<PTDir> = ghost(pt@.entries[idx].get_Some_0());
                assert(self.directories_obey_invariant_at(layer, ptr, pt@));
                proof {
                    assert(interp@.inv());
                    assert(interp@.directories_obey_invariant());
                    assert(interp@.entries[idx].is_Directory());
                    assert(interp@.entries[idx].get_Directory_0().inv());
                    assert(l1::NodeEntry::Directory(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@)) === interp@.entries[idx]);
                    assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt@));
                }
                let res = self.resolve_aux(layer + 1, dir_addr, entry_base, vaddr, dir_pt);
                assert(res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr));
                res
            } else {
                assert(entry@.is_Page());
                assert(interp@.entries.index(idx).is_Page());
                // let offset: usize = vaddr - entry_base;
                // FIXME: need to assume a maximum for physical addresses
                assume(entry@.get_Page_addr() < 10000);
                // assert(offset < self.arch@.entry_size(layer));
                let pte = PageTableEntryExec {
                    frame: MemRegionExec { base: entry.address() as usize, size: self.arch.entry_size(layer) },
                    flags: entry.flags()
                };
                let res = Ok((entry_base, pte));
                // FIXME: should be postcondition of flags function
                assume(pte.flags.is_writable == entry@.get_Page_flag_RW());
                assume(pte.flags.is_supervisor == !entry@.get_Page_flag_US());
                assume(pte.flags.disable_execute == entry@.get_Page_flag_XD());
                proof {
                if interp@.resolve(vaddr).is_Ok() {
                    assert(interp@.entries.index(idx).get_Page_0() === interp@.resolve(vaddr).get_Ok_0().1);
                    assert(interp@.entries.index(idx) === self.interp_at_entry(layer, ptr, base, idx, pt@));
                }
                }
                assert(res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).0) === interp@.resolve(vaddr).map_ok(|v| v.0));
                assert(res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.frame) === interp@.resolve(vaddr).map_ok(|v| v.1.frame));
                assert(res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@).1.flags) === interp@.resolve(vaddr).map_ok(|v| v.1.flags));
                assert(res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr));
                res
            }
        } else {
            assert(entry@.is_Empty());
            assert(interp@.entries.index(idx).is_Empty());
            assert(Err(()).map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === interp@.resolve(vaddr));
            Err(())
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    pub fn resolve(&self, vaddr: usize) -> (res: (Result<(usize, PageTableEntryExec),()>))
        requires
            self.inv(),
            self.interp().inv(),
            self.interp().interp().accepted_resolve(vaddr),
            vaddr < MAX_BASE,
        ensures
            // Refinement of l1
            res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp().resolve(vaddr),
            // Refinement of l0
            res.map_ok(|v: (usize, PageTableEntryExec)| (v.0 as nat, v.1@)) === self.interp().interp().resolve(vaddr),
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        let res = self.resolve_aux(0, cr3.base, 0, vaddr, self.ghost_pt);
        res
    }

    // I have no reason to believe that this functions is particularly problematic and should be
    // opaque. However, after changing it slightly map_frame_aux was timing out and this is a
    // bandaid that allows me to continue without refactoring that entire function's proofs.
    #[verifier(opaque)]
    pub open spec fn accepted_mapping(self, vaddr: nat, pte: PageTableEntry) -> bool {
        // Can't map pages in PML4, i.e. layer 0
        self.arch@.contains_entry_size_at_index_atleast(pte.frame.size, 1)
    }

    // FIXME: pub const KERNEL_BASE: u64 = 0x4000_0000_0000;
    // use that for overflow stuff
    #[verifier(spinoff_prover)] #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn map_frame_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pte: PageTableEntryExec, pt: Ghost<PTDir>)
        -> (res: (Result<Ghost<(PTDir,Set<MemRegion>)>,()>))
        requires
            old(self).inv_at(layer, ptr, pt@),
            old(self).interp_at(layer, ptr, base, pt@).inv(),
            old(self).memory.inv(),
            old(self).accepted_mapping(vaddr, pte@),
            old(self).interp_at(layer, ptr, base, pt@).accepted_mapping(vaddr, pte@),
            base <= vaddr < MAX_BASE,
            // aligned(base, old(self).arch@.entry_size(layer) * old(self).arch@.num_entries(layer)),
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
                    &&& self.inv_at(layer, ptr, pt_res)
                    // We only touch already allocated regions if they're in pt.used_regions
                    &&& (forall|r: MemRegion| !(#[trigger] pt@.used_regions.contains(r)) && !(new_regions.contains(r))
                        ==> self.memory.region_view(r) === old(self).memory.region_view(r))
                    &&& self.arch === old(self).arch
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
                    Ok(self.interp_at(layer, ptr, base, pt_res)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)
                },
                Err(e) =>
                    Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@),
            },
        // decreases self.arch@.layers.len() - layer
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let idxg: Ghost<usize> = ghost(idx);
        let entry = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = ghost(self.interp_at(layer, ptr, base, pt@));
        proof {
            interp@.lemma_map_frame_structure_assertions(vaddr, pte@, idx);
            self.lemma_interp_at_facts(layer, ptr, base, pt@);
            assert({
                &&& between(vaddr, self.arch@.entry_base(layer, base, idx), self.arch@.next_entry_base(layer, base, idx))
                &&& aligned(vaddr, self.arch@.entry_size(layer)) ==> vaddr == self.arch@.entry_base(layer, base, idx)
                &&& idx < MAX_NUM_ENTRIES
                &&& idx < self.arch@.num_entries(layer) }) by
            {
                indexing::lemma_index_from_base_and_addr(base, vaddr, self.arch@.entry_size(layer), self.arch@.num_entries(layer));
            };
            interp@.lemma_map_frame_refines_map_frame(vaddr, pte@);
        }
        let entry_base: usize = self.arch.entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(base, idx, self.arch@.entry_size(layer));
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                if self.arch.entry_size(layer) == pte.frame.size {
                    assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@));
                    Err(())
                } else {
                    let dir_addr = entry.address() as usize;
                    assert(pt@.entries[idx].is_Some());
                    let dir_pt: Ghost<PTDir> = ghost(pt@.entries[idx].get_Some_0());
                    assert(self.directories_obey_invariant_at(layer, ptr, pt@));
                    match self.map_frame_aux(layer + 1, dir_addr, entry_base, vaddr, pte, dir_pt) {
                        Ok(rec_res) => {
                            let dir_pt_res: Ghost<PTDir> = ghost(rec_res@.0);
                            let new_regions: Ghost<Set<MemRegion>> = ghost(rec_res@.1);

                            assert(dir_pt_res@.used_regions === dir_pt@.used_regions.union(new_regions@));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] dir_pt@.used_regions.contains(r)));
                            assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt_res@));
                            assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@))
                                   === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).map_frame(vaddr, pte@));
                            assert(idx == idxg@);
                            assert(idxg@ < pt@.entries.len());
                            let pt_res: Ghost<PTDir> = ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions.union(new_regions@),
                                });

                            assert(idx < pt@.entries.len());
                            assert(pt_res@.region === pt@.region);
                            assert(!new_regions@.contains(pt_res@.region));
                            assert(!dir_pt_res@.used_regions.contains(pt_res@.region));

                            let ptrg: Ghost<usize> = ghost(ptr);
                            assert(self.inv_at(layer, ptr, pt_res@)
                                && Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)) by
                            {
                                assert forall|i: nat| i < self.arch@.num_entries(layer)
                                    implies {
                                        let entry = self.view_at(layer, ptr, i, pt_res@);
                                        entry.is_Directory() == (#[trigger] pt_res@.entries.index(i)).is_Some()
                                    }
                                by {
                                    assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                                    let entry = self.view_at(layer, ptrg@, i, pt_res@);
                                    if i == idxg@ {
                                        assert(i < pt_res@.entries.len());
                                        assert(pt_res@.entries[i].is_Some());
                                        assert(entry.is_Directory());
                                    } else {
                                        assert(pt@.entries[i] === pt_res@.entries[i]);
                                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                                        assert(entry.is_Directory() == pt_res@.entries[i].is_Some());
                                    }
                                };
                                assert(self.ghost_pt_matches_structure(layer, ptr, pt_res@));

                                assert(self.ghost_pt_used_regions_rtrancl(layer, ptr, pt_res@));
                                assert(self.ghost_pt_region_notin_used_regions(layer, ptr, pt_res@));
                                assert forall|i: nat, j: nat, r: MemRegion|
                                    i != j &&
                                    i < pt_res@.entries.len() && pt_res@.entries[i].is_Some() &&
                                    #[trigger] pt_res@.entries[i].get_Some_0().used_regions.contains(r) &&
                                    j < pt_res@.entries.len() && pt_res@.entries[j].is_Some()
                                    implies !(#[trigger] pt_res@.entries[j].get_Some_0().used_regions.contains(r)) by
                                {
                                    assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt@));
                                    if j == idxg@ {
                                        assert(pt_res@.entries[j].get_Some_0() === dir_pt_res@);
                                        assert(pt_res@.entries[i] === pt@.entries[i]);
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
                                        if i == idxg@ {
                                            assert(pt_res@.entries[i].get_Some_0() === dir_pt_res@);
                                            assert(pt_res@.entries[j] === pt@.entries[j]);
                                            if new_regions@.contains(r) {
                                                assert(dir_pt_res@.used_regions.contains(r));
                                                assert(!dir_pt@.used_regions.contains(r));
                                                assert(!old(self).memory.regions().contains(r));
                                                assert(!pt@.entries[j].get_Some_0().used_regions.contains(r));
                                            } else {
                                                assert(dir_pt@.used_regions.contains(r));
                                                assert(!pt@.entries[j].get_Some_0().used_regions.contains(r));
                                            }
                                        } else {
                                            assert(pt_res@.entries[i] === pt@.entries[i]);
                                            assert(pt_res@.entries[j] === pt@.entries[j]);
                                        }
                                    }
                                };
                                assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_res@));

                                assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                                assert forall|i: nat| i < self.arch@.num_entries(layer) implies {
                                    let entry = #[trigger] self.view_at(layer, ptr, i, pt_res@);
                                    entry.is_Directory() ==> {
                                        &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i].get_Some_0())
                                    }
                                }
                                by {
                                    let entry = #[trigger] self.view_at(layer, ptr, i, pt_res@);
                                    let byte_addr = (ptrg@ + i * WORD_SIZE) as nat;
                                    if i == idxg@ {
                                        assert(pt_res@.entries[i].get_Some_0() === dir_pt_res@);
                                        assert(entry.get_Directory_addr() === dir_addr);
                                        assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i].get_Some_0()));
                                    } else {
                                        assert(old(self).directories_obey_invariant_at(layer, ptr, pt@));
                                        assert(pt@.entries[i] === pt_res@.entries[i]);
                                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                                        assert(entry === old(self).view_at(layer, ptr, i, pt_res@));
                                        if entry.is_Directory() {
                                            let pt_entry = pt_res@.entries[i].get_Some_0();
                                            assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_res@));
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
                                            assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0()));
                                            assert(forall|r: MemRegion| pt_res@.entries[i].get_Some_0().used_regions.contains(r)
                                                   ==> #[trigger] self.memory.region_view(r) === old(self).memory.region_view(r));
                                            assert(pt_res@.entries[i].is_Some());
                                            assert(pt_res@.entries[i].get_Some_0().used_regions === pt@.entries[i].get_Some_0().used_regions);
                                            old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0());
                                            assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i].get_Some_0()));
                                        }
                                    }
                                };
                                assert(self.directories_obey_invariant_at(layer, ptr, pt_res@));

                                assert(self.entry_addrs_are_zero_padded(layer, ptr, pt_res@)) by {
                                    assert forall|i: nat|
                                        i < self.arch@.num_entries(layer)
                                        implies {
                                            let entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt_res@);
                                            &&& (entry@.is_Page() ==> 0 < entry.layer())
                                            &&& entry.addr_is_zero_padded()
                                        }
                                    by {
                                        let entry = self.entry_at_spec(layer, ptr, i, pt_res@);
                                        if i == idxg@ {
                                            assert(entry@.is_Page() ==> 0 < entry.layer());
                                            assert(entry.addr_is_zero_padded());
                                        } else {
                                            assert(self.entry_at_spec(layer, ptr, i, pt_res@) === old(self).entry_at_spec(layer, ptr, i, pt@));
                                            assert(old(self).entry_addrs_are_zero_padded(layer, ptr, pt@));
                                            assert(entry@.is_Page() ==> 0 < entry.layer());
                                            assert(entry.addr_is_zero_padded());
                                        }
                                    };
                                };

                                assert(self.inv_at(layer, ptr, pt_res@));

                                assert(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)) by
                                {
                                    self.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt_res@);
                                    assert(pt_res@.region === pt@.region);
                                    // recursive postcondition:
                                    assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@))
                                           === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).map_frame(vaddr, pte@));
                                    assert(self.inv_at(layer, ptr, pt_res@));
                                    assert(old(self).inv_at(layer, ptr, pt@));
                                    assert(pt_res@.entries[idxg@].is_Some());
                                    assert(pt_res@.entries[idxg@].get_Some_0() === dir_pt_res@);

                                    assert(forall|i: nat| i < self.arch@.num_entries(layer) && i != idxg@ ==> pt@.entries[i] === pt_res@.entries[i]);

                                    assert forall|i: nat|
                                        i < old(self).arch@.num_entries(layer) && i != idxg@
                                        implies
                                            self.interp_at(layer, ptr, base, pt_res@).entries.index(i)
                                            === #[trigger] old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries.index(i) by
                                    {
                                        assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).is_Ok());
                                        assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries[i] === old(self).interp_at(layer, ptr, base, pt@).entries[i]);
                                        assert(self.interp_at(layer, ptr, base, pt_res@).entries.index(i) === self.interp_at_entry(layer, ptr, base, i, pt_res@));
                                        assert(old(self).interp_at(layer, ptr, base, pt@).entries.index(i) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                                        if pt_res@.entries[i].is_Some() {
                                            let pt_entry = pt_res@.entries[i].get_Some_0();
                                            assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_res@));
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
                                        old(self).lemma_interp_at_entry_different_memory(*self, layer, ptr, base, i, pt@, pt_res@);
                                        assert(self.interp_at_entry(layer, ptr, base, i, pt_res@) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                                    };

                                    assert(self.interp_at(layer, ptr, base, pt_res@).entries[idxg@] === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries[idxg@]);
                                    assert_seqs_equal!(self.interp_at(layer, ptr, base, pt_res@).entries, old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                                    assert(self.interp_at(layer, ptr, base, pt_res@).entries === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                                    assert(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@));
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
                            assert(self.arch === old(self).arch);
                            assert(pt_res@.region === pt@.region);

                            let res: Ghost<(PTDir,Set<MemRegion>)> = ghost((pt_res@,new_regions@));
                            Ok(res)
                        },
                        Err(e) => {
                            assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@));
                            Err(e)
                        },
                    }
                }
            } else {
                assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@));
                Err(())
            }
        } else {
            if self.arch.entry_size(layer) == pte.frame.size {
                proof {
                    let layerg = layer;
                    assert(0 < layer) by {
                        reveal(Self::accepted_mapping);
                        if layerg == 0 {
                            let iprime = choose|i: nat| 1 <= i && i < self.arch@.layers.len() && #[trigger] self.arch@.entry_size(i) == pte.frame.size;
                            assert(self.arch@.entry_size(0) == pte.frame.size);
                            assert(self.arch@.contains_entry_size_at_index_atleast(pte.frame.size, 1));
                            // FIXME: unstable
                            assume(forall|i: nat| 0 < i < self.arch@.layers.len() ==> self.arch@.entry_size(0) < #[trigger] self.arch@.entry_size(i));
                        }
                    };
                    let frame_base = pte.frame.base as u64;
                    // FIXME: this should be derivable from alignment property in accepted_mapping
                    assume(addr_is_zero_padded(layer, frame_base, true));
                    // FIXME: need additional precondition?
                    assume(frame_base & MASK_ADDR == frame_base);
                }
                let new_page_entry = PageDirectoryEntry::new_page_entry(layer, pte);
                assume(ptr < 100);
                assert(aligned((ptr + idx * WORD_SIZE) as nat, 8));
                let write_addr = ptr + idx * WORD_SIZE;
                let pwmem: Ghost<mem::PageTableMemory> = ghost(self.memory);
                self.memory.write(write_addr, ghost(pt@.region), new_page_entry.entry);
                assert(self.memory.region_view(pt@.region) === pwmem@.region_view(pt@.region).update(idx, new_page_entry.entry));
                assert(self.memory.region_view(pt@.region).len() == self.arch@.num_entries(layer));

                let ptrg: Ghost<usize> = ghost(ptr);
                assert forall|i: nat| i < self.arch@.num_entries(layer)
                    implies {
                        let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                        entry.is_Directory() == pt@.entries[i].is_Some()
                    }
                by {
                    let byte_addr = (ptrg@ + i * WORD_SIZE) as nat;
                    let entry = self.view_at(layer, ptr, i, pt@);
                    if i == idxg@ {
                        assert(entry === new_page_entry@);
                    } else {
                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                    }
                };
                assert(self.inv_at(layer, ptr, pt@)) by {
                    assert(self.ghost_pt_matches_structure(layer, ptr, pt@));

                    assert forall|i: nat| i < self.arch@.num_entries(layer) implies {
                        let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                        entry.is_Directory() ==> {
                            &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0())
                        }
                    }
                    by {
                        let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                        let byte_addr = (ptrg@ + i * WORD_SIZE) as nat;
                        assert(i < self.memory.region_view(pt@.region).len());
                        if i == idxg@ {
                            assert(entry === new_page_entry@);
                            assert(!entry.is_Directory());
                        } else {
                            assert(old(self).directories_obey_invariant_at(layer, ptr, pt@));
                            assert(entry === old(self).view_at(layer, ptr, i, pt@));
                            if entry.is_Directory() {
                                assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0()));
                                assert(pt@.entries[i].is_Some());
                                assert(forall|r: MemRegion| pt@.entries[i].get_Some_0().used_regions.contains(r)
                                       ==> #[trigger] self.memory.region_view(r) === old(self).memory.region_view(r));
                                old(self).lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0());
                                assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0()));
                            }
                        }
                    };
                    assert(self.directories_obey_invariant_at(layer, ptr, pt@));

                    assert(self.ghost_pt_used_regions_rtrancl(layer, ptr, pt@));
                    assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt@));
                    assert(self.entry_addrs_are_zero_padded(layer, ptr, pt@)) by {
                        assert forall|i: nat|
                            i < self.arch@.num_entries(layer)
                            implies {
                                let entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt@);
                                &&& (entry@.is_Page() ==> 0 < entry.layer())
                                &&& entry.addr_is_zero_padded()
                            }
                        by {
                            let entry = self.entry_at_spec(layer, ptr, i, pt@);
                            if i == idxg@ {
                                assert(entry@.is_Page() ==> 0 < entry.layer());
                                assert(entry.addr_is_zero_padded());
                            } else {
                                assert(self.entry_at_spec(layer, ptr, i, pt@) === old(self).entry_at_spec(layer, ptr, i, pt@));
                            }
                        };
                    };
                };


                assert(Ok(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)) by {
                    self.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt@);
                    assert(self.inv_at(layer, ptr, pt@));
                    assert(old(self).inv_at(layer, ptr, pt@));
                    assert(pt@.entries[idxg@].is_None());

                    assert forall|i: nat|
                        i < old(self).arch@.num_entries(layer) && i != idxg@
                        implies
                            self.interp_at(layer, ptr, base, pt@).entries.index(i)
                            === #[trigger] old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries.index(i) by
                    {
                        let byte_addr = (ptrg@ + i * WORD_SIZE) as nat;
                        assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).is_Ok());
                        assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries[i] === old(self).interp_at(layer, ptr, base, pt@).entries[i]);
                        assert(old(self).interp_at(layer, ptr, base, pt@).entries.index(i) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                        assert(old(self).memory.spec_read((ptr + i * WORD_SIZE) as nat, pt@.region) === self.memory.spec_read((ptr + i * WORD_SIZE) as nat, pt@.region));
                        old(self).lemma_interp_at_entry_different_memory(*self, layer, ptr, base, i, pt@, pt@);
                        assert(self.interp_at_entry(layer, ptr, base, i, pt@) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                    };

                    let new_interp = self.interp_at(layer, ptr, base, pt@);
                    assert(new_interp.entries[idxg@] === self.interp_at_entry(layer, ptr, base, idxg@, pt@));
                    assert(self.view_at(layer, ptr, idxg@, pt@) === new_page_entry@);

                    assert(self.interp_at_entry(layer, ptr, base, idxg@, pt@) === l1::NodeEntry::Page(pte@));

                    assert(new_interp.entries[idxg@] === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries[idxg@]);
                    assert_seqs_equal!(new_interp.entries, old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                    assert(new_interp.entries === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                    assert(Ok(new_interp) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@));
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
                assert(self.arch === old(self).arch);
                assert(pt@.region === pt@.region);

                Ok(ghost((pt@, set![])))
            } else {
                let new_dir_region = self.memory.alloc_page();
                let new_dir_ptr = new_dir_region.base;
                let new_dir_ptr_u64 = new_dir_ptr as u64;
                let new_dir_pt: Ghost<PTDir> = ghost(
                    PTDir {
                        region: new_dir_region@,
                        entries: new_seq::<Option<PTDir>>(self.arch@.num_entries(layer), None),
                        used_regions: set![new_dir_region@],
                    });
                proof {
                    lemma_page_aligned_implies_mask_dir_addr_is_identity();
                    assert(new_dir_ptr_u64 & MASK_DIR_ADDR == new_dir_ptr_u64);
                }
                let new_dir_entry = PageDirectoryEntry::new_dir_entry(layer, new_dir_ptr_u64);
                assume(ptr < 100);
                let write_addr = ptr + idx * WORD_SIZE;
                assert(aligned(write_addr, 8));
                self.memory.write(write_addr, ghost(pt@.region), new_dir_entry.entry);


                // After writing the new empty directory entry we prove that the resulting state
                // satisfies the invariant and TODO: probably also that the interpretation remains
                // unchanged.
                let pt_with_empty: Ghost<PTDir> = ghost(
                    PTDir {
                        region:       pt@.region,
                        entries:      pt@.entries.update(idx, Some(new_dir_pt@)),
                        used_regions: pt@.used_regions.insert(new_dir_pt@.region),
                    });
                // For easier reference we take a snapshot of self here. In the subsequent proofs
                // (after the recursive call) we have old(self), self_with_empty and self to refer
                // to each relevant state.
                let self_with_empty: Ghost<Self> = ghost(*self);
                proof {
                    assert(self.arch === old(self).arch);
                    assert(pt_with_empty@.region === pt@.region);
                    lemma_new_seq::<u64>(512nat, 0u64);
                    lemma_new_seq::<Option<PTDir>>(self_with_empty@.arch@.num_entries(layer), None);
                    assert(new_dir_pt@.entries.len() == 512);
                    assert(new_dir_region@.contains(new_dir_ptr));
                    assert(self_with_empty@.memory.region_view(new_dir_region@) === new_seq(512nat, 0u64));
                    self_with_empty@.lemma_zeroed_page_implies_empty_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@);
                    assert(self_with_empty@.empty_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));
                    assert(self_with_empty@.inv_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));

                    assert(forall|r: MemRegion| r !== new_dir_pt@.region && r !== pt_with_empty@.region
                           ==> self_with_empty@.memory.region_view(r) === old(self).memory.region_view(r));
                    assert(self_with_empty@.memory.region_view(pt_with_empty@.region)
                           === old(self).memory.region_view(pt_with_empty@.region).update(idx, new_dir_entry.entry));
                    assert(forall|i: nat| i < self_with_empty@.arch@.num_entries(layer) && i != idxg@ ==> pt@.entries[i] === pt_with_empty@.entries[i]);
                    let ptrg = ptr;
                    assert(self_with_empty@.inv_at(layer, ptr, pt_with_empty@)) by {
                        assert(self_with_empty@.ghost_pt_matches_structure(layer, ptr, pt_with_empty@)) by {
                            assert forall|i: nat|
                                i < self_with_empty@.arch@.num_entries(layer) implies {
                                    let entry = #[trigger] self_with_empty@.view_at(layer, ptr, i, pt_with_empty@);
                                    entry.is_Directory() == pt_with_empty@.entries[i].is_Some()
                                } by
                            {
                                let entry = self_with_empty@.view_at(layer, ptr, i, pt_with_empty@);
                                assert(old(self).directories_obey_invariant_at(layer, ptr, pt@));
                                assert(old(self).ghost_pt_matches_structure(layer, ptr, pt@));
                                if i == idxg@ {
                                } else {
                                    let addr = ptrg as nat + (i * WORD_SIZE as nat);
                                    assert(self_with_empty@.memory.spec_read(addr, pt_with_empty@.region)
                                           === old(self).memory.spec_read(addr, pt@.region));
                                    assert(entry === old(self).view_at(layer, ptr, i, pt@));
                                    assert(entry.is_Directory() == pt_with_empty@.entries[i].is_Some());
                                }
                            };
                        };
                        assert(self_with_empty@.directories_obey_invariant_at(layer, ptr, pt_with_empty@)) by {
                            assert forall|i: nat| i < self_with_empty@.arch@.num_entries(layer) implies {
                                let entry = #[trigger] self_with_empty@.view_at(layer, ptr, i, pt_with_empty@);
                                entry.is_Directory()
                                    ==> self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_with_empty@.entries[i].get_Some_0())
                            } by
                            {
                                let entry = self_with_empty@.view_at(layer, ptr, i, pt_with_empty@);
                                assert(old(self).directories_obey_invariant_at(layer, ptr, pt@));
                                assert(old(self).ghost_pt_matches_structure(layer, ptr, pt@));
                                assert(old(self).ghost_pt_used_regions_rtrancl(layer, ptr, pt@));

                                assert(self.ghost_pt_matches_structure(layer, ptr, pt_with_empty@));
                                if i == idxg@ {
                                } else {
                                    if entry.is_Directory() {
                                        let addr = ptrg as nat + (i * WORD_SIZE as nat);
                                        assert(self_with_empty@.memory.spec_read(addr, pt_with_empty@.region)
                                               === old(self).memory.spec_read(addr, pt@.region));
                                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                                        assert(pt@.entries[i].is_Some());
                                        let pt_entry = pt@.entries[i].get_Some_0();
                                        assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_entry));
                                        assert(pt@.entries[i] === pt_with_empty@.entries[i]);
                                        assert(old(self).memory.regions().contains(pt_entry.region));
                                        assert(self_with_empty@.memory.regions().contains(pt_entry.region));
                                        old(self).lemma_inv_at_different_memory(self_with_empty@, (layer + 1) as nat, entry.get_Directory_addr(), pt_entry);
                                        assert(self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_with_empty@.entries[i].get_Some_0()));
                                    }
                                }
                            };
                        };
                        assert(self_with_empty@.ghost_pt_used_regions_rtrancl(layer, ptr, pt_with_empty@));
                        assert(self_with_empty@.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_with_empty@));
                        assert(self_with_empty@.ghost_pt_region_notin_used_regions(layer, ptr, pt_with_empty@));

                        assert(self_with_empty@.entry_addrs_are_zero_padded(layer, ptr, pt_with_empty@)) by {
                            assert forall|i: nat|
                                i < self_with_empty@.arch@.num_entries(layer)
                                implies {
                                    let entry = #[trigger] self_with_empty@.entry_at_spec(layer, ptr, i, pt_with_empty@);
                                    &&& (entry@.is_Page() ==> 0 < entry.layer())
                                    &&& entry.addr_is_zero_padded()
                                }
                            by {
                                let entry = self_with_empty@.entry_at_spec(layer, ptr, i, pt_with_empty@);
                                if i == idxg@ {
                                    assert(entry@.is_Page() ==> 0 < entry.layer());
                                    assert(entry.addr_is_zero_padded());
                                } else {
                                    assert(self_with_empty@.entry_at_spec(layer, ptr, i, pt_with_empty@) === old(self).entry_at_spec(layer, ptr, i, pt@));
                                    assert(old(self).entry_addrs_are_zero_padded(layer, ptr, pt@));
                                    assert(entry@.is_Page() ==> 0 < entry.layer());
                                    assert(entry.addr_is_zero_padded());
                                }
                            };
                        };


                        assert(self_with_empty@.inv_at(layer, ptr, pt_with_empty@));
                    };

                    assert(self_with_empty@.memory.spec_read(write_addr, pt_with_empty@.region) === new_dir_entry.entry);
                    assert(self_with_empty@.view_at(layer, ptr, idx, pt_with_empty@) === new_dir_entry@);
                    assert(new_dir_entry@.get_Directory_addr() == new_dir_ptr);
                    self_with_empty@.lemma_empty_at_interp_equal_l1_empty_dir(layer, ptr, base, idx, pt_with_empty@, interp@);
                    let new_dir_interp: l1::Directory = self_with_empty@.interp_at((layer + 1) as nat, new_dir_ptr, entry_base, new_dir_pt@);
                    assert(new_dir_interp === interp@.new_empty_dir(idx));

                    old(self).lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt@);
                    self_with_empty@.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt_with_empty@);

                    assert forall|i: nat|
                        i < old(self).arch@.num_entries(layer) && i != idxg@
                        implies
                            self_with_empty@.interp_at(layer, ptr, base, pt_with_empty@).entries.index(i)
                            === #[trigger] old(self).interp_at(layer, ptr, base, pt@).entries.index(i) by
                    {
                        let prev_interp = old(self).interp_at(layer, ptr, base, pt@);
                        let byte_addr = (ptrg + i * WORD_SIZE) as nat;
                        assert(prev_interp.entries.index(i) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                        assert(old(self).memory.spec_read((ptr + i * WORD_SIZE) as nat, pt@.region) === self_with_empty@.memory.spec_read((ptr + i * WORD_SIZE) as nat, pt_with_empty@.region));
                        old(self).lemma_interp_at_entry_different_memory(self_with_empty@, layer, ptr, base, i, pt@, pt_with_empty@);
                        assert(i < self_with_empty@.arch@.num_entries(layer));
                        assert(self_with_empty@.interp_at_entry(layer, ptr, base, i, pt_with_empty@) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                        assert(self_with_empty@.interp_at_entry(layer, ptr, base, i, pt_with_empty@) === self_with_empty@.interp_at(layer, ptr, base, pt_with_empty@).entries.index(i));
                        assert(self_with_empty@.interp_at(layer, ptr, base, pt_with_empty@).entries.index(i)
                               === old(self).interp_at(layer, ptr, base, pt@).entries.index(i));
                    };
                    assert(new_dir_interp.inv());
                }

                assert(self.accepted_mapping(vaddr, pte@)) by {
                    reveal(Self::accepted_mapping);
                };
                match self.map_frame_aux(layer + 1, new_dir_ptr, entry_base, vaddr, pte, new_dir_pt) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = ghost(rec_res@.0);
                        let dir_new_regions: Ghost<Set<MemRegion>> = ghost(rec_res@.1);
                        let pt_final: Ghost<PTDir> = ghost(
                            PTDir {
                                region:       pt_with_empty@.region,
                                entries:      pt_with_empty@.entries.update(idx, Some(dir_pt_res@)),
                                used_regions: pt_with_empty@.used_regions.union(dir_new_regions@),
                            });
                        let new_regions: Ghost<Set<MemRegion>> = ghost(dir_new_regions@.insert(new_dir_region@));
                        proof {
                            let ptrg = ptr;
                            assert(idx < pt_with_empty@.entries.len());
                            assert(!dir_new_regions@.contains(pt_final@.region));
                            assert(!new_dir_pt@.used_regions.contains(pt_final@.region));
                            // Note: Many of these invariant/interp framing proofs are nearly
                            // identical. If I find some time I should extract them into a lemma.
                            // Would clean up this function quite a bit.
                            assert(self.inv_at(layer, ptr, pt_final@)) by {
                                assert(self.ghost_pt_matches_structure(layer, ptr, pt_final@)) by {
                                    assert forall|i: nat|
                                        i < self.arch@.num_entries(layer) implies {
                                            let entry = #[trigger] self.view_at(layer, ptr, i, pt_final@);
                                            entry.is_Directory() == pt_final@.entries[i].is_Some()
                                        } by
                                    {
                                        let entry = self.view_at(layer, ptr, i, pt_final@);
                                        assert(self_with_empty@.directories_obey_invariant_at(layer, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_matches_structure(layer, ptr, pt_with_empty@));
                                        if i == idxg@ {
                                        } else {
                                            let addr = ptrg as nat + (i * WORD_SIZE as nat);
                                            assert(self.memory.spec_read(addr, pt_final@.region)
                                                   === self_with_empty@.memory.spec_read(addr, pt_with_empty@.region));
                                            assert(entry === self_with_empty@.view_at(layer, ptr, i, pt_with_empty@));
                                            assert(entry.is_Directory() == pt_final@.entries[i].is_Some());
                                        }
                                    };
                                };

                                assert(self.directories_obey_invariant_at(layer, ptr, pt_final@)) by {
                                    assert forall|i: nat| i < self.arch@.num_entries(layer) implies {
                                        let entry = #[trigger] self.view_at(layer, ptr, i, pt_final@);
                                        entry.is_Directory()
                                            ==> self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_final@.entries[i].get_Some_0())
                                    } by
                                    {
                                        let entry = self.view_at(layer, ptr, i, pt_final@);
                                        assert(self_with_empty@.directories_obey_invariant_at(layer, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_matches_structure(layer, ptr, pt_with_empty@));
                                        assert(self_with_empty@.ghost_pt_used_regions_rtrancl(layer, ptr, pt_with_empty@));

                                        assert(self.ghost_pt_matches_structure(layer, ptr, pt_final@));
                                        if i == idxg@ {
                                        } else {
                                            assert(pt_final@.entries[i] === pt_with_empty@.entries[i]);
                                            if entry.is_Directory() {
                                                let addr = ptrg as nat + (i * WORD_SIZE as nat);
                                                assert(self.memory.spec_read(addr, pt_final@.region)
                                                       === self_with_empty@.memory.spec_read(addr, pt_with_empty@.region));
                                                assert(entry === self_with_empty@.view_at(layer, ptr, i, pt_with_empty@));
                                                assert(pt_with_empty@.entries[i].is_Some());
                                                let pt_entry = pt_with_empty@.entries[i].get_Some_0();
                                                assert(self_with_empty@.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_entry));
                                                assert(pt_with_empty@.entries[i] === pt_final@.entries[i]);
                                                assert(self_with_empty@.memory.regions().contains(pt_entry.region));
                                                assert(self.memory.regions().contains(pt_entry.region));
                                                assert(forall|r: MemRegion| #[trigger] pt_entry.used_regions.contains(r)
                                                       ==> !dir_new_regions@.contains(r) && !new_dir_pt@.used_regions.contains(r));
                                                assert(forall|r: MemRegion| pt_entry.used_regions.contains(r)
                                                       ==> #[trigger] self_with_empty@.memory.region_view(r) === self.memory.region_view(r));
                                                self_with_empty@.lemma_inv_at_different_memory(*self, (layer + 1) as nat, entry.get_Directory_addr(), pt_entry);
                                                assert(pt_final@.entries[i].get_Some_0() === pt_entry);
                                                assert(self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_final@.entries[i].get_Some_0()));
                                            }
                                        }
                                    };
                                };
                                assert(pt_final@.entries.len() == pt_with_empty@.entries.len());
                                assert(forall|i: nat| i != idxg@ && i < pt_final@.entries.len() ==> pt_final@.entries[i] === pt_with_empty@.entries[i]);
                                assert(self.ghost_pt_used_regions_rtrancl(layer, ptr, pt_final@)) by {
                                    assert forall|i: nat, r: MemRegion|
                                        i < pt_final@.entries.len() &&
                                        pt_final@.entries[i].is_Some() &&
                                        #[trigger] pt_final@.entries[i].get_Some_0().used_regions.contains(r)
                                        implies pt_final@.used_regions.contains(r)
                                    by
                                    {
                                        if i == idxg@ {
                                            if dir_new_regions@.contains(r) {
                                                assert(pt_final@.used_regions.contains(r));
                                            } else {
                                                assert(pt_with_empty@.entries[i].get_Some_0().used_regions.contains(r));
                                                assert(pt_with_empty@.used_regions.contains(r));
                                                assert(pt_final@.used_regions.contains(r));
                                            }
                                        } else {
                                            assert(pt_final@.entries[i] === pt_with_empty@.entries[i]);
                                        }
                                    };
                                };
                                assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_final@)) by {
                                    assert forall|i: nat, j: nat, r: MemRegion|
                                        i != j &&
                                        i < pt_final@.entries.len() && pt_final@.entries[i].is_Some() &&
                                        #[trigger] pt_final@.entries[i].get_Some_0().used_regions.contains(r) &&
                                        j < pt_final@.entries.len() && pt_final@.entries[j].is_Some()
                                        implies !(#[trigger] pt_final@.entries[j].get_Some_0().used_regions.contains(r))
                                    by
                                    {
                                        assert(self_with_empty@.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_with_empty@));
                                        if j == idxg@ {
                                            assert(pt_final@.entries[j].get_Some_0() === dir_pt_res@);
                                            assert(pt_final@.entries[i] === pt@.entries[i]);
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
                                            if i == idxg@ {
                                                assert(pt_final@.entries[i].get_Some_0() === dir_pt_res@);
                                                assert(pt_final@.entries[j] === pt@.entries[j]);
                                                if dir_new_regions@.contains(r) {
                                                    assert(dir_pt_res@.used_regions.contains(r));
                                                    assert(!new_dir_pt@.used_regions.contains(r));
                                                    assert(!self_with_empty@.memory.regions().contains(r));
                                                    assert(!pt@.entries[j].get_Some_0().used_regions.contains(r));
                                                } else {
                                                    assert(new_dir_pt@.used_regions.contains(r));
                                                    assert(!pt@.entries[j].get_Some_0().used_regions.contains(r));
                                                }
                                            } else {
                                                assert(pt_final@.entries[i] === pt@.entries[i]);
                                                assert(pt_final@.entries[j] === pt@.entries[j]);
                                            }
                                        }

                                    };
                                };
                                assert(self.ghost_pt_matches_structure(layer, ptr, pt_final@));
                                assert(self.ghost_pt_region_notin_used_regions(layer, ptr, pt_final@));

                                assert(self.entry_addrs_are_zero_padded(layer, ptr, pt_final@)) by {
                                    assert forall|i: nat|
                                        i < self.arch@.num_entries(layer)
                                        implies {
                                            let entry = #[trigger] self.entry_at_spec(layer, ptr, i, pt_final@);
                                            &&& (entry@.is_Page() ==> 0 < entry.layer())
                                            &&& entry.addr_is_zero_padded()
                                        }
                                    by {
                                        let entry = self.entry_at_spec(layer, ptr, i, pt_final@);
                                        if i == idxg@ {
                                            assert(entry@.is_Page() ==> 0 < entry.layer());
                                            assert(entry.addr_is_zero_padded());
                                        } else {
                                            assert(self.entry_at_spec(layer, ptr, i, pt_final@) === self_with_empty@.entry_at_spec(layer, ptr, i, pt_with_empty@));
                                            assert(self_with_empty@.entry_addrs_are_zero_padded(layer, ptr, pt_with_empty@));
                                            assert(entry@.is_Page() ==> 0 < entry.layer());
                                            assert(entry.addr_is_zero_padded());
                                        }
                                    };
                                };

                                assert(self.inv_at(layer, ptr, pt_final@));
                            };

                            assert(Ok(self.interp_at(layer, ptr, base, pt_final@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)) by {
                                self_with_empty@.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt_with_empty@);
                                assert(self.inv_at(layer, ptr, pt_final@));
                                assert(self_with_empty@.inv_at(layer, ptr, pt_with_empty@));
                                self.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt_final@);

                                assert forall|i: nat|
                                    i < self_with_empty@.arch@.num_entries(layer) && i != idxg@
                                    implies
                                        self.interp_at(layer, ptr, base, pt_final@).entries.index(i)
                                        === #[trigger] self_with_empty@.interp_at(layer, ptr, base, pt_with_empty@).entries.index(i) by
                                {
                                    let prev_interp = self_with_empty@.interp_at(layer, ptr, base, pt_with_empty@);
                                    let byte_addr = (ptrg + i * WORD_SIZE) as nat;
                                    assert(prev_interp.entries.index(i) === self_with_empty@.interp_at_entry(layer, ptr, base, i, pt_with_empty@));
                                    if pt_final@.entries[i].is_Some() {
                                        let pt_entry = pt_final@.entries[i].get_Some_0();
                                        assert(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_final@));
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
                                    assert(self_with_empty@.memory.spec_read((ptr + i * WORD_SIZE) as nat, pt_with_empty@.region) === self.memory.spec_read((ptr + i * WORD_SIZE) as nat, pt_final@.region));
                                    self_with_empty@.lemma_interp_at_entry_different_memory(*self, layer, ptr, base, i, pt_with_empty@, pt_final@);
                                    assert(self.interp_at_entry(layer, ptr, base, i, pt_final@) === self_with_empty@.interp_at_entry(layer, ptr, base, i, pt_with_empty@));
                                };

                                let final_interp = self.interp_at(layer, ptr, base, pt_final@);
                                assert(final_interp.entries[idxg@] === self.interp_at_entry(layer, ptr, base, idxg@, pt_final@));
                                assert(final_interp.entries[idxg@] === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries[idxg@]);
                                assert_seqs_equal!(final_interp.entries, old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                                assert(final_interp.entries === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().entries);
                                assert(final_interp.layer === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().layer);
                                assert(final_interp.base_vaddr === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().base_vaddr);
                                assert(final_interp.arch === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@).get_Ok_0().arch);
                                assert(Ok(self.interp_at(layer, ptr, base, pt_final@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, pte@)) by {
                                };
                            };
                        }

                        // posts
                        proof {
                            assert(self.arch === old(self).arch);
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
                        Ok(ghost((pt_final@, new_regions@)))
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
            self.well_formed(layer, ptr),
            self.memory.inv(),
            self.memory.regions().contains(pt.region),
            pt.region.base == ptr,
            pt.region.size == PAGE_SIZE,
            self.memory.region_view(pt.region).len() == pt.entries.len(),
            pt.region.base == ptr,
            ptr == pt.region.base,
            pt.used_regions === set![pt.region],
            self.layer_in_range(layer),
            pt.entries.len() == self.arch@.num_entries(layer),
            forall|i: nat| i < self.arch@.num_entries(layer) ==> self.memory.region_view(pt.region).index(i) == 0u64,
            forall|i: nat| i < self.arch@.num_entries(layer) ==> pt.entries[i].is_None(),
        ensures
            self.empty_at(layer, ptr, pt),
            self.inv_at(layer, ptr, pt),
    {
        assert forall|i: nat|
            i < self.arch@.num_entries(layer)
            implies
            self.view_at(layer, ptr, i, pt).is_Empty()
            by
        {
            let entry = self.memory.spec_read(ptr as nat + (i * WORD_SIZE as nat), pt.region);
            assert((entry & (1u64 << 0)) != (1u64 << 0)) by (bit_vector) requires entry == 0u64;
        };
        // Can't combine with the first assert forall because manually choosing multiple triggers
        // in assert forall is broken.
        assert forall|i: nat|
            i < self.arch@.num_entries(layer)
            implies
            ((#[trigger] self.entry_at_spec(layer, ptr, i, pt))@.is_Page() ==> 0 < self.entry_at_spec(layer, ptr, i, pt).layer()) &&
            self.entry_at_spec(layer, ptr, i, pt).addr_is_zero_padded()
            by
        {
            let entry = self.memory.spec_read(ptr as nat + (i * WORD_SIZE as nat), pt.region);
            assert((entry & (1u64 << 0)) != (1u64 << 0)) by (bit_vector) requires entry == 0u64;

            let pt_entry = self.entry_at_spec(layer, ptr, i, pt);
            assert(pt_entry@.is_Page() ==> 0 < pt_entry.layer());
            assert(pt_entry.addr_is_zero_padded());

        };
        assert(self.entry_addrs_are_zero_padded(layer, ptr, pt));

        assert(self.directories_obey_invariant_at(layer, ptr, pt));
    }

    proof fn lemma_empty_at_interp_equal_l1_empty_dir(self, layer: nat, ptr: usize, base: nat, idx: nat, pt: PTDir, l1dir: l1::Directory)
        requires
            // TODO: May need more preconditions
            self.inv_at(layer, ptr, pt),
            idx < self.arch@.num_entries(layer),
            self.view_at(layer, ptr, idx, pt).is_Directory(),
            self.empty_at((layer + 1) as nat, self.view_at(layer, ptr, idx, pt).get_Directory_addr(), pt.entries[idx].get_Some_0()),
            l1dir.inv(),
            l1dir.layer === layer,
            l1dir.arch === self.arch@,
            l1dir.base_vaddr === base,
        ensures
            self.interp_at((layer + 1) as nat, self.view_at(layer, ptr, idx, pt).get_Directory_addr(), self.arch@.entry_base(layer, base, idx), pt.entries.index(idx).get_Some_0())
                === l1dir.new_empty_dir(idx)
    {
        // FIXME:
        // For each entry self.interp_at_entry == l1::NodeEntry::Empty()
        // lemma_new_empty_dir
        let c = self.interp_at((layer + 1) as nat, self.view_at(layer, ptr, idx, pt).get_Directory_addr(), self.arch@.entry_base(layer, base, idx), pt.entries.index(idx).get_Some_0());
        let s = l1dir.new_empty_dir(idx);

        assume(false);
        assert(self.inv_at(layer + 1, ptr, pt));

        assert(c.layer == layer + 1);
        assert(l1dir.layer == layer);
        assert(s.layer == layer + 1);
        assert(c.layer === s.layer);

        // assert(s.arch === self.arch@);
        assume(c.arch === s.arch);

        assume(c.base_vaddr === s.base_vaddr);
        assume(c.entries === s.entries);
    }

    proof fn lemma_inv_at_doesnt_use_ghost_pt(self, other: Self, layer: nat, ptr: usize, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            other.memory === self.memory,
            other.arch === self.arch,
        ensures
            other.inv_at(layer, ptr, pt),
        decreases self.arch@.layers.len() - layer
    {
        assert(other.well_formed(layer, ptr));
        assert(other.memory.inv());
        assert(other.memory.regions().contains(pt.region));
        assert(pt.region.base == ptr);
        assert(pt.region.size == PAGE_SIZE);
        assert(other.memory.region_view(pt.region).len() == pt.entries.len());
        assert(other.layer_in_range(layer));
        assert(pt.entries.len() == other.arch@.num_entries(layer));
        assert(other.directories_obey_invariant_at(layer, ptr, pt)) by {
            assert forall|i: nat| i < other.arch@.num_entries(layer) implies {
                let entry = #[trigger] other.view_at(layer, ptr, i, pt);
                entry.is_Directory() ==> {
                    &&& other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0())
                }
            } by
            {
                let entry = other.view_at(layer, ptr, i, pt);
                assert(entry === self.view_at(layer, ptr, i, pt));
                if entry.is_Directory() {
                    assert(self.directories_obey_invariant_at(layer, ptr, pt));
                    assert(self.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0()));
                    self.lemma_inv_at_doesnt_use_ghost_pt(other, layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0());
                    assert(other.inv_at(layer + 1, entry.get_Directory_addr(), pt.entries[i].get_Some_0()));
                }
            };
        };
        assume(false);
        assert(other.ghost_pt_matches_structure(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_rtrancl(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt));
        assert(other.ghost_pt_region_notin_used_regions(layer, ptr, pt));
        assert(pt.used_regions.subset_of(other.memory.regions()));
        assert(other.entry_addrs_are_zero_padded(layer, ptr, pt));
    }

    pub fn map_frame(&mut self, vaddr: usize, pte: PageTableEntryExec) -> (res: MapResult)
        requires
            old(self).inv(),
            old(self).interp().inv(),
            old(self).memory.inv(),
            old(self).accepted_mapping(vaddr, pte@),
            old(self).interp().accepted_mapping(vaddr, pte@),
            vaddr < MAX_BASE,
        ensures
            self.inv(),
            self.interp().inv(),
            self.arch === old(self).arch,
            self.ghost_pt@.region === old(self).ghost_pt@.region,
            // Refinement of l1
            match res {
                MapResult::Ok => {
                    Ok(self.interp()) === old(self).interp().map_frame(vaddr, pte@)
                },
                MapResult::ErrOverlap =>
                    Err(self.interp()) === old(self).interp().map_frame(vaddr, pte@),
            },
            // Refinement of l0
            match res {
                MapResult::Ok => {
                    Ok(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr, pte@)
                },
                MapResult::ErrOverlap =>
                    Err(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr, pte@),
            },
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        match self.map_frame_aux(0, cr3.base, 0, vaddr, pte, self.ghost_pt) {
            Ok(res) => {
                let pt_res: Ghost<PTDir> = ghost(res@.0);
                let new_regions: Ghost<Set<MemRegion>> = ghost(res@.1);
                assert(self.inv_at(0, cr3.base, pt_res@));
                let self_before_pt_update: Ghost<Self> = ghost(*self);
                let old_pt: Ghost<PTDir> = self.ghost_pt;
                self.ghost_pt = pt_res;
                // FIXME: prove lemma that inv_at is preserved when changing self.ghost_pt
                proof {
                    self_before_pt_update@.lemma_inv_at_doesnt_use_ghost_pt(*self, 0, cr3.base, pt_res@);
                    assert(self.inv_at(0, cr3.base, pt_res@));
                }
                // FIXME: prove lemma that interp_at is preserved when changing self.ghost_pt
                assume(self.interp_at(0, cr3.base, 0, self.ghost_pt@) === self_before_pt_update@.interp_at(0, cr3.base, 0, pt_res@));
                proof {
                    // FIXME: add a postcondition to map_frame_aux, saying that cr3 and cr3_region
                    // remain unchanged. Will also need to add that fact to the memory
                    // postconditions for any functions with mutable borrows.
                    assume(cr3 === self.memory.cr3_spec());
                    assert(self.ghost_pt@.region === cr3@);
                    assert(self.inv_at(0, cr3.base, self.ghost_pt@));
                    assert(self.inv());
                    old(self).interp().lemma_map_frame_preserves_inv(vaddr, pte@);
                    assert(self.arch === old(self).arch);
                    assert(Ok(self.interp()) === old(self).interp().map_frame(vaddr, pte@));
                    old(self).interp().lemma_map_frame_refines_map_frame(vaddr, pte@);
                    assert(Ok(self.interp().interp()) === old(self).interp().interp().map_frame(vaddr, pte@));
                    assert(self.interp().inv());
                }
                MapResult::Ok
            },
            Err(e) => {
                proof {
                    old(self).interp().lemma_map_frame_refines_map_frame(vaddr, pte@);
                }
                MapResult::ErrOverlap
            },
        }
    }

    fn is_directory_empty(&self, layer: usize, ptr: usize, pt: Ghost<PTDir>) -> (res: bool)
        requires
            self.inv_at(layer, ptr, pt@),
        ensures
            res === self.empty_at(layer, ptr, pt@)
    {
        assert(self.directories_obey_invariant_at(layer, ptr, pt@));
        let mut idx = 0;
        let num_entries = self.arch.num_entries(layer);
        while idx < num_entries
            invariant
                self.inv_at(layer, ptr, pt@),
                forall|i: nat| i < idx ==> self.view_at(layer, ptr, i, pt@).is_Empty(),
        {
            assert(idx < num_entries);
            // Any chance it's actually faster to just bitwise or all the entries together and check at the end?
            let entry = self.entry_at(layer, ptr, idx, pt);
            if entry.is_mapping() {
                assert(!self.view_at(layer, ptr, idx, pt@).is_Empty());
                assume(!self.empty_at(layer, ptr, pt@));
                return false;
            }
            idx = idx + 1;
        }
        true
    }

    #[verifier(spinoff_prover)] #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn unmap_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: Ghost<PTDir>)
        -> (res: (Result<Ghost<(PTDir,Set<MemRegion>)>,()>))
        requires
            old(self).inv_at(layer, ptr, pt@),
            old(self).interp_at(layer, ptr, base, pt@).inv(),
            old(self).memory.inv(),
            // old(self).accepted_unmap(vaddr),
            old(self).interp_at(layer, ptr, base, pt@).accepted_unmap(vaddr),
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
                    &&& self.inv_at(layer, ptr, pt_res)
                    // We only touch regions in pt.used_regions
                    &&& (forall|r: MemRegion| !(#[trigger] pt_res.used_regions.contains(r))
                        ==> self.memory.region_view(r) === old(self).memory.region_view(r))
                    &&& self.arch === old(self).arch
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
                    Ok(self.interp_at(layer, ptr, base, pt_res)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr)
                },
                Err(e) =>
                    Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr),
            },
        // decreases self.arch@.layers.len() - layer
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let idxg: Ghost<usize> = ghost(idx);
        let entry = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = ghost(self.interp_at(layer, ptr, base, pt@));
        proof {
            interp@.lemma_unmap_structure_assertions(vaddr, idx);
            self.lemma_interp_at_facts(layer, ptr, base, pt@);
            indexing::lemma_index_from_base_and_addr(base, vaddr, self.arch@.entry_size(layer), self.arch@.num_entries(layer));
            interp@.lemma_unmap_refines_unmap(vaddr);
        }
        let entry_base: usize = self.arch.entry_base(layer, base, idx);
        proof {
            indexing::lemma_entry_base_from_index(base, idx, self.arch@.entry_size(layer));
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                let dir_addr = entry.address() as usize;
                assert(pt@.entries[idx].is_Some());
                let dir_pt: Ghost<PTDir> = ghost(pt@.entries[idx].get_Some_0());
                assert(self.directories_obey_invariant_at(layer, ptr, pt@));
                match self.unmap_aux(layer + 1, dir_addr, entry_base, vaddr, dir_pt) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = ghost(rec_res@.0);
                        let removed_regions: Ghost<Set<MemRegion>> = ghost(rec_res@.1);

                        assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt_res@));
                        assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@))
                               === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).unmap(vaddr));
                        assert(idx == idxg@);
                        assert(idxg@ < pt@.entries.len());

                        if self.is_directory_empty(layer + 1, dir_addr, dir_pt_res) {
                            let write_addr = ptr + idx * WORD_SIZE;
                            assume(pt@.region.contains(write_addr));
                            assume(self.memory.regions().contains(pt@.region));
                            assume(self.memory.inv());
                            self.memory.write(write_addr, ghost(pt@.region), 0u64);

                            let pt_res: Ghost<PTDir> = ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx, None),
                                    used_regions: pt@.used_regions.difference(removed_regions@).remove(dir_pt_res@.region),
                                });

                            let res: Ghost<(PTDir,Set<MemRegion>)> = ghost((pt_res@,removed_regions@));
                            // Refinement
                            assume(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
                            // postconditions
                            assume(old(self).memory.regions() === self.memory.regions().union(removed_regions@));
                            assume(pt@.used_regions === pt_res@.used_regions.union(removed_regions@));
                            assume((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] self.memory.regions().contains(r))));
                            assume((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                            assume(self.inv_at(layer, ptr, pt_res@));
                            assume(forall|r: MemRegion| !(#[trigger] pt_res@.used_regions.contains(r))
                                   ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                            assume(self.arch === old(self).arch);
                            assume(pt_res@.region === pt@.region);
                            Ok(res)
                        } else {
                            let pt_res: Ghost<PTDir> = ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions.difference(removed_regions@),
                                });

                            assert(idx < pt@.entries.len());
                            assert(pt_res@.region === pt@.region);

                            let res: Ghost<(PTDir,Set<MemRegion>)> = ghost((pt_res@,removed_regions@));
                            // Refinement
                            assume(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
                            // postconditions
                            assume(old(self).memory.regions() === self.memory.regions().union(removed_regions@));
                            assume(pt@.used_regions === pt_res@.used_regions.union(removed_regions@));
                            assume((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] self.memory.regions().contains(r))));
                            assume((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                            assume(self.inv_at(layer, ptr, pt_res@));
                            assume(forall|r: MemRegion| !(#[trigger] pt_res@.used_regions.contains(r))
                                   ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                            assume(self.arch === old(self).arch);
                            assume(pt_res@.region === pt@.region);
                            Ok(res)
                        }

                    },
                    Err(e) => {
                        assert(self === old(self));
                        assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
                        Err(e)
                    },
                }
            } else {
                if aligned_exec(vaddr, self.arch.entry_size(layer)) {
                    let write_addr = ptr + idx * WORD_SIZE;
                    assume(pt@.region.contains(write_addr));
                    self.memory.write(write_addr, ghost(pt@.region), 0u64);

                    let pt_res: Ghost<PTDir> = pt;
                    let removed_regions: Ghost<Set<MemRegion>> = ghost(Set::empty());
                    let res: Ghost<(PTDir,Set<MemRegion>)> = ghost((pt_res@, removed_regions@));

                    // Refinement
                    assume(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
                    // postconditions
                    assume(old(self).memory.regions() === self.memory.regions().union(removed_regions@));
                    assume(pt@.used_regions === pt_res@.used_regions.union(removed_regions@));
                    assume((forall|r: MemRegion| removed_regions@.contains(r) == !(#[trigger] self.memory.regions().contains(r))));
                    assume((forall|r: MemRegion| removed_regions@.contains(r) ==> !(#[trigger] pt_res@.used_regions.contains(r))));
                    assume(self.inv_at(layer, ptr, pt_res@));
                    assume(forall|r: MemRegion| !(#[trigger] pt_res@.used_regions.contains(r))
                           ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                    assume(self.arch === old(self).arch);
                    assume(pt_res@.region === pt@.region);
                    Ok(res)
                } else {
                    assert(self === old(self));
                    assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
                    Err(())
                }
            }
        } else {
            assert(self === old(self));
            assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).unmap(vaddr));
            Err(())
        }
    }

    // FIXME: need to do tlb invalidate
    pub fn unmap(&mut self, vaddr: usize) -> (res: UnmapResult)
        requires
            old(self).inv(),
            old(self).interp().inv(),
            old(self).memory.inv(),
            // old(self).accepted_unmap(vaddr),
            old(self).interp().accepted_unmap(vaddr),
            vaddr < MAX_BASE,
        ensures
            self.inv(),
            self.interp().inv(),
            self.arch === old(self).arch,
            self.ghost_pt@.region === old(self).ghost_pt@.region,
            // Refinement of l1
            match res {
                UnmapResult::Ok => {
                    Ok(self.interp()) === old(self).interp().unmap(vaddr)
                },
                UnmapResult::ErrNoSuchMapping =>
                    Err(self.interp()) === old(self).interp().unmap(vaddr),
            },
            // Refinement of l0
            match res {
                UnmapResult::Ok => {
                    Ok(self.interp().interp()) === old(self).interp().interp().unmap(vaddr)
                },
                UnmapResult::ErrNoSuchMapping =>
                    Err(self.interp().interp()) === old(self).interp().interp().unmap(vaddr),
            },
    {
        proof { ambient_arith(); }
        let cr3 = self.memory.cr3();
        match self.unmap_aux(0, cr3.base, 0, vaddr, self.ghost_pt) {
            Ok(res) => {
                let pt_res: Ghost<PTDir> = ghost(res@.0);
                assert(self.inv_at(0, cr3.base, pt_res@));
                let self_before_pt_update: Ghost<Self> = ghost(*self);
                self.ghost_pt = pt_res;
                // FIXME: prove lemma that inv_at is preserved when changing self.ghost_pt
                assume(self.inv_at(0, cr3.base, pt_res@));
                // FIXME: prove lemma that interp_at is preserved when changing self.ghost_pt
                assume(self.interp_at(0, cr3.base, 0, self.ghost_pt@) === self_before_pt_update@.interp_at(0, cr3.base, 0, pt_res@));
                proof {
                    // FIXME: add a postcondition to map_frame_aux, saying that cr3 and cr3_region
                    // remain unchanged. Will also need to add that fact to the memory
                    // postconditions for any functions with mutable borrows.
                    assume(cr3 === self.memory.cr3_spec());
                    assert(self.ghost_pt@.region === cr3@);
                    assert(self.inv_at(0, cr3.base, self.ghost_pt@));
                    assert(self.inv());
                    old(self).interp().lemma_unmap_preserves_inv(vaddr);
                    assert(self.arch === old(self).arch);
                    assert(Ok(self.interp()) === old(self).interp().unmap(vaddr));
                    old(self).interp().lemma_unmap_refines_unmap(vaddr);
                    assert(Ok(self.interp().interp()) === old(self).interp().interp().unmap(vaddr));
                    assert(self.interp().inv());
                }
                UnmapResult::Ok
            },
            Err(e) => {
                proof {
                    old(self).interp().lemma_unmap_refines_unmap(vaddr);
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
