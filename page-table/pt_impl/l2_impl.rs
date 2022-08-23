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
use crate::lib_axiom::*;

use result::{*, Result::*};

use crate::aux_defs::{ Arch, ArchExec, MemRegion, MemRegionExec, overlap, between, aligned, new_seq };
use crate::aux_defs::{ MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, ENTRY_BYTES, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS };
use crate::pt_impl::l1;
use crate::pt_impl::l0::{ambient_arith};
use crate::mem::{ self, word_index_spec };

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
const MASK_FLAG_P:    u64 = bit!(0u64);
const MASK_FLAG_RW:   u64 = bit!(1u64);
const MASK_FLAG_US:   u64 = bit!(2u64);
const MASK_FLAG_PWT:  u64 = bit!(3u64);
const MASK_FLAG_PCD:  u64 = bit!(4u64);
const MASK_FLAG_A:    u64 = bit!(5u64);
const MASK_FLAG_XD:   u64 = bit!(63u64);
// We can use the same address mask for all layers as long as we preserve the invariant that the
// lower bits that *should* be masked off are already zero.
const MASK_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);
// const MASK_ADDR:      u64 = 0b0000000000001111111111111111111111111111111111111111000000000000;

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
const MASK_PG_FLAG_D:    u64 = bit!(6u64);
const MASK_PG_FLAG_G:    u64 = bit!(8u64);
const MASK_PG_FLAG_PAT:  u64 = bit!(12u64);

const MASK_L1_PG_FLAG_PS:   u64 = bit!(7u64);
const MASK_L2_PG_FLAG_PS:   u64 = bit!(7u64);

const MASK_L3_PG_FLAG_PAT:  u64 = bit!(7u64);

// const MASK_DIR_REFC:           u64 = bitmask_inc!(52u64,62u64); // Ignored bits for storing refcount in L3 and L2
// const MASK_DIR_L1_REFC:        u64 = bitmask_inc!(8u64,12u64); // Ignored bits for storing refcount in L1
// const MASK_DIR_REFC_SHIFT:     u64 = 52u64;
// const MASK_DIR_L1_REFC_SHIFT:  u64 = 8u64;
const MASK_DIR_ADDR:           u64 = MASK_ADDR;

// We should be able to always use the 12:52 mask and have the invariant state that in the
// other cases, the lower bits are already zero anyway.
const MASK_L1_PG_ADDR:      u64 = bitmask_inc!(30u64,MAXPHYADDR_BITS);
const MASK_L2_PG_ADDR:      u64 = bitmask_inc!(21u64,MAXPHYADDR_BITS);
const MASK_L3_PG_ADDR:      u64 = bitmask_inc!(12u64,MAXPHYADDR_BITS);

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
            addr & MASK_ADDR == addr & MASK_L1_PG_ADDR
        } else if layer == 2 {
            addr & MASK_ADDR == addr & MASK_L2_PG_ADDR
        } else if layer == 3 {
            addr & MASK_ADDR == addr & MASK_L3_PG_ADDR
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
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
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
                let addr     = (v & MASK_ADDR) as usize;
                let flag_P   = v & MASK_FLAG_P   == MASK_FLAG_P;
                let flag_RW  = v & MASK_FLAG_RW  == MASK_FLAG_RW;
                let flag_US  = v & MASK_FLAG_US  == MASK_FLAG_US;
                let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
                let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
                let flag_A   = v & MASK_FLAG_A   == MASK_FLAG_A;
                let flag_XD  = v & MASK_FLAG_XD  == MASK_FLAG_XD;
                if (self.layer() == 3) || (v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) {
                    let flag_D   = v & MASK_PG_FLAG_D   == MASK_PG_FLAG_D;
                    let flag_G   = v & MASK_PG_FLAG_G   == MASK_PG_FLAG_G;
                    let flag_PAT = if self.layer() == 3 { v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT } else { v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT };
                    GhostPageDirectoryEntry::Page {
                        addr,
                        flag_P, flag_RW, flag_US, flag_PWT, flag_PCD,
                        flag_A, flag_D, flag_G, flag_PAT, flag_XD,
                    }
                } else {
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

    pub open spec fn inv(self) -> bool {
        &&& self.layer() <= 3
        &&& self.addr_is_zero_padded()
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
        ensures
            ({ let e = address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { MASK_FLAG_US }        else { 0 }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 };
                e & MASK_ADDR == address
            }),
    {
        assume(false);
    }

    pub fn new_page_entry(layer: usize, address: u64) -> (r: Self)
        requires
            0 < layer <= 3,
            addr_is_zero_padded(layer, address, true),
        ensures
            r.inv(),
            r@.is_Page(),
            r.layer == layer,
            // r@.get_Page_addr() == address,
    {
        // FIXME: check what flags we want here
        Self::new_entry(layer, address, true, true, true, false, false, false)
    }

    pub fn new_dir_entry(layer: usize, address: u64) -> (r: Self)
        requires
            layer < 3,
            address & MASK_DIR_ADDR == address
        ensures
            r.inv(),
            r@.is_Directory(),
            r.layer == layer,
            // r@.get_Directory_addr() == address,
    {
        // FIXME: check what flags we want here
        Self::new_entry(layer, address, false, true, true, false, false, false)
    }

    pub fn new_entry(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool, // TODO: is this inverted, 0 is user-mode-access allowed, 1 is disallowed
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> (r: PageDirectoryEntry)
        requires
            layer <= 3,
            if is_page { 0 < layer } else { layer < 3 },
            addr_is_zero_padded(layer, address, is_page),
        ensures
            if is_page { r@.is_Page() } else { r@.is_Directory() },
            r.inv(),
            r.layer == layer,
    {
        let e =
        PageDirectoryEntry {
            entry: {
                address
                | MASK_FLAG_P
                | if is_page && layer != 3 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { MASK_FLAG_US }        else { 0 }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 }
            },
            layer: layer as nat,
        };

        proof {
            assert(e.layer() <= 3);
            if e.layer() <= 3 {
                if e.entry & MASK_FLAG_P == MASK_FLAG_P {
                    if e.layer() == 3 {
                        assert(is_page);
                        assert(e@.is_Page());
                    } else if e.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                        // FIXME: bitvector
                        assume(is_page);
                        assert(e@.is_Page());
                    } else {
                        // FIXME: bitvector
                        assume(!is_page);
                        assert(e@.is_Directory());
                    }
                } else {
                    // FIXME: bitvector
                    assume(false);
                }
            }
            assert(if is_page { e@.is_Page() } else { e@.is_Directory() });

            if is_page {
                assert_by(e.addr_is_zero_padded(), {
                    // lemma_addr_masks_facts(address);
                    // lemma_addr_masks_facts2(e.entry);
                    // Self::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
                    // assert(addr_is_zero_padded(layer, address, true));
                    // FIXME: bitvector
                    // Need to show that we aren't setting any of the bits that are masked off by
                    // the L1/L2 masks but not masked off by MASK_ADDR
                    if e.layer() == 1 {
                        assume(e.entry & MASK_ADDR == e.entry & MASK_L1_PG_ADDR);
                    } else if e.layer() == 2 {
                        assume(e.entry & MASK_ADDR == e.entry & MASK_L2_PG_ADDR);
                    } else if e.layer() == 3 {
                        assert(e.entry & MASK_ADDR == e.entry & MASK_L3_PG_ADDR);
                    }
                });
            } else {
                assert(e.addr_is_zero_padded());
            }
        }
        e
    }

    pub fn address(&self) -> (res: u64)
        requires
            self.layer() <= 3,
            !self@.is_Empty(),
        ensures
            res as usize == match self@ {
                GhostPageDirectoryEntry::Page { addr, .. }      => addr,
                GhostPageDirectoryEntry::Directory { addr, .. } => addr,
                GhostPageDirectoryEntry::Empty                  => arbitrary(),
            }
    {
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
    // pub mem_structure: Ghost<Map<MemRegion,Seq<MemRegion>>>,
    // /// Reflexive, transitive closure of `mem_structure`
    // pub mem_rtrancl: Ghost<Map<MemRegion,Set<MemRegion>>>,
}

impl PageTable {
    pub open spec(checked) fn well_formed(self, layer: nat, ptr: usize) -> bool {
        &&& self.arch@.inv()
        &&& aligned(ptr, PAGE_SIZE)
    }

    pub open spec(checked) fn inv(&self) -> bool {
        let (cr3_region, cr3) = self.memory.cr3_spec();
        &&& self.ghost_pt@.region === cr3_region
        &&& self.inv_at(0, cr3, self.ghost_pt@)
    }

    /// Get the view of the entry at address ptr + i * ENTRY_BYTES
    pub open spec fn view_at(self, layer: nat, ptr: usize, i: nat, pt: PTDir) -> GhostPageDirectoryEntry {
        PageDirectoryEntry {
            entry: self.memory.spec_read(ptr as nat + i * ENTRY_BYTES, pt.region),
            layer,
        }@
    }

    /// Get the entry at address ptr + i * ENTRY_BYTES
    #[verifier(nonlinear)]
    fn entry_at(&self, layer: usize, ptr: usize, i: usize, pt: Ghost<PTDir>) -> (res: PageDirectoryEntry)
        requires
            self.inv_at(layer, ptr, pt@)
        ensures
            res.layer == layer,
            res@ === self.view_at(layer, ptr, i, pt@),
    {
        // FIXME:
        assume(ptr <= 100);
        assume(i * ENTRY_BYTES <= 100000);
        assume(aligned((ptr + i * ENTRY_BYTES) as nat, 8));
        // FIXME:
        assume(pt@.region.contains((ptr + i * ENTRY_BYTES) as nat));
        assert(self.memory.inv());
        PageDirectoryEntry {
            entry: self.memory.read(ptr + i * ENTRY_BYTES, ghost(pt@.region)),
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

    // pub open spec fn obtain_mem_partitions(self, layer: nat, ptr: usize) -> Seq<Set<MemRegion>>
    //     recommends self.directories_obey_invariant_at(layer, ptr)
    // {
    //     choose|mem_partitions: Seq<Set<MemRegion>>| {
    //         &&& mem_partitions.len() == self.arch@.num_entries(layer)
    //         // Union of the partitions is the whole set minus the current directory:
    //         &&& seq_union(mem_partitions) === regions.remove(self.obtain_dir_region(layer, ptr))
    //         // No duplicates:
    //         &&& (forall|i: nat, j: nat, r: MemRegion|
    //                 i != j && i < mem_partitions.len() && j < mem_partitions.len() && #[trigger] mem_partitions[i].contains(r)
    //                     ==> !(#[trigger] mem_partitions[j].contains(r)))
    //         &&& forall|i: nat| i < self.arch@.num_entries(layer) ==> {
    //             let entry = #[trigger] self.view_at(layer, ptr, i, self.obtain_dir_region(layer, ptr));
    //             entry.is_Directory() ==> self.inv_at(layer + 1, entry.get_Directory_addr())
    //         }
    //     }
    // }

    pub open spec fn empty_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        recommends self.well_formed(layer, ptr)
    {
        forall|i: nat| i < self.arch@.num_entries(layer) ==> self.view_at(layer, ptr, i, pt).is_Empty()
    }

    pub open spec(checked) fn layer_in_range(self, layer: nat) -> bool {
        layer < self.arch@.layers.len()
    }

    // pub open spec fn mem_rtrancl_is_rtrancl(self, layer: nat, ptr: usize, region: MemRegion) -> bool {
    //     &&& self.mem_rtrancl@.dom().contains(region)
    //     // reflexive
    //     &&& self.mem_rtrancl@[region].contains(region)
    //     // transitive
    //     &&& forall|i: nat, r: MemRegion| i < self.arch@.num_entries(layer) ==> {
    //         let entry = #[trigger] self.view_at(layer, ptr, i, region);
    //         let dir_region = self.mem_structure@[region][i];
    //         entry.is_Directory() && self.mem_rtrancl@[dir_region].contains(r)
    //             ==> #[trigger] self.mem_rtrancl@[region].contains(r)
    //     }
    // }

    pub open spec(checked) fn inv_at(self, layer: nat, ptr: usize, pt: PTDir) -> bool
        decreases self.arch@.layers.len() - layer
    {
        &&& self.well_formed(layer, ptr)
        &&& self.memory.inv()
        &&& self.memory.regions().contains(pt.region)
        &&& pt.region.contains(ptr)
        &&& self.layer_in_range(layer)
        &&& pt.entries.len() == self.arch@.num_entries(layer)
        &&& self.directories_obey_invariant_at(layer, ptr, pt)
        &&& self.ghost_pt_matches_structure(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_rtrancl(layer, ptr, pt)
        &&& self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt)
        &&& self.ghost_pt_region_notin_used_regions(layer, ptr, pt)
        &&& pt.used_regions.subset_of(self.memory.regions())
    }
    
    pub open spec fn ghost_pt_used_regions_pairwise_disjoint(self, layer: nat, ptr: usize, pt: PTDir) -> bool {
        forall|i: nat, j: nat, r: MemRegion|
            i != j &&
            i < pt.entries.len() && pt.entries[i].is_Some() &&
            #[trigger] pt.entries[i].get_Some_0().used_regions.contains(r) &&
            j < pt.entries.len() && pt.entries[j].is_Some()
            ==> !(#[trigger] pt.entries[j].get_Some_0().used_regions.contains(r))
    }

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
            GhostPageDirectoryEntry::Page { addr, .. } =>
                l1::NodeEntry::Page(MemRegion { base: addr, size: self.arch@.entry_size(layer) }),
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

    spec fn interp(self) -> l1::Directory {
        let (cr3_region, cr3) = self.memory.cr3_spec();
        self.interp_at(0, cr3, 0, self.ghost_pt@)
    }

    proof fn lemma_inv_at_different_memory(self, other: PageTable, layer: nat, ptr: usize, pt: PTDir)
        requires
            self.inv_at(layer, ptr, pt),
            self.arch@ === other.arch@,
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
        assert(pt.region.contains(ptr));
        assert(other.layer_in_range(layer));
        assert(pt.entries.len() == other.arch@.num_entries(layer));
        assert(other.ghost_pt_used_regions_rtrancl(layer, ptr, pt));
        assert(other.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt));
        assert(other.ghost_pt_region_notin_used_regions(layer, ptr, pt));
        assert(pt.used_regions.subset_of(other.memory.regions()));

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

    // proof fn lemma_interp_at_different_memory(self, other: PageTable, layer: nat, ptr: usize, base_vaddr: nat)
    //     requires
    //         self.inv_at(layer, ptr),
    //         other.memory.inv(),
    //         self.arch@ === other.arch@,
    //         forall|r: MemRegion| #[trigger] regions.contains(r) ==> self.memory.regions().contains(r) && other.memory.regions().contains(r),
    //         forall|r: MemRegion| #[trigger] regions.contains(r) ==> self.memory.region_view(r) === other.memory.region_view(r),
    //     ensures
    //         self.interp_at(layer, ptr, base_vaddr) === other.interp_at(layer, ptr, base_vaddr, regions),
    // {
    //     self.lemma_inv_at_different_memory(other, layer, ptr);
    //     assume(false);
    // }

    // proof fn lemma_interp_at_aux_different_memory(self, other: PageTable, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>)
    //     requires
    //         self.inv_at(layer, ptr),
    //         other.memory.inv(),
    //         self.arch@ === other.arch@,
    //         forall|r: MemRegion| #[trigger] regions.contains(r) ==> self.memory.regions().contains(r) && other.memory.regions().contains(r),
    //         forall|r: MemRegion| #[trigger] regions.contains(r) ==> self.memory.region_view(r) === other.memory.region_view(r),
    //     ensures
    //         self.interp_at_aux(layer, ptr, base_vaddr, init) === other.interp_at_aux(layer, ptr, base_vaddr, init, regions),
    //     decreases (self.arch@.layers.len() - layer, self.arch@.num_entries(layer) - init.len(), 0nat)
    // {
    //     self.lemma_inv_at_different_memory(other, layer, ptr);
    //     self.lemma_interp_at_aux_facts(layer, ptr, base_vaddr, init);
    //     if init.len() >= self.arch@.num_entries(layer) {
    //     } else {
    //         assert(self.directories_obey_invariant_at(layer, ptr));
    //         assert(other.directories_obey_invariant_at(layer, ptr));
    //         assert(self.obtain_dir_region(layer, ptr) === other.obtain_dir_region(layer, ptr, regions));
    //         assert(self.view_at(layer, ptr, init.len(), self.obtain_dir_region(layer, ptr)) === other.view_at(layer, ptr, init.len(), other.obtain_dir_region(layer, ptr, regions)));
    //         let entry = match self.view_at(layer, ptr, init.len(), self.obtain_dir_region(layer, ptr)) {
    //             GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
    //                 let entry_base = self.arch@.entry_base(layer, base_vaddr, init.len());
    //                 assert(entry_base === other.arch@.entry_base(layer, base_vaddr, init.len()));
    //                 let mem_partitions = self.obtain_mem_partitions(layer, ptr);
    //                 assert(mem_partitions === other.obtain_mem_partitions(layer, ptr));
    //                 // assume(forall|r: MemRegion| #[trigger] mem_partitions[init.len()].contains(r) ==> regions.contains(r));
    //                 // self.lemma_interp_at_aux_different_memory(other, layer + 1, dir_addr, entry_base, seq![]);
    //                 // assert(self.interp_at_aux(layer + 1, dir_addr, entry_base, seq![]) === other.interp_at_aux(layer + 1, dir_addr, entry_base, seq![], mem_partitions[init.len()]));
    //                 assert(self.interp_at(layer + 1, dir_addr, entry_base) === other.interp_at(layer + 1, dir_addr, entry_base, mem_partitions[init.len()]));
    //                 self.lemma_interp_at_aux_facts(layer + 1, dir_addr, entry_base, seq![]);
    //                 // assume(false);
    //                 l1::NodeEntry::Directory(self.interp_at(layer + 1, dir_addr, entry_base))
    //             },
    //             GhostPageDirectoryEntry::Page { addr, .. } =>
    //                 l1::NodeEntry::Page(MemRegion { base: addr, size: self.arch@.entry_size(layer) }),
    //             GhostPageDirectoryEntry::Empty =>
    //                 l1::NodeEntry::Empty(),
    //         };
    //         let init_next = init.add(seq![entry]);

    //         self.lemma_interp_at_aux_different_memory(other, layer, ptr, base_vaddr, init_next);
    //     }
    // }

    proof fn lemma_interp_at_facts(self, layer: nat, ptr: usize, base_vaddr: nat, pt: PTDir)
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
                        GhostPageDirectoryEntry::Page { addr, .. } => res.entries.index(j).is_Page() && res.entries.index(j).get_Page_0().base == addr,
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
                        GhostPageDirectoryEntry::Page { addr, .. } => res.index(j).is_Page() && res.index(j).get_Page_0().base == addr,
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
    fn resolve_aux(&self, layer: usize, ptr: usize, base: usize, vaddr: usize, pt: Ghost<PTDir>) -> (res: (Result<usize, ()>))
        requires
            self.inv_at(layer, ptr, pt@),
            self.interp_at(layer, ptr, base, pt@).inv(),
            self.interp_at(layer, ptr, base, pt@).interp().accepted_resolve(vaddr),
            base <= vaddr < MAX_BASE,
            // aligned(base, self.arch@.entry_size(layer) * self.arch@.num_entries(layer)),
        ensures
            // Refinement of l1
            res.map_ok(|v: usize| v as nat) === self.interp_at(layer, ptr, base, pt@).resolve(vaddr),
            // Refinement of l0
            res.map_ok(|v: usize| v as nat) === self.interp_at(layer, ptr, base, pt@).interp().resolve(vaddr),
        // decreases self.arch@.layers.len() - layer
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let entry      = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = ghost(self.interp_at(layer, ptr, base, pt@));
        proof {
            interp@.lemma_resolve_structure_assertions(vaddr, idx);
            self.lemma_interp_at_facts(layer, ptr, base, pt@);
            self.arch@.lemma_index_for_vaddr(layer, base, vaddr);
            interp@.lemma_resolve_refines(vaddr);
        }
        if entry.is_mapping() {
            let entry_base: usize = self.arch.entry_base(layer, base, idx);
            proof {
                self.arch@.lemma_entry_base();
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
                assert(res.map_ok(|v: usize| v as nat) === interp@.resolve(vaddr));
                res
            } else {
                assert(entry@.is_Page());
                assert(interp@.entries.index(idx).is_Page());
                let offset: usize = vaddr - entry_base;
                // FIXME: need to assume a maximum for physical addresses
                assume(entry@.get_Page_addr() < 10000);
                assert(offset < self.arch@.entry_size(layer));
                let res = Ok(entry.address() as usize + offset);
                assert(res.map_ok(|v: usize| v as nat) === interp@.resolve(vaddr));
                res
            }
        } else {
            assert(entry@.is_Empty());
            assert(interp@.entries.index(idx).is_Empty());
            assert(Err(()).map_ok(|v: usize| v as nat) === interp@.resolve(vaddr));
            Err(())
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn resolve(&self, vaddr: usize) -> (res: (Result<usize,()>))
        requires
            self.inv(),
            self.interp().inv(),
            self.interp().interp().accepted_resolve(vaddr),
            vaddr < MAX_BASE,
        ensures
            // Refinement of l1
            res.map_ok(|v: usize| v as nat) === self.interp().resolve(vaddr),
            // Refinement of l0
            // res.map_ok(|v: usize| v as nat) === self.interp().interp().resolve(vaddr),
    {
        proof { ambient_arith(); }
        let (cr3_region, cr3) = self.memory.cr3();
        self.resolve_aux(0, cr3, 0, vaddr, self.ghost_pt)
    }

    spec fn accepted_mapping(self, layer: nat, ptr: usize, base: nat, vaddr: nat, frame: MemRegion) -> bool {
        &&& 0 < layer // Can't map pages in PML4
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn map_frame_aux(&mut self, layer: usize, ptr: usize, base: usize, vaddr: usize, frame: MemRegionExec, pt: Ghost<PTDir>)
        -> (res: (Result<Ghost<(PTDir,Set<MemRegion>)>,()>))
        requires
            old(self).inv_at(layer, ptr, pt@),
            old(self).interp_at(layer, ptr, base, pt@).inv(),
            old(self).memory.inv(),
            old(self).accepted_mapping(layer, ptr, base, vaddr, frame@),
            old(self).interp_at(layer, ptr, base, pt@).accepted_mapping(vaddr, frame@),
            base <= vaddr < MAX_BASE,
            // aligned(base, old(self).arch@.entry_size(layer) * old(self).arch@.num_entries(layer)),
        ensures
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    // We return the regions that we added
                    &&& self.memory.regions() === old(self).memory.regions().union(new_regions)
                    &&& pt_res.used_regions === pt@.used_regions.union(new_regions)
                    // only those we added
                    &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)))
                    &&& (forall|r: MemRegion| new_regions.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)))
                    // Invariant preserved
                    &&& self.inv_at(layer, ptr, pt_res)
                },
                Err(e) => {
                    // If error, unchanged
                    &&& self === old(self)
                },
            },
            // We only touch regions in pt.used_regions
            forall|r: MemRegion| !pt@.used_regions.contains(r) ==> self.memory.region_view(r) === old(self).memory.region_view(r),
            // Refinement of l1
            match res {
                Ok(resv) => {
                    let (pt_res, new_regions) = resv@;
                    Ok(self.interp_at(layer, ptr, base, pt_res)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@)
                },
                Err(e) =>
                    Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@),
            },
            // // Refinement of l0
            // match res {
            //     Ok(res) =>
            //         Ok(self.interp_at(layer, ptr, base).interp())
            //             === old(self).interp_at(layer, ptr, base).interp().map_frame(vaddr, frame@),
            //     Err(e)  => Err(e) === old(self).interp_at(layer, ptr, base).interp().map_frame(vaddr, frame@),
            // }
        // decreases self.arch@.layers.len() - layer
    {
        let idx: usize = self.arch.index_for_vaddr(layer, base, vaddr);
        let idxg: Ghost<usize> = ghost(idx);
        let entry = self.entry_at(layer, ptr, idx, pt);
        let interp: Ghost<l1::Directory> = ghost(self.interp_at(layer, ptr, base, pt@));
        proof {
            interp@.lemma_map_frame_structure_assertions(vaddr, frame@, idx);
            self.lemma_interp_at_facts(layer, ptr, base, pt@);
            self.arch@.lemma_index_for_vaddr(layer, base, vaddr);
            interp@.lemma_map_frame_refines_map_frame(vaddr, frame@);
        }
        let entry_base: usize = self.arch.entry_base(layer, base, idx);
        proof {
            self.arch@.lemma_entry_base();
            assert(entry_base <= vaddr);
        }
        if entry.is_mapping() {
            if entry.is_dir(layer) {
                if self.arch.entry_size(layer) == frame.size {
                    assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));
                    Err(())
                } else {
                    let dir_addr = entry.address() as usize;
                    assert(pt@.entries[idx].is_Some());
                    let dir_pt: Ghost<PTDir> = ghost(pt@.entries[idx].get_Some_0());
                    assert(self.directories_obey_invariant_at(layer, ptr, pt@));
                    match self.map_frame_aux(layer + 1, dir_addr, entry_base, vaddr, frame, dir_pt) {
                        Ok(rec_res) => {
                            let dir_pt_res: Ghost<PTDir> = ghost(rec_res@.0);
                            let new_regions: Ghost<Set<MemRegion>> = ghost(rec_res@.1);
                            assert(dir_pt_res@.used_regions === dir_pt@.used_regions.union(new_regions@));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] dir_pt@.used_regions.contains(r)));
                            assert(self.inv_at((layer + 1) as nat, dir_addr, dir_pt_res@));
                            assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@))
                                   === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).map_frame(vaddr, frame@));
                            assert(idx == idxg@);
                            assert(idxg@ < pt@.entries.len());
                            let pt_res: Ghost<PTDir> = ghost(
                                PTDir {
                                    region: pt@.region,
                                    entries: pt@.entries.update(idx, Some(dir_pt_res@)),
                                    used_regions: pt@.used_regions.union(new_regions@),
                                });

                            let ptrg: Ghost<usize> = ghost(ptr);
                            assert forall|i: nat| i < self.arch@.num_entries(layer)
                                implies {
                                    let entry = self.view_at(layer, ptr, i, pt_res@);
                                    entry.is_Directory() == (#[trigger] pt_res@.entries.index(i)).is_Some()
                                }
                            by {
                                let byte_addr = (ptrg@ + i * ENTRY_BYTES) as nat;
                                let word_addr = word_index_spec(sub(byte_addr, pt_res@.region.base));
                                // FIXME:
                                assume(word_addr < self.memory.region_view(pt_res@.region).len());
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
                            // FIXME:
                            assume(self.ghost_pt_used_regions_pairwise_disjoint(layer, ptr, pt_res@));

                            assert(self.memory.region_view(pt_res@.region) === old(self).memory.region_view(pt_res@.region));
                            assert forall|i: nat| i < self.arch@.num_entries(layer) implies {
                                let entry = #[trigger] self.view_at(layer, ptr, i, pt_res@);
                                entry.is_Directory() ==> {
                                    &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt_res@.entries[i].get_Some_0())
                                }
                            }
                            by {
                                let entry = #[trigger] self.view_at(layer, ptr, i, pt_res@);
                                let byte_addr = (ptrg@ + i * ENTRY_BYTES) as nat;
                                let word_addr = word_index_spec(sub(byte_addr, pt_res@.region.base));
                                // FIXME:
                                assume(word_addr < self.memory.region_view(pt_res@.region).len());
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

                            assert(self.inv_at(layer, ptr, pt_res@));

                            assert(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@)) by
                            {
                                self.lemma_interp_at_aux_facts(layer, ptr, base, seq![], pt_res@);
                                assert(pt_res@.region === pt@.region);
                                // recursive postcondition:
                                assert(Ok(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@))
                                       === old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).map_frame(vaddr, frame@));
                                assert(self.inv_at(layer, ptr, pt_res@));
                                assert(old(self).inv_at(layer, ptr, pt@));
                                assert(pt_res@.entries[idxg@].is_Some());
                                assert(pt_res@.entries[idxg@].get_Some_0() === dir_pt_res@);

                                assert(forall|i: nat| i < self.arch@.num_entries(layer) && i != idxg@ ==> pt@.entries[i] === pt_res@.entries[i]);

                                assert(self.interp_at(layer, ptr, base, pt_res@).entries[idxg@]
                                       === l1::NodeEntry::Directory(self.interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt_res@)));
                                assert(self.interp_at(layer, ptr, base, pt_res@).entries[idxg@]
                                       === l1::NodeEntry::Directory(old(self).interp_at((layer + 1) as nat, dir_addr, entry_base, dir_pt@).map_frame(vaddr, frame@).get_Ok_0()));


                                assert forall|i: nat|
                                    i < old(self).arch@.num_entries(layer) && i != idxg@
                                    implies
                                        self.interp_at(layer, ptr, base, pt_res@).entries.index(i)
                                        === #[trigger] old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@).get_Ok_0().entries.index(i) by
                                {
                                    assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@).is_Ok());
                                    assert(old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@).get_Ok_0().entries[i] === old(self).interp_at(layer, ptr, base, pt@).entries[i]);
                                    assert(self.interp_at(layer, ptr, base, pt_res@).entries.index(i) === self.interp_at_entry(layer, ptr, base, i, pt_res@));
                                    assert(old(self).interp_at(layer, ptr, base, pt@).entries.index(i) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                                    assume(self.interp_at_entry(layer, ptr, base, i, pt_res@) === old(self).interp_at_entry(layer, ptr, base, i, pt@));
                                };

                                assert(self.interp_at(layer, ptr, base, pt_res@).entries[idxg@] === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@).get_Ok_0().entries[idxg@]);
                                assert_seqs_equal!(self.interp_at(layer, ptr, base, pt_res.view()).entries, old(self).interp_at(layer, ptr, base, pt.view()).map_frame(vaddr, frame.view()).get_Ok_0().entries);
                                assert(self.interp_at(layer, ptr, base, pt_res@).entries === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@).get_Ok_0().entries);
                                assert(Ok(self.interp_at(layer, ptr, base, pt_res@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));
                            };

                            assert(forall|r: MemRegion| !pt@.used_regions.contains(r) ==> self.memory.region_view(r) === old(self).memory.region_view(r));

                            // posts
                            assert(self.memory.regions() === old(self).memory.regions().union(new_regions@));
                            assert(pt_res@.used_regions === pt@.used_regions.union(new_regions@));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)));
                            assert(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));

                            let res: Ghost<(PTDir,Set<MemRegion>)> = ghost((pt_res@,new_regions@));
                            Ok(res)
                        },
                        Err(e) => {
                            assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));
                            Err(e)
                        },
                    }
                }
            } else {
                assert(Err(self.interp_at(layer, ptr, base, pt@)) === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));
                Err(())
            }
        } else {
            if self.arch.entry_size(layer) == frame.size {
                proof {
                    let frame_base = frame.base as u64;
                    // FIXME: this should be derivable from alignment property in accepted_mapping
                    assume(addr_is_zero_padded(layer, frame_base, true));
                }
                let new_page_entry = PageDirectoryEntry::new_page_entry(layer, frame.base as u64);
                assume(ptr < 100);
                // TODO: this assertion goes through "by accident" due to lemma_entry_base. Maybe
                // we should rename entry_base and use it for all index calculations?
                assert(aligned((ptr + idx * ENTRY_BYTES) as nat, 8));
                // assume(word_index_spec((ptr + idx * ENTRY_BYTES) as nat) < self.memory@.len());
                let write_addr = ptr + idx * ENTRY_BYTES;
                let word_addr: Ghost<nat> = ghost(word_index_spec(sub(write_addr, pt@.region.base)));
                assume(word_addr@ < self.memory.region_view(pt@.region).len());
                assume(pt@.region.contains(write_addr));
                let pwmem: Ghost<mem::PageTableMemory> = ghost(self.memory);
                self.memory.write(write_addr, ghost(pt@.region), new_page_entry.entry);
                assert(self.memory.region_view(pt@.region) === pwmem@.region_view(pt@.region).update(word_addr@, new_page_entry.entry));

                let ptrg: Ghost<usize> = ghost(ptr);
                assert forall|i: nat| i < self.arch@.num_entries(layer)
                    implies {
                        let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                        entry.is_Directory() == pt@.entries[i].is_Some()
                    }
                by {
                    let byte_addr = (ptrg@ + i * ENTRY_BYTES) as nat;
                    let word_addr = word_index_spec(sub(byte_addr, pt@.region.base));
                    // FIXME:
                    assume(word_addr < self.memory.region_view(pt@.region).len());
                    let entry = self.view_at(layer, ptr, i, pt@);
                    if i == idxg@ {
                        assert(entry === new_page_entry@);
                    } else {
                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                    }
                };
                assert(self.ghost_pt_matches_structure(layer, ptr, pt@));

                assert forall|i: nat| i < self.arch@.num_entries(layer) implies {
                    let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                    entry.is_Directory() ==> {
                        &&& self.inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0())
                    }
                }
                by {
                    let entry = #[trigger] self.view_at(layer, ptr, i, pt@);
                    let byte_addr = (ptrg@ + i * ENTRY_BYTES) as nat;
                    let word_addr = word_index_spec(sub(byte_addr, pt@.region.base));
                    // FIXME:
                    assume(word_addr < self.memory.region_view(pt@.region).len());
                    if i == idxg@ {
                        assert(entry === new_page_entry@);
                        assert(!entry.is_Directory());
                    } else {
                        assert(old(self).directories_obey_invariant_at(layer, ptr, pt@));
                        assert(entry === old(self).view_at(layer, ptr, i, pt@));
                        assert(pt@.entries[i] === pt@.entries[i]);
                        if entry.is_Directory() {
                            assert(old(self).inv_at((layer + 1) as nat, entry.get_Directory_addr(), pt@.entries[i].get_Some_0()));
                            // FIXME: need lemma that re-establishes invariant when only another
                            // entry changed
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

                assert(self.inv_at(layer, ptr, pt@));

                // FIXME: need lemma that shows interp of other (unchanged) entries is equal
                assume(Ok(self.interp_at(layer, ptr, base, pt@))
                       === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));

                // posts
                assert(forall|r: MemRegion| !pt@.used_regions.contains(r) ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                proof {
                    assert_sets_equal!(self.memory.regions(), old(self).memory.regions().union(set![]));
                    assert(self.memory.regions() === old(self).memory.regions().union(set![]));
                    // FIXME: this shouldn't be hard but it is
                    // assert_sets_equal!(pt.view().used_regions, pt.view().used_regions.union(set![]));
                    assume(pt@.used_regions === pt@.used_regions.union(set![]));
                }
                assert(forall|r: MemRegion| set![].contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)));
                assert(forall|r: MemRegion| set![].contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));

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
                assert(aligned((ptr + idx * ENTRY_BYTES) as nat, 8));
                // assume(word_index_spec((ptr + idx * ENTRY_BYTES) as nat) < self.memory@.len());
                assume(pt@.region.contains((ptr + idx * ENTRY_BYTES) as nat));
                let write_addr = ptr + idx * ENTRY_BYTES;
                let word_addr: Ghost<nat> = ghost(word_index_spec(sub(write_addr, pt@.region.base)));
                assume(word_addr@ < self.memory.region_view(pt@.region).len());
                self.memory.write(write_addr, ghost(pt@.region), new_dir_entry.entry);

                // Gerd:
                // Proof sketch:
                // 1. new_dir_ptr is from alloc_page, which has a postcondition that the page is zeroed out
                // 2. Prove that view_at of a 0u64 entry is GhostPageDirectoryEntry::Empty
                // 3. Prove that thus empty_at is true for a page of zeros
                // 4. Also use step 2 to prove inv_at is true for a page of zeros
                assume(self.empty_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));
                assume(self.inv_at((layer + 1) as nat, new_dir_ptr, new_dir_pt@));
                let new_dir_interp: Ghost<l1::Directory> = ghost(self.interp_at((layer + 1) as nat, new_dir_ptr, entry_base, new_dir_pt@));
                assume(new_dir_interp@ === interp@.new_empty_dir(idx));
                assert(new_dir_interp@.inv());
                match self.map_frame_aux(layer + 1, new_dir_ptr, entry_base, vaddr, frame, new_dir_pt) {
                    Ok(rec_res) => {
                        let dir_pt_res: Ghost<PTDir> = ghost(rec_res@.0);
                        let dir_new_regions: Ghost<Set<MemRegion>> = ghost(rec_res@.1);
                        let pt_res: Ghost<PTDir> = ghost(
                            PTDir {
                                region: pt@.region,
                                entries: pt@.entries.update(idx, Some(dir_pt_res@)),
                                used_regions: pt@.used_regions.union(dir_new_regions@),
                            });
                        // FIXME:
                        assume(self.inv_at(layer, ptr, pt_res@));
                        assume(Ok(self.interp_at(layer, ptr, base, pt_res@))
                               === old(self).interp_at(layer, ptr, base, pt@).map_frame(vaddr, frame@));


                        let new_regions: Ghost<Set<MemRegion>> = ghost(dir_new_regions@.insert(new_dir_region@));
                        // posts
                        assume(forall|r: MemRegion| !pt@.used_regions.contains(r) ==> self.memory.region_view(r) === old(self).memory.region_view(r));
                        assume(self.memory.regions() === old(self).memory.regions().union(new_regions@));
                        assume(pt_res@.used_regions === pt@.used_regions.union(new_regions@));
                        assume(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] old(self).memory.regions().contains(r)));
                        assume(forall|r: MemRegion| new_regions@.contains(r) ==> !(#[trigger] pt@.used_regions.contains(r)));
                        Ok(ghost((pt_res@, new_regions@)))
                    },
                    Err(e) => {
                        assert(false); // We always successfully insert into an empty directory
                        Err(e)
                    },
                }
            }
        }
    }

    #[allow(unused_parens)] // https://github.com/secure-foundations/verus/issues/230
    fn map_frame(&mut self, vaddr: usize, frame: MemRegionExec) -> (res: (Result<(),()>))
        requires
            old(self).inv(),
            old(self).memory.inv(),
            old(self).accepted_mapping(0, old(self).memory.cr3_spec().1, 0, vaddr, old(self).memory.cr3_spec().0),
            old(self).interp().accepted_mapping(vaddr, frame@),
            vaddr < MAX_BASE,
    {
        proof { ambient_arith(); }
        let (cr3_region, cr3) = self.memory.cr3();
        match self.map_frame_aux(0, cr3, 0, vaddr, frame, self.ghost_pt) {
            Ok(res) => {
                let pt_res: Ghost<PTDir> = ghost(res@.0);
                let new_regions: Ghost<Set<MemRegion>> = ghost(res@.1);
                self.ghost_pt = pt_res;
                Ok(())
            },
            Err(e) => Err(e),
        }
    }
}

}
