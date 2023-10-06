#![allow(unused_imports)] 
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;
use vstd::set::*;
use crate::definitions_t::{ PageTableEntry, RWOp, LoadResult, StoreResult, between, aligned, MemRegion, x86_arch_spec, Flags };
use crate::definitions_t::{ MAX_BASE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, X86_NUM_LAYERS, X86_NUM_ENTRIES };
use crate::spec_t::mem;
use crate::spec_t::mem::{ word_index_spec };
use crate::impl_u::l0;
use crate::impl_u::l2_impl;

verus! {

pub struct HWVariables {
    /// Word-indexed physical memory
    pub mem:    Seq<nat>,
    pub pt_mem: mem::PageTableMemory,
    pub tlb:    Map<nat,PageTableEntry>,
}

#[is_variant]
pub enum HWStep {
    ReadWrite { vaddr: nat, paddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    PTMemOp,
    TLBFill  { vaddr: nat, pte: PageTableEntry },
    TLBEvict { vaddr: nat},
}

// Duplicate macros because I still don't understand how to import Rust macros
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0u64 << (($high+1u64)-$low))) << $low
    }
}
macro_rules! bit {
    ($v:expr) => {
        1u64 << $v
    }
}

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


// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table


// MASK_FLAG_* are flags valid for entries at all levels.
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

#[allow(repr_transparent_external_private_fields)]
// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PageDirectoryEntry {
    pub entry: u64,
    pub layer: Ghost<nat>,
}

// This impl defines everything necessary for the page table walk semantics.
// PageDirectoryEntry is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
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

    // pub open spec fn view(self) -> GhostPageDirectoryEntry {
    //     arbitrary()
    //     // let v = self.entry;
    //     // let flag_P   = v & MASK_FLAG_P   == MASK_FLAG_P;
    //     // let flag_RW  = v & MASK_FLAG_RW  == MASK_FLAG_RW;
    //     // let flag_US  = v & MASK_FLAG_US  == MASK_FLAG_US;
    //     // let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
    //     // let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
    //     // let flag_A   = v & MASK_FLAG_A   == MASK_FLAG_A;
    //     // let flag_XD  = v & MASK_FLAG_XD  == MASK_FLAG_XD;
    //     // let flag_D   = v & MASK_PG_FLAG_D   == MASK_PG_FLAG_D;
    //     // let flag_G   = v & MASK_PG_FLAG_G   == MASK_PG_FLAG_G;
    //     // if self.layer == 0 && (v & MASK_FLAG_P == MASK_FLAG_P) {
    //     //     let addr = (v & MASK_ADDR) as usize;
    //     //     GhostPageDirectoryEntry::Directory {
    //     //         addr, flag_P, flag_RW, flag_US, flag_PWT, flag_PCD, flag_A, flag_XD,
    //     //     }
    //     // } else if self.layer == 1 {
    //     // }
    //     // // FIXME: left off here

    //     // if self.layer() <= 3 {
    //     //     if v & MASK_FLAG_P == MASK_FLAG_P { // Is the Present bit set?
    //     //         if (self.layer() == 3) || (v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS) {
    //     //             // This is a page mapping, either because the PS flag is set (huge page) or
    //     //             // because we're in the bottom-most layer.
    //     //             let addr =
    //     //                 if self.layer() == 3 {
    //     //                     (v & MASK_L3_PG_ADDR) as usize
    //     //                 } else if self.layer() == 2 {
    //     //                     (v & MASK_L2_PG_ADDR) as usize
    //     //                 } else {
    //     //                     (v & MASK_L1_PG_ADDR) as usize
    //     //                 };
    //     //             let flag_PAT = if self.layer() == 3 { v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT } else { v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT };
    //     //             GhostPageDirectoryEntry::Page {
    //     //                 addr,
    //     //                 flag_P, flag_RW, flag_US, flag_PWT, flag_PCD,
    //     //                 flag_A, flag_D, flag_G, flag_PAT, flag_XD,
    //     //             }
    //     //         } else {
    //     //             // This mapping is a directory for the next layer.
    //     //             let addr = (v & MASK_ADDR) as usize;
    //     //             GhostPageDirectoryEntry::Directory {
    //     //                 addr, flag_P, flag_RW, flag_US, flag_PWT, flag_PCD, flag_A, flag_XD,
    //     //             }
    //     //         }
    //     //     } else {
    //     //         GhostPageDirectoryEntry::Empty
    //     //     }
    //     // } else {
    //     //     arbitrary()
    //     // }
    // }

    pub open spec fn layer(self) -> nat {
        self.layer@
    }
}

macro_rules! l0_bits {
    ($addr:expr) => { $addr & bitmask_inc!(12u64,21u64) }
}

macro_rules! l1_bits {
    ($addr:expr) => { $addr & bitmask_inc!(21u64,30u64) }
}

macro_rules! l2_bits {
    ($addr:expr) => { $addr & bitmask_inc!(30u64,39u64) }
}

macro_rules! l3_bits {
    ($addr:expr) => { $addr & bitmask_inc!(39u64,48u64) }
}


pub open spec fn read_entry(pt_mem: mem::PageTableMemory, dir_addr: nat, layer: nat, idx: nat) -> GhostPageDirectoryEntry {
    let directory = pt_mem.region_view(MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat });
    PageDirectoryEntry { entry: directory[idx as int], layer: Ghost(layer) }@
}

pub open spec fn valid_pt_walk_maps_normal_page(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    let l3_idx: nat = l3_bits!(addr) as nat;
    aligned(addr as nat, L3_ENTRY_SIZE as nat) &&
    if let GhostPageDirectoryEntry::Directory {
        addr: dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
    } = read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        if let GhostPageDirectoryEntry::Directory {
            addr: dir_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
        } = read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
            if let GhostPageDirectoryEntry::Directory {
                addr: dir_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
            } = read_entry(pt_mem, dir_addr as nat, 2, l2_idx) {
                if let GhostPageDirectoryEntry::Page {
                    addr, flag_RW: l3_RW, flag_US: l3_US, flag_XD: l3_XD, ..
                } = read_entry(pt_mem, dir_addr as nat, 3, l3_idx) {
                    pte == PageTableEntry {
                        frame: MemRegion { base: addr as nat, size: L3_ENTRY_SIZE as nat },
                        flags: Flags {
                            is_writable:      l0_RW &&  l1_RW &&  l2_RW &&  l3_RW,
                            is_supervisor:   !l0_US || !l1_US || !l2_US || !l3_US,
                            disable_execute:  l0_XD ||  l1_XD ||  l2_XD ||  l3_XD
                        }
                    }
                } else { false }
            } else { false }
        } else { false }
    } else { false }
}

pub open spec fn valid_pt_walk_maps_huge_page(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    aligned(addr as nat, L2_ENTRY_SIZE as nat) &&
    if let GhostPageDirectoryEntry::Directory {
        addr: dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
    } = read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        if let GhostPageDirectoryEntry::Directory {
            addr: dir_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
        } = read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
            if let GhostPageDirectoryEntry::Page {
                addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
            } = read_entry(pt_mem, dir_addr as nat, 2, l2_idx) {
                pte == PageTableEntry {
                    frame: MemRegion { base: addr as nat, size: L2_ENTRY_SIZE as nat },
                    flags: Flags {
                        is_writable:      l0_RW &&  l1_RW &&  l2_RW,
                        is_supervisor:   !l0_US || !l1_US || !l2_US,
                        disable_execute:  l0_XD ||  l1_XD ||  l2_XD
                    }
                }
            } else { false }
        } else { false }
    } else { false }
}

pub open spec fn valid_pt_walk_maps_super_page(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    aligned(addr as nat, L1_ENTRY_SIZE as nat) &&
    if let GhostPageDirectoryEntry::Directory {
        addr: dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
    } = read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        if let GhostPageDirectoryEntry::Page {
            addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
        } = read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
            pte == PageTableEntry {
                frame: MemRegion { base: addr as nat, size: L1_ENTRY_SIZE as nat },
                flags: Flags {
                    is_writable:      l0_RW &&  l1_RW,
                    is_supervisor:   !l0_US || !l1_US,
                    disable_execute:  l0_XD ||  l1_XD
                }
            }
        } else { false }
    } else { false }
}

pub proof fn pt_walk_cases_disjoint(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry)
    ensures
        valid_pt_walk_maps_normal_page(pt_mem, addr, pte) ==> !valid_pt_walk_maps_huge_page(pt_mem, addr, pte),
        valid_pt_walk_maps_normal_page(pt_mem, addr, pte) ==> !valid_pt_walk_maps_super_page(pt_mem, addr, pte),
        valid_pt_walk_maps_huge_page(pt_mem, addr, pte)   ==> !valid_pt_walk_maps_normal_page(pt_mem, addr, pte),
        valid_pt_walk_maps_huge_page(pt_mem, addr, pte)   ==> !valid_pt_walk_maps_super_page(pt_mem, addr, pte),
        valid_pt_walk_maps_super_page(pt_mem, addr, pte)  ==> !valid_pt_walk_maps_normal_page(pt_mem, addr, pte),
        valid_pt_walk_maps_super_page(pt_mem, addr, pte)  ==> !valid_pt_walk_maps_huge_page(pt_mem, addr, pte),
{ }



// TODO: list 4-level paging no HLAT etc. as assumptions (+ the register to enable XD semantics)
// The intended semantics for valid_pt_walk is this:
// Given a `PageTableMemory` `pt_mem`, the predicate is true for those `addr` and `pte` where the
// MMU's page table walk arrives at an entry mapping the frame `pte.frame`. The properties in
// `pte.flags` reflect the properties along the translation path. I.e. `pte.flags.is_writable` is
// true iff the RW flag is set in all directories along the translation path and in the frame
// mapping. Similarly, `pte.flags.is_supervisor` is true iff the US flag is unset in all those
// structures and `pte.flags.disable_execute` is true iff the XD flag is set in at least one of
// those structures.
//
// In practice, we always set these flags to their more permissive state in directories and only
// make more restrictive settings in the frame mappings. (Ensured in the invariant, see conjunct
// `directories_have_flags` in refinement layers 1 and 2.) But in the hardware model we still
// define the full, correct semantics to ensure the implementation sets the flags correctly.
pub open spec fn valid_pt_walk(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry) -> bool {
    ||| valid_pt_walk_maps_normal_page(pt_mem, addr, pte)
    ||| valid_pt_walk_maps_huge_page(pt_mem, addr, pte)
    ||| valid_pt_walk_maps_super_page(pt_mem, addr, pte)
}

// FIXME:
// There's a number of bits that are reserved/must-be-zero. Non-zero bits result in a page-fault.
// Need to consider that in pt_walk def.
//
// Also should consider supervisor bits on intermediate entries
//
// Won't have to change the interp function but add conjuncts to the invariant saying that
// 1. supervisor bit on directories is never set
// 2. mb0 bits are unset
// (but changing the pagedirectoryentry view *will* change the interp, still should be easy with
// invariant change)

// Can't use `n as u64` in triggers because it's an arithmetic expression
pub open spec fn nat_to_u64(n: nat) -> u64
    recommends n <= u64::MAX
{ n as u64 }

// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry> {
    Map::new(
        |addr: nat|
            0 <= addr && addr < MAX_BASE
            // Casting addr to u64 is okay since addr < MAX_BASE < u64::MAX
            && exists|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte),
        |addr: nat|
            choose|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte))
}

pub proof fn lemma_page_table_walk_interp()
    ensures
        forall|pt: l2_impl::PageTable| #![auto] pt.inv() ==> pt.interp().interp().map === interp_pt_mem(pt.memory)
{
    assert forall|pt: l2_impl::PageTable| #![auto]
        pt.inv()
        implies
        pt.interp().interp().map === interp_pt_mem(pt.memory) by
    {
        lemma_page_table_walk_interp_aux(pt);
    }
}

pub proof fn lemma_page_table_walk_interp_aux(pt: l2_impl::PageTable)
    requires
        pt.inv()
    ensures
        pt.interp().interp().map === interp_pt_mem(pt.memory)
{
    let m1 = pt.interp().interp().map;
    let m2 = interp_pt_mem(pt.memory);
        assert forall|addr: nat, pte: PageTableEntry|
            m2.contains_pair(addr, pte) implies #[trigger] m1.contains_pair(addr, pte) by
        {
            assert(m2.dom().contains(addr));
            assert(m2[addr] == pte);
            assert(pt.memory.inv());
            assert(0 <= addr && addr < MAX_BASE);
            assert(aligned(addr, PAGE_SIZE as nat));
            // assert(pt_walk(pt.memory, addr as u64) == Some(pte));
            // assert(aligned(addr as nat, pte.frame.size as nat));
            assume(false);
        };
        assert forall|addr: nat, pte: PageTableEntry|
            m1.contains_pair(addr, pte) implies #[trigger] m2.contains_pair(addr, pte) by
        {
            assume(false);
        };
        assert forall|addr: nat| m1.dom().contains(addr) <==> m2.dom().contains(addr) by {
            if m1.dom().contains(addr) {
                assert(m1.contains_pair(addr, m1[addr]));
                assert(m2.contains_pair(addr, m1[addr]));
            }
            if m2.dom().contains(addr) {
                assert(m2.contains_pair(addr, m2[addr]));
                assert(m1.contains_pair(addr, m2[addr]));
            }
        };
        assert forall|addr: nat| #[trigger] m1.dom().contains(addr) && m2.dom().contains(addr) implies m1[addr] == m2[addr] by {
            assert(m1.contains_pair(addr, m1[addr]));
            assert(m2.contains_pair(addr, m1[addr]));
        };
        assert(m1 =~= m2);
}

pub open spec fn init(s: HWVariables) -> bool {
    &&& s.tlb.dom() === Set::empty()
    &&& interp_pt_mem(s.pt_mem) === Map::empty()
}

// We only allow aligned accesses. Can think of unaligned accesses as two aligned accesses. When we
// get to concurrency we may have to change that.
pub open spec fn step_ReadWrite(s1: HWVariables, s2: HWVariables, vaddr: nat, paddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)>) -> bool {
    &&& aligned(vaddr, 8)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.tlb === s1.tlb
    &&& match pte {
        Some((base, pte)) => {
            let pmem_idx = word_index_spec(paddr);
            // If pte is Some, it's a cached mapping that maps vaddr to paddr..
            &&& s1.tlb.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& paddr === (pte.frame.base + (vaddr - base)) as nat
            // .. and the result depends on the flags.
            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result.is_Ok()
                        &&& s2.mem === s1.mem.update(pmem_idx as int, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem[pmem_idx as int]
                    } else {
                        &&& result.is_Pagefault()
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& (!exists|base, pte| {
                 &&& interp_pt_mem(s1.pt_mem).contains_pair(base, pte)
                 &&& between(vaddr, base, base + pte.frame.size)
            })
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result.is_Pagefault(),
                RWOp::Load  { is_exec, result }   => result.is_Pagefault(),
            }
        },
    }
}

pub open spec fn step_PTMemOp(s1: HWVariables, s2: HWVariables) -> bool {
    &&& s2.mem === s1.mem
    // s2.tlb is a submap of s1.tlb
    &&& forall|base: nat, pte: PageTableEntry| s2.tlb.contains_pair(base, pte) ==> s1.tlb.contains_pair(base, pte)
    // pt_mem may change arbitrarily
}

pub open spec fn step_TLBFill(s1: HWVariables, s2: HWVariables, vaddr: nat, pte: PageTableEntry) -> bool {
    &&& interp_pt_mem(s1.pt_mem).contains_pair(vaddr, pte)
    &&& s2.tlb === s1.tlb.insert(vaddr, pte)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn step_TLBEvict(s1: HWVariables, s2: HWVariables, vaddr: nat) -> bool {
    &&& s1.tlb.dom().contains(vaddr)
    &&& s2.tlb === s1.tlb.remove(vaddr)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn next_step(s1: HWVariables, s2: HWVariables, step: HWStep) -> bool {
    match step {
        HWStep::ReadWrite { vaddr, paddr, op, pte } => step_ReadWrite(s1, s2, vaddr, paddr, op, pte),
        HWStep::PTMemOp                             => step_PTMemOp(s1, s2),
        HWStep::TLBFill  { vaddr, pte }             => step_TLBFill(s1, s2, vaddr, pte),
        HWStep::TLBEvict { vaddr }                  => step_TLBEvict(s1, s2, vaddr),
    }
}

pub open spec fn next(s1: HWVariables, s2: HWVariables) -> bool {
    exists|step: HWStep| next_step(s1, s2, step)
}

pub closed spec fn inv(s: HWVariables) -> bool {
    true
}

proof fn init_implies_inv(s: HWVariables)
    requires
        init(s),
    ensures
        inv(s)
{ }

proof fn next_preserves_inv(s1: HWVariables, s2: HWVariables)
    requires
        next(s1, s2),
        inv(s1),
    ensures
        inv(s2),
{
    let step = choose|step: HWStep| next_step(s1, s2, step);
    match step {
        HWStep::ReadWrite { vaddr, paddr, op , pte} => (),
        HWStep::PTMemOp                             => (),
        HWStep::TLBFill  { vaddr, pte }             => (),
        HWStep::TLBEvict { vaddr }                  => (),
    }
}

}
