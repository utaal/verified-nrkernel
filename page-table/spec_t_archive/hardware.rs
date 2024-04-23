#![verus::trusted]
// trusted:
// this defines the page table structure as interpreted by the hardware
// and the hardware state machine

use vstd::prelude::*;
use crate::definitions_t::{ PageTableEntry, RWOp, between, aligned, MemRegion, Flags, MAX_BASE,
PAGE_SIZE, MAX_PHYADDR_WIDTH, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
axiom_max_phyaddr_width_facts, bit, bitmask_inc };
use crate::spec_t::mem::{ self, word_index_spec };


verus! {

pub struct HWVariables {
    /// Word-indexed physical memory
    pub mem:    Seq<nat>,
    pub pt_mem: mem::PageTableMemory,
    pub tlb:    Map<nat,PageTableEntry>,
}

#[allow(inconsistent_fields)]
pub enum HWStep {
    ReadWrite { vaddr: nat, paddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    PTMemOp,
    TLBFill  { vaddr: nat, pte: PageTableEntry },
    TLBEvict { vaddr: nat},
}

// FIXME: Including is_variant conditionally to avoid the warning when not building impl. But this
// should disappear completely when I find the time to migrate to the new syntax.
#[cfg_attr(feature = "impl", is_variant)]
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
    /// An `Empty` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
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

// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: u64 ensures MASK_ADDR == MASK_ADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: u64 = bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: u64 ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(30u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L2_PG_ADDR_SPEC: u64 = bitmask_inc!(21u64, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: u64 ensures MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(21u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L3_PG_ADDR_SPEC: u64 = bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: u64 ensures MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC{
    axiom_max_phyaddr_width_facts();
    bitmask_inc!(12u64, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_DIR_ADDR_SPEC: u64 = MASK_ADDR;
#[verifier::when_used_as_spec(MASK_DIR_ADDR_SPEC)]
pub exec const MASK_DIR_ADDR: u64 ensures MASK_DIR_ADDR == MASK_DIR_ADDR_SPEC {
    MASK_ADDR
}


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
        let v = self.entry;
        let flag_P   = v & MASK_FLAG_P   == MASK_FLAG_P;
        let flag_RW  = v & MASK_FLAG_RW  == MASK_FLAG_RW;
        let flag_US  = v & MASK_FLAG_US  == MASK_FLAG_US;
        let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
        let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
        let flag_A   = v & MASK_FLAG_A   == MASK_FLAG_A;
        let flag_XD  = v & MASK_FLAG_XD  == MASK_FLAG_XD;
        let flag_D   = v & MASK_PG_FLAG_D   == MASK_PG_FLAG_D;
        let flag_G   = v & MASK_PG_FLAG_G   == MASK_PG_FLAG_G;
        if self.layer@ <= 3 {
            if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
                if self.layer == 0 {
                    let addr = (v & MASK_ADDR) as usize;
                    GhostPageDirectoryEntry::Directory {
                        addr, flag_P, flag_RW, flag_US, flag_PWT, flag_PCD, flag_A, flag_XD,
                    }
                } else if self.layer == 1 {
                    if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                        // super page mapping
                        let addr = (v & MASK_L1_PG_ADDR) as usize;
                        let flag_PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
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
                } else if self.layer == 2 {
                    if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                        // huge page mapping
                        let addr = (v & MASK_L2_PG_ADDR) as usize;
                        let flag_PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
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
                    // TODO: uncomment when we have inline proofs
                    // assert(self.layer == 3);
                    let addr = (v & MASK_L3_PG_ADDR) as usize;
                    let flag_PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                    GhostPageDirectoryEntry::Page {
                        addr,
                        flag_P, flag_RW, flag_US, flag_PWT, flag_PCD,
                        flag_A, flag_D, flag_G, flag_PAT, flag_XD,
                    }
                }
            } else {
                GhostPageDirectoryEntry::Empty
            }
        } else {
            arbitrary()
        }
    }

    /// Returns `true` iff all must-be-zero bits for a given entry are zero.
    #[verifier::opaque]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool
        recommends self.layer@ <= 3,
    {
        if self.entry & MASK_FLAG_P == MASK_FLAG_P {
            if self.layer == 0 { // PML4, always directory
                // 51:M, 7
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                &&& self.entry & bit!(7u64) == 0
            } else if self.layer == 1 { // PDPT
                if self.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // 51:M, 29:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bitmask_inc!(13u64,29u64) == 0
                } else {
                    // 51:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                    &&& self.entry & bit!(7u64) == 0
                }
            } else if self.layer == 2 { // PD
                if self.entry & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // 62:M, 20:13
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bitmask_inc!(13u64,20u64) == 0
                } else {
                    // 62:M, 7
                    &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                    &&& self.entry & bit!(7u64) == 0
                }
            } else if self.layer == 3 { // PT, always frame
                // 62:M
                self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
            } else {
                arbitrary()
            }
        } else {
            // No bits are reserved for unused entries
            true
        }
    }

    pub open spec fn layer(self) -> nat {
        self.layer@
    }
}

#[allow(unused_macros)]
macro_rules! l0_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(39u64,47u64)) >> 39u64 }
}
pub(crate) use l0_bits;

#[allow(unused_macros)]
macro_rules! l1_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(30u64,38u64)) >> 30u64 }
}
pub(crate) use l1_bits;

#[allow(unused_macros)]
macro_rules! l2_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(21u64,29u64)) >> 21u64 }
}
pub(crate) use l2_bits;

#[allow(unused_macros)]
macro_rules! l3_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(12u64,20u64)) >> 12u64 }
}
pub(crate) use l3_bits;

pub open spec fn read_entry(pt_mem: mem::PageTableMemory, dir_addr: nat, layer: nat, idx: nat) -> GhostPageDirectoryEntry {
    let region = MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat };
    PageDirectoryEntry { entry: pt_mem.spec_read(idx, region), layer: Ghost(layer) }@
}


/// TODO: list 4-level paging no HLAT etc. as assumptions (+ the register to enable XD semantics,
/// it's must-be-zero otherwise)
///
/// The intended semantics for valid_pt_walk is this:
/// Given a `PageTableMemory` `pt_mem`, the predicate is true for those `addr` and `pte` where the
/// MMU's page table walk arrives at an entry mapping the frame `pte.frame`. The properties in
/// `pte.flags` reflect the properties along the translation path. I.e. `pte.flags.is_writable` is
/// true iff the RW flag is set in all directories along the translation path and in the frame
/// mapping. Similarly, `pte.flags.is_supervisor` is true iff the US flag is unset in all those
/// structures and `pte.flags.disable_execute` is true iff the XD flag is set in at least one of
/// those structures.
///
/// In practice, we always set these flags to their more permissive state in directories and only
/// make more restrictive settings in the frame mappings. (Ensured in the invariant, see conjunct
/// `directories_have_flags` in refinement layers 1 and 2.) But in the hardware model we still
/// define the full, correct semantics to ensure the implementation sets the flags correctly.
pub open spec fn valid_pt_walk(pt_mem: mem::PageTableMemory, addr: u64, pte: PageTableEntry) -> bool {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    let l3_idx: nat = l3_bits!(addr) as nat;
    match read_entry(pt_mem, pt_mem.cr3_spec()@.base, 0, l0_idx) {
        GhostPageDirectoryEntry::Directory {
            addr: dir_addr, flag_RW: l0_RW, flag_US: l0_US, flag_XD: l0_XD, ..
        } => {
            match read_entry(pt_mem, dir_addr as nat, 1, l1_idx) {
                GhostPageDirectoryEntry::Page {
                    addr: page_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                } => {
                    aligned(addr as nat, L1_ENTRY_SIZE as nat) &&
                    pte == PageTableEntry {
                        frame: MemRegion { base: page_addr as nat, size: L1_ENTRY_SIZE as nat },
                        flags: Flags {
                            is_writable:      l0_RW &&  l1_RW,
                            is_supervisor:   !l0_US || !l1_US,
                            disable_execute:  l0_XD ||  l1_XD
                        }
                    }
                },
                GhostPageDirectoryEntry::Directory {
                    addr: dir_addr, flag_RW: l1_RW, flag_US: l1_US, flag_XD: l1_XD, ..
                } => {
                    match read_entry(pt_mem, dir_addr as nat, 2, l2_idx) {
                        GhostPageDirectoryEntry::Page {
                            addr: page_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                        } => {
                            aligned(addr as nat, L2_ENTRY_SIZE as nat) &&
                            pte == PageTableEntry {
                                frame: MemRegion { base: page_addr as nat, size: L2_ENTRY_SIZE as nat },
                                flags: Flags {
                                    is_writable:      l0_RW &&  l1_RW &&  l2_RW,
                                    is_supervisor:   !l0_US || !l1_US || !l2_US,
                                    disable_execute:  l0_XD ||  l1_XD ||  l2_XD
                                }
                            }
                        },
                        GhostPageDirectoryEntry::Directory {
                            addr: dir_addr, flag_RW: l2_RW, flag_US: l2_US, flag_XD: l2_XD, ..
                        } => {
                            match read_entry(pt_mem, dir_addr as nat, 3, l3_idx) {
                                GhostPageDirectoryEntry::Page {
                                    addr: page_addr, flag_RW: l3_RW, flag_US: l3_US, flag_XD: l3_XD, ..
                                } => {
                                    aligned(addr as nat, L3_ENTRY_SIZE as nat) &&
                                    pte == PageTableEntry {
                                        frame: MemRegion { base: page_addr as nat, size: L3_ENTRY_SIZE as nat },
                                        flags: Flags {
                                            is_writable:      l0_RW &&  l1_RW &&  l2_RW &&  l3_RW,
                                            is_supervisor:   !l0_US || !l1_US || !l2_US || !l3_US,
                                            disable_execute:  l0_XD ||  l1_XD ||  l2_XD ||  l3_XD
                                        }
                                    }
                                },
                                GhostPageDirectoryEntry::Directory { .. } => false,
                                GhostPageDirectoryEntry::Empty => false,
                            }
                        },
                        GhostPageDirectoryEntry::Empty => false,
                    }
                },
                GhostPageDirectoryEntry::Empty => false,
            }
        },
        _ => false,
    }
}

// Can't use `n as u64` in triggers because it's an arithmetic expression
pub open spec fn nat_to_u64(n: nat) -> u64
    recommends n <= u64::MAX
{ n as u64 }

/// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry> {
    Map::new(
        |addr: nat|
            addr < MAX_BASE
            // Casting addr to u64 is okay since addr < MAX_BASE < u64::MAX
            && exists|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte),
        |addr: nat|
            choose|pte: PageTableEntry| valid_pt_walk(pt_mem, nat_to_u64(addr), pte))
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
                        &&& result is Ok
                        &&& s2.mem === s1.mem.update(pmem_idx as int, new_value)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem[pmem_idx as int]
                    } else {
                        &&& result is Pagefault
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
                RWOp::Store { new_value, result } => result is Pagefault,
                RWOp::Load  { is_exec, result }   => result is Pagefault,
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

// pub closed spec fn inv(s: HWVariables) -> bool {
//     true
// }
// 
// proof fn init_implies_inv(s: HWVariables)
//     requires
//         init(s),
//     ensures
//         inv(s)
// { }
// 
// proof fn next_preserves_inv(s1: HWVariables, s2: HWVariables)
//     requires
//         next(s1, s2),
//         inv(s1),
//     ensures
//         inv(s2),
// {
//     let step = choose|step: HWStep| next_step(s1, s2, step);
//     match step {
//         HWStep::ReadWrite { vaddr, paddr, op , pte} => (),
//         HWStep::PTMemOp                             => (),
//         HWStep::TLBFill  { vaddr, pte }             => (),
//         HWStep::TLBEvict { vaddr }                  => (),
//     }
// }

}
