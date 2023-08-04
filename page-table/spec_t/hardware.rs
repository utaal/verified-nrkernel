#![allow(unused_imports)] 
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;
use vstd::set::*;
use crate::definitions_t::{ PageTableEntry, RWOp, LoadResult, StoreResult, between, aligned, MemRegion, x86_arch_spec, Flags, PAGE_SIZE, MAX_BASE };
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

// Duplicate macro because I still don't understand how to import Rust macros
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0u64 << (($high+1u64)-$low))) << $low
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

// Currently ignoring supervisor bits
pub open spec fn pt_walk(pt_mem: mem::PageTableMemory, addr: u64) -> Option<PageTableEntry> {
    let l0_idx: nat = l0_bits!(addr) as nat;
    let l1_idx: nat = l1_bits!(addr) as nat;
    let l2_idx: nat = l2_bits!(addr) as nat;
    let l3_idx: nat = l3_bits!(addr) as nat;
    // TODO: maybe just don't need this and should be recommends instead
    if pt_mem.inv() {
        // TODO: Invariant might need to say that cr3 region is in regions()
        let l0_tbl = pt_mem.region_view(pt_mem.cr3_spec()@);
        let l0_ent = l2_impl::PageDirectoryEntry { entry: l0_tbl[l0_idx as int], layer: Ghost(0) }@;
        match l0_ent {
            l2_impl::GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                let l1_tbl = pt_mem.region_view(MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat });
                let l1_ent = l2_impl::PageDirectoryEntry { entry: l1_tbl[l1_idx as int], layer: Ghost(1) }@;
                match l1_ent {
                    l2_impl::GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                        let l2_tbl = pt_mem.region_view(MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat });
                        let l2_ent = l2_impl::PageDirectoryEntry { entry: l2_tbl[l2_idx as int], layer: Ghost(2) }@;
                        match l2_ent {
                            l2_impl::GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => {
                                let l3_tbl = pt_mem.region_view(MemRegion { base: dir_addr as nat, size: PAGE_SIZE as nat });
                                let l3_ent = l2_impl::PageDirectoryEntry { entry: l3_tbl[l3_idx as int], layer: Ghost(3) }@;
                                match l3_ent {
                                    l2_impl::GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } => None,
                                    l2_impl::GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } =>
                                        Some(PageTableEntry {
                                            frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(3) },
                                            flags: Flags {
                                                is_writable:     flag_RW,
                                                is_supervisor:   !flag_US,
                                                disable_execute: flag_XD,
                                            }
                                        }),
                                    l2_impl::GhostPageDirectoryEntry::Empty => None,
                                }
                            },
                            l2_impl::GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } =>
                                Some(PageTableEntry {
                                    frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(2) },
                                    flags: Flags {
                                        is_writable:     flag_RW,
                                        is_supervisor:   !flag_US,
                                        disable_execute: flag_XD,
                                    }
                                }),
                            l2_impl::GhostPageDirectoryEntry::Empty => None,
                        }
                    },
                    l2_impl::GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } =>
                        Some(PageTableEntry {
                            frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(1) },
                            flags: Flags {
                                is_writable:     flag_RW,
                                is_supervisor:   !flag_US,
                                disable_execute: flag_XD,
                            }
                        }),
                    l2_impl::GhostPageDirectoryEntry::Empty => None,
                }
            },
            // Pages can't be *that* huge.
            // TODO: I think this is already taken care of in the PageDirectoryEntry constructor?
            l2_impl::GhostPageDirectoryEntry::Page { addr, flag_RW, flag_US, flag_XD, .. } => None,
            l2_impl::GhostPageDirectoryEntry::Empty => None,
        }
    } else {
        arbitrary()
    }
}

// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry> {
    if pt_mem.inv() {
        // Domain:
        // - Addresses in the region [0, MAX_BASE)
        // - Must decode to a mapping
        // - The address must be the base address for that mapping
        //   (That's the `aligned` in the Some branch of the match.)
        Map::new(
            |addr: nat|
                0 <= addr && addr < MAX_BASE
                && aligned(addr, PAGE_SIZE as nat)
                // Casting to u64 is okay since MAX_BASE < u64::MAX
                && match pt_walk(pt_mem, addr as u64) {
                        Some(pte) => aligned(addr as nat, pte.frame.size as nat),
                        None => false,
                },
            |addr: nat| match pt_walk(pt_mem, addr as u64) {
                Some(pte) => pte,
                None => arbitrary(),
            })
    } else {
        arbitrary()
    }
}

// // Page table walker interpretation of the page table memory
// pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry>;

pub proof fn lemma_page_table_walk_interp(pt: l2_impl::PageTable)
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
            assert(pt_walk(pt.memory, addr as u64) == Some(pte));
            assert(aligned(addr as nat, pte.frame.size as nat));
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

/// We axiomatize the page table walker with the implementation's interpretation function.
#[verifier(external_body)]
pub proof fn axiom_page_table_walk_interp()
    ensures
        forall|pt: l2_impl::PageTable| pt.inv() ==> #[trigger] pt.interp().interp().map === interp_pt_mem(pt.memory);

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
