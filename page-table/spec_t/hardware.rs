#![allow(unused_imports)] 
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use seq::*;
#[allow(unused_imports)] use set::*;
use crate::definitions_t::{ PageTableEntry, RWOp, LoadResult, StoreResult, between, aligned };
use crate::spec_t::mem;
use crate::spec_t::mem::{ word_index_spec };
use crate::impl_u::l0;
use crate::impl_u::l2_impl;
use option::{ *, Option::* };

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

// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry>;

/// We axiomatize the page table walker with the implementation's interpretation function.
#[verifier(external_body)]
pub proof fn axiom_page_table_walk_interp()
    ensures
        forall|pt: l2_impl::PageTable| pt.inv() ==> #[trigger] pt.interp().interp().map === interp_pt_mem(pt.memory);

pub open spec fn init(s: HWVariables) -> bool {
    &&& s.tlb.dom() === Set::empty()
    &&& interp_pt_mem(s.pt_mem) === Map::empty()
}

// TODO: we only allow aligned accesses, need to argue in report that that's fine. can think of
// unaligned accesses as two aligned accesses. when we get to concurrency we may have to change
// that.
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
                        &&& s2.mem === s1.mem.update(pmem_idx, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < s1.mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem.index(pmem_idx)
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
