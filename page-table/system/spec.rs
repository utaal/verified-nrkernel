#![allow(unused_imports)] 
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use seq::*;
#[allow(unused_imports)] use set::*;
use crate::aux_defs::{ PageTableEntry, IoOp, LoadResult, StoreResult, between, aligned };
use crate::mem::{ self, word_index_spec };
use crate::pt_impl::l0;
use option::{ *, Option::* };

// state:
// - memory
// - pt memory
// - tlb
// transitions:
// - mem read/write
// - pt mem op
// - resolve --> this will be introduced in the composition state machine
// - tlb evict, tlb fill

verus! {

// TODO: is it correct that the tlb stores full page translations? i.e. we always only need to
// invalidate a single entry?

pub struct SystemVariables {
    /// Word-indexed physical memory
    pub mem:    Seq<nat>,
    pub pt_mem: mem::PageTableMemory,
    pub tlb:    Map<nat,PageTableEntry>,
}

#[is_variant]
pub enum SystemStep {
    IoOp { vaddr: nat, paddr: nat, op: IoOp, pte: Option<(nat, PageTableEntry)> },
    PTMemOp,
    TLBFill { base: nat, pte: PageTableEntry },
    TLBEvict { base: nat},
}

// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry>;

pub open spec fn init(s: SystemVariables) -> bool {
    &&& s.tlb.dom() === Set::empty()
    &&& interp_pt_mem(s.pt_mem) === Map::empty()
}

// TODO: we only allow aligned accesses, need to argue in report that that's fine. can think of
// unaligned accesses as two aligned accesses. when we get to concurrency we may have to change
// that.
pub open spec fn step_IoOp(s1: SystemVariables, s2: SystemVariables, vaddr: nat, paddr: nat, op: IoOp, pte: Option<(nat, PageTableEntry)>) -> bool {
    &&& aligned(vaddr, 8)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.tlb === s1.tlb
    &&& match pte {
        Some((base, pte)) => {
            let mem_idx = word_index_spec(paddr);
            // If pte is Some, it's a cached mapping that maps vaddr to paddr..
            &&& s1.tlb.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& paddr === (pte.frame.base + (vaddr - base)) as nat
            // .. and the result depends on the flags.
            &&& match op {
                IoOp::Store { new_value, result } => {
                    if !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result.is_Ok()
                        &&& s2.mem === s1.mem.update(mem_idx, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                IoOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem.index(mem_idx)
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
                IoOp::Store { new_value, result } => result.is_Pagefault(),
                IoOp::Load  { is_exec, result }   => result.is_Pagefault(),
            }
        },
    }
}

pub open spec fn step_PTMemOp(s1: SystemVariables, s2: SystemVariables) -> bool {
    &&& s2.mem === s1.mem
    // s2.tlb is a submap of s1.tlb
    &&& forall|base: nat, pte: PageTableEntry| s2.tlb.contains_pair(base, pte) ==> s1.tlb.contains_pair(base, pte)
    // pt_mem may change arbitrarily
}

pub open spec fn step_TLBFill(s1: SystemVariables, s2: SystemVariables, base: nat, pte: PageTableEntry) -> bool {
    &&& interp_pt_mem(s1.pt_mem).contains_pair(base, pte)
    &&& s2.tlb === s1.tlb.insert(base, pte)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn step_TLBEvict(s1: SystemVariables, s2: SystemVariables, base: nat) -> bool {
    &&& s1.tlb.dom().contains(base)
    &&& s2.tlb === s1.tlb.remove(base)
    &&& s2.pt_mem === s1.pt_mem
    &&& s2.mem === s1.mem
}

pub open spec fn next_step(s1: SystemVariables, s2: SystemVariables, step: SystemStep) -> bool {
    match step {
        SystemStep::IoOp { vaddr, paddr, op, pte } => step_IoOp(s1, s2, vaddr, paddr, op, pte),
        SystemStep::PTMemOp => step_PTMemOp(s1, s2),
        SystemStep::TLBFill { base, pte } => step_TLBFill(s1, s2, base, pte),
        SystemStep::TLBEvict { base } => step_TLBEvict(s1, s2, base),
    }
}

pub open spec fn next(s1: SystemVariables, s2: SystemVariables) -> bool {
    exists|step: SystemStep| next_step(s1, s2, step)
}

pub closed spec fn inv(s: SystemVariables) -> bool {
    true
}

proof fn init_implies_inv(s: SystemVariables)
    requires
        init(s),
    ensures
        inv(s)
{ }

proof fn next_preserves_inv(s1: SystemVariables, s2: SystemVariables)
    requires
        next(s1, s2),
        inv(s1),
    ensures
        inv(s2),
{
    let step = choose|step: SystemStep| next_step(s1, s2, step);
    match step {
        SystemStep::IoOp { vaddr, paddr, op , pte} => (),
        SystemStep::PTMemOp => (),
        SystemStep::TLBFill { base, pte } => (),
        SystemStep::TLBEvict { base } => (),
    }
}

}
