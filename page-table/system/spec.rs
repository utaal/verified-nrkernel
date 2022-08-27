#![allow(unused_imports)] 
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use seq::*;
#[allow(unused_imports)] use set::*;
use crate::aux_defs::{ PageTableEntry, IoOp, LoadResult, StoreResult, between };
use crate::mem;
use crate::pt_impl::l0;
use option::*;

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

pub struct SystemVariables {
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

// Unaligned accesses are a bit funky with this index function and the word sequences but unaligned
// accesses can be thought of as two aligned accesses so it's probably fine at least until we
// consider concurrency.
pub open spec fn word_index(idx: nat) -> nat {
    idx / 8
}

// Page table walker interpretation of the page table memory
pub open spec fn interp_pt_mem(pt_mem: mem::PageTableMemory) -> Map<nat, PageTableEntry>;

pub open spec fn init(s: SystemVariables) -> bool {
    s.tlb.dom() === Set::empty()
}

pub open spec fn step_IoOp(s1: SystemVariables, s2: SystemVariables, vaddr: nat, paddr: nat, op: IoOp, pte: Option<(nat, PageTableEntry)>) -> bool {
    match pte {
        Option::Some((base, pte)) => {
            &&& s1.tlb.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& paddr === (pte.frame.base + (vaddr - base)) as nat
            &&& s2.tlb === s1.tlb
            &&& s2.pt_mem === s1.pt_mem
            &&& match op {
                IoOp::Load { is_exec, result: LoadResult::Value(n) }      => {
                    &&& !pte.flags.is_supervisor
                    &&& (is_exec ==> !pte.flags.disable_execute)
                    &&& s2.mem === s1.mem
                    &&& n == s1.mem.index(word_index(paddr))
                },
                IoOp::Store { new_value, result: StoreResult::Ok }        => {
                    &&& !pte.flags.is_supervisor
                    &&& pte.flags.is_writable
                    &&& s2.mem === s1.mem.update(word_index(paddr), new_value)
                }
                IoOp::Store { new_value, result: StoreResult::PageFault } => {
                    &&& s2.mem === s1.mem
                    &&& {
                        ||| pte.flags.is_supervisor
                        ||| !pte.flags.is_writable
                    }
                }
                IoOp::Load { is_exec, result: LoadResult::PageFault }     => {
                    &&& s2.mem === s1.mem
                    &&& {
                        ||| pte.flags.is_supervisor
                        ||| (is_exec && pte.flags.disable_execute)
                    }
                },
            }
        },
        Option::None => {
            &&& s2.tlb === s1.tlb
            &&& s2.pt_mem === s1.pt_mem
            &&& s2.mem === s1.mem
            &&& match op {
                IoOp::Store { new_value, result: StoreResult::PageFault } => true,
                IoOp::Load { is_exec, result: LoadResult::PageFault }     => true,
                _                                                         => false,
            }
        },
    }
}

pub open spec fn step_PTMemOp(s1: SystemVariables, s2: SystemVariables) -> bool {
    &&& s2.mem === s1.mem
    &&& s2.tlb === s1.tlb
    // only pt_mem may change, but arbitrarily
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
