#![allow(unused_imports)]
use crate::pervasive::*;
use seq::*;
use crate::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use crate::aux_defs::{ between, overlap, MemRegion, PageTableEntry, Flags, IoOp, LoadResult, StoreResult, MapResult, UnmapResult, aligned, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_mapping };
use crate::aux_defs::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use option::*;

// TODO:
// - should Map be able to set is_supervisor?

verus! {

pub struct AbstractVariables {
    /// Word-indexed virtual memory
    pub mem: Map<nat,nat>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the preconditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat,PageTableEntry>
}

pub enum AbstractStep {
    IoOp  { vaddr: nat, op: IoOp, pte: Option<(nat, PageTableEntry)> },
    Map   { base: nat, pte: PageTableEntry, result: MapResult },
    Unmap { base: nat, result: UnmapResult },
    Stutter,
    // Resolve { vaddr: nat }, // How do we specify this?
    // TODO:
    // Need to add resolve. I think if I'm careful in how I connect the hardware spec to the
    // high-level spec (i.e. when defining the abstraction function), I should be able to guarantee
    // that the mappings in the high-level spec are the correct ones, i.e. the ones that are
    // actually used in the system spec, which would make the spec of the resolve function here
    // meaningful.
}

// Unaligned accesses are a bit funky with this index function and the word sequences but unaligned
// accesses can be thought of as two aligned accesses so it's probably fine at least until we
// consider concurrency.
pub open spec fn word_index(idx: nat) -> nat {
    idx / 8
}

pub open spec fn init(s: AbstractVariables) -> bool {
    s.mem === Map::empty() // TODO: maybe change this
}

// TODO: also use this in system spec
/// Returns `true` if m contains a mapping for `base` and `vaddr` is within the range of that mapping
pub open spec fn mapping_contains(m: Map<nat, PageTableEntry>, base: nat, vaddr: nat) -> bool {
    m.dom().contains(base) && base <= vaddr && vaddr < base + m.index(base).frame.size
}

pub open spec fn step_IoOp(s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, op: IoOp, pte: Option<(nat, PageTableEntry)>) -> bool {
    let mem_idx = word_index(vaddr);
    let mem_val = s1.mem.index(mem_idx);
    &&& s2.mappings === s1.mappings
    // FIXME:
    // &&& pte.is_Some() === mem_domain_from_mappings(s1.mappings).contains(mem_idx)
    &&& match pte {
        Option::Some((base, pte)) => {
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& match op {
                IoOp::Store { new_value, result } => {
                    if !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& s2.mem === s1.mem.insert(mem_idx, new_value)
                        &&& result.is_Ok()
                    } else {
                        &&& s2.mem === s1.mem
                        &&& result.is_Pagefault()
                    }
                }
                IoOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == mem_val
                    } else {
                        &&& result.is_Pagefault()
                    }
                },
            }
        },
        Option::None => {
            // FIXME: this needs to ensure no suitable mapping exists
            match op {
                IoOp::Store { new_value, result: StoreResult::Pagefault } => s2.mem === s1.mem,
                IoOp::Load  { is_exec,   result: LoadResult::Pagefault }  => s2.mem === s1.mem,
                _                                                         => false,
            }
        },

    }
}

pub open spec fn step_Map_preconditions(base: nat, pte: PageTableEntry) -> bool {
    &&& aligned(base, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    // FIXME: We don't have an upper bound on the physical addresses we can map. If a physical
    // address outside the actual physical address space is mapped and then accessed, the spec just
    // treats it like a valid memory access but in practice we'd get a fault.
    // &&& pte.frame.base + pte.frame.size <= c.phys_addr_space_size
    &&& candidate_mapping_in_bounds(base, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
}

pub open spec fn step_Map(s1: AbstractVariables, s2: AbstractVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& step_Map_preconditions(base, pte)
    &&& if candidate_mapping_overlaps_existing_mapping(s1.mappings, base, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    } else {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.insert(base, pte)
        &&& { // Contents of the newly mapped memory are arbitrary
            let mem_idx = word_index(base);
            let num_words = pte.frame.size / WORD_SIZE;
            &&& (forall|idx| #![auto] s1.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
            // FIXME:
            // &&& mem_domain_from_mappings(s2.mappings) === s2.mem.dom()
            // &&& s2.mem.dom() === s1.mem.dom().union(...)
            // &&& forall|vaddr, base, pte|
            //         s1.mappings.contains_pair(base, pte) && pte.frame.contains(vaddr)
            //         ==> s2.mem[word_index(vaddr)] == s1.mem[word_index(vaddr)]
            // &&& s2.mem.len() == s1.mem.len()
            // &&& (forall|i: nat| #![auto]
            //      i < s2.mem.len() && !between(i, mem_idx, mem_idx + num_words)
            //      ==> { s2.mem[i] == s1.mem[i] })
        }
    }
}

pub open spec fn step_Unmap_preconditions(base: nat) -> bool {
    &&& between(base, PT_BOUND_LOW, PT_BOUND_HIGH)
    &&& { // The given base must be aligned to some valid page size
        ||| aligned(base, L3_ENTRY_SIZE)
        ||| aligned(base, L2_ENTRY_SIZE)
        ||| aligned(base, L1_ENTRY_SIZE)
    }
}

pub open spec fn step_Unmap(s1: AbstractVariables, s2: AbstractVariables, base: nat, result: UnmapResult) -> bool {
    &&& step_Unmap_preconditions(base)
    &&& if s1.mappings.dom().contains(base) {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.remove(base)
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.mappings === s1.mappings
    }
    &&& s2.mem === s1.mem
}

pub open spec fn step_Stutter(s1: AbstractVariables, s2: AbstractVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(s1: AbstractVariables, s2: AbstractVariables, step: AbstractStep) -> bool {
    match step {
        AbstractStep::IoOp  { vaddr, op, pte }    => step_IoOp(s1, s2, vaddr, op, pte),
        AbstractStep::Map   { base, pte, result } => step_Map(s1, s2, base, pte, result),
        AbstractStep::Unmap { base, result }      => step_Unmap(s1, s2, base, result),
        AbstractStep::Stutter                     => step_Stutter(s1, s2),
    }
}

pub open spec fn next(s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(s1, s2, step)
}

}
