#![allow(unused_imports)]
use crate::pervasive::*;
use seq::*;
use set::*;
use crate::*;
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;
use map::*;
use crate::definitions_t::{ between, overlap, MemRegion, PageTableEntry, Flags, RWOp, LoadResult, StoreResult, MapResult, UnmapResult, ResolveResult, aligned, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
use crate::definitions_t::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use option::{ *, Option::None, Option::Some };
use crate::spec_t::mem::{ word_index_spec };

// TODO:
// - should Unmap be able to unmap when is_supervisor is set?

verus! {

pub struct AbstractConstants {
    pub phys_mem_size: nat,
}

pub struct AbstractVariables {
    /// Word-indexed virtual memory
    pub mem: Map<nat,nat>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat,PageTableEntry>,
}

pub enum AbstractStep {
    ReadWrite { vaddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    Map       { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap     { vaddr: nat, result: UnmapResult },
    Resolve   { vaddr: nat, result: ResolveResult },
    Stutter,
}

pub open spec fn init(s: AbstractVariables) -> bool {
    &&& s.mem === Map::empty()
    &&& s.mappings === Map::empty()
}

pub open spec fn mem_domain_from_mappings_contains(phys_mem_size: nat, word_idx: nat, mappings: Map<nat, PageTableEntry>) -> bool {
    let vaddr = word_idx * WORD_SIZE as nat;
    exists|base: nat, pte: PageTableEntry| {
        let paddr = (pte.frame.base + (vaddr - base)) as nat;
        let pmem_idx = word_index_spec(paddr);
        &&& #[trigger] mappings.contains_pair(base, pte)
        &&& between(vaddr, base, base + pte.frame.size)
        &&& pmem_idx < phys_mem_size
    }
}

pub open spec fn mem_domain_from_mappings(phys_mem_size: nat, mappings: Map<nat, PageTableEntry>) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub proof fn lemma_mem_domain_from_mappings(phys_mem_size: nat, mappings: Map<nat, PageTableEntry>, base: nat, pte: PageTableEntry)
    requires
        !mappings.dom().contains(base)
    ensures
        (forall|word_idx: nat|
            mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
            ==> #[trigger] mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings.insert(base, pte))),
        (forall|word_idx: nat|
            !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
            && #[trigger] mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings.insert(base, pte))
            ==> between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size)),
{
    assert forall|word_idx: nat|
        mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
        implies #[trigger] mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings.insert(base, pte)) by
    {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base: nat, pte: PageTableEntry| {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            &&& #[trigger] mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& pmem_idx < phys_mem_size
        };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
    };
    assert forall|word_idx: nat|
        !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
        && #[trigger] mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings.insert(base, pte))
        implies between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size) by
    {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base2: nat, pte2: PageTableEntry| {
            let paddr = (pte2.frame.base + (vaddr - base2)) as nat;
            let pmem_idx = word_index_spec(paddr);
            &&& #[trigger] mappings.insert(base, pte).contains_pair(base2, pte2)
            &&& between(vaddr, base2, base2 + pte2.frame.size)
            &&& pmem_idx < phys_mem_size
        };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
        assert(between(vaddr, base2, base2 + pte2.frame.size));
        if !between(vaddr, base, base + pte.frame.size) {
            assert(base2 != base || pte2 !== pte);
            if base2 != base {
                assert(mappings.contains_pair(base2, pte2));
                assert(mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings));
            }
            assert(false);
        } else {
        }
    };
}

pub open spec fn step_ReadWrite(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)>) -> bool {
    let vmem_idx = word_index_spec(vaddr);
    &&& aligned(vaddr, 8)
    &&& s2.mappings === s1.mappings
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            // .. and the result depends on the flags.
            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result.is_Ok()
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value)
                    } else {
                        &&& result.is_Pagefault()
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load  { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result.is_Value()
                        &&& result.get_Value_0() == s1.mem.index(vmem_idx)
                    } else {
                        &&& result.is_Pagefault()
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result.is_Pagefault(),
                RWOp::Load  { is_exec, result }   => result.is_Pagefault(),
            }
        },
    }
}

pub open spec fn step_Map_enabled(map: Map<nat,PageTableEntry>, vaddr: nat, pte: PageTableEntry) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& { // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(map, vaddr, pte)
}

pub open spec fn step_Map(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& step_Map_enabled(s1.mappings, vaddr, pte)
    &&& if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
        &&& result.is_ErrOverlap()
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    } else {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.insert(vaddr, pte)
        &&& (forall|idx:nat| #![auto] s1.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE)
        ||| aligned(vaddr, L2_ENTRY_SIZE)
        ||| aligned(vaddr, L1_ENTRY_SIZE)
    }
}

pub open spec fn step_Unmap(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, result: UnmapResult) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& if s1.mappings.dom().contains(vaddr) {
        &&& result.is_Ok()
        &&& s2.mappings === s1.mappings.remove(vaddr)
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
        &&& (forall|idx:nat| #![auto] s2.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
    } else {
        &&& result.is_ErrNoSuchMapping()
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
}

pub open spec fn step_Resolve(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables, vaddr: nat, result: ResolveResult) -> bool {
    &&& step_Resolve_enabled(vaddr)
    &&& s2 === s1
    &&& match result {
        ResolveResult::Ok(base, pte) => {
            // If result is Ok, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
        },
        ResolveResult::ErrUnmapped => {
            let vmem_idx = word_index_spec(vaddr);
            // If result is ErrUnmapped, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
        },
    }
}


pub open spec fn step_Stutter(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables) -> bool {
    s1 === s2
}

pub open spec fn next_step(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables, step: AbstractStep) -> bool {
    match step {
        AbstractStep::ReadWrite { vaddr, op, pte }     => step_ReadWrite(c, s1, s2, vaddr, op, pte),
        AbstractStep::Map       { vaddr, pte, result } => step_Map(c, s1, s2, vaddr, pte, result),
        AbstractStep::Unmap     { vaddr, result }      => step_Unmap(c, s1, s2, vaddr, result),
        AbstractStep::Resolve   { vaddr, result }      => step_Resolve(c, s1, s2, vaddr, result),
        AbstractStep::Stutter                          => step_Stutter(c, s1, s2),
    }
}

pub open spec fn next(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(c, s1, s2, step)
}

}
