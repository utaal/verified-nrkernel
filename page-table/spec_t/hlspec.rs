#![verus::trusted]
// trusted:
// this is the process-level specification of the kernel's behaviour

use crate::definitions_t::{
    aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, PageTableEntry, RWOp, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
    L3_ENTRY_SIZE, MAX_PHYADDR, PT_BOUND_HIGH, PT_BOUND_LOW, WORD_SIZE,
};
//use crate::spec_t::hlspec::AbstractArguments::{Empty};
use crate::spec_t::mem;
use vstd::prelude::*;

verus! {

pub struct AbstractConstants {
    //so far const
    pub thread_no: nat,
    pub phys_mem_size: nat,
}

pub struct AbstractVariables {
    /// Word-indexed virtual memory
    pub mem: Map<nat, nat>,
    pub thread_state: Map<nat, AbstractArguments>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat, PageTableEntry>,
}

#[allow(inconsistent_fields)]
pub enum AbstractStep {
    ReadWrite          { thread_id: nat, vaddr: nat, op: RWOp, pte: Option<(nat, PageTableEntry)> },
    MapStart           { thread_id: nat, vaddr: nat, pte: PageTableEntry },
    MapEnd             { thread_id: nat, result: Result<(), ()> },
    UnmapStart         { thread_id: nat, vaddr: nat },
    UnmapEnd           { thread_id: nat, result: Result<(), ()> },
    ResolveStart       { thread_id: nat, vaddr: nat },
    ResolveEnd         { thread_id: nat, result: Result<(nat, PageTableEntry), ()> },
    Stutter,
}

//To allow two-step transitions that preserve arguments
#[allow(inconsistent_fields)]
pub enum AbstractArguments {
    Map           { vaddr: nat, pte: PageTableEntry },
    Unmap         { vaddr: nat },
    Resolve       { vaddr: nat },
    Empty,
}

pub open spec fn wf(c: AbstractConstants, s:AbstractVariables) -> bool {
    &&& forall |id: nat| id <= c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mem.dom().finite()
}

pub open spec fn init(c: AbstractConstants, s: AbstractVariables) -> bool {
    &&& s.mem === Map::empty()
    &&& s.mappings === Map::empty()
    &&& forall |id: nat| id <= c.thread_no ==> (s.thread_state[id] === AbstractArguments::Empty)
    &&& wf(c, s)
}

pub open spec fn mem_domain_from_mappings_contains(
    phys_mem_size: nat,
    word_idx: nat,
    mappings: Map<nat, PageTableEntry>,
) -> bool {
    let vaddr = word_idx * WORD_SIZE as nat;
    exists|base: nat, pte: PageTableEntry|
        {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            &&& #[trigger] mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            &&& pmem_idx < phys_mem_size
        }
}

pub open spec fn mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub proof fn lemma_mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry,
)
    requires
        !mappings.dom().contains(base),
    ensures
        (forall|word_idx: nat|
            mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                ==> #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            )),
        (forall|word_idx: nat|
            !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
                && #[trigger] mem_domain_from_mappings_contains(
                phys_mem_size,
                word_idx,
                mappings.insert(base, pte),
            ) ==> between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size)),
{
    assert forall|word_idx: nat|
        mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings,
        ) implies #[trigger] mem_domain_from_mappings_contains(
        phys_mem_size,
        word_idx,
        mappings.insert(base, pte),
    ) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base: nat, pte: PageTableEntry|
            {
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
                &&& #[trigger] mappings.contains_pair(base, pte)
                &&& between(vaddr, base, base + pte.frame.size)
                &&& pmem_idx < phys_mem_size
            };
        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
    };
    assert forall|word_idx: nat|
        !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
            && #[trigger] mem_domain_from_mappings_contains(
            phys_mem_size,
            word_idx,
            mappings.insert(base, pte),
        ) implies between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size) by {
        let vaddr = word_idx * WORD_SIZE as nat;
        let (base2, pte2) = choose|base2: nat, pte2: PageTableEntry|
            {
                let paddr = (pte2.frame.base + (vaddr - base2)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
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

pub open spec fn valid_thread(c: AbstractConstants, thread_id: nat) -> bool {
    thread_id <= c.thread_no
}

pub open spec fn state_unchanged_besides_thread_state(
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    thread_arguments: AbstractArguments,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings
}


pub open spec fn step_ReadWrite(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
    op: RWOp,
    pte: Option<(nat, PageTableEntry)>,
) -> bool {
    let vmem_idx = mem::word_index_spec(vaddr);
    &&& aligned(vaddr, 8)
    &&& s2.mappings === s1.mappings  
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === AbstractArguments::Empty
    &&& s2.thread_state === s1.thread_state
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(
                vaddr,
                base,
                base + pte.frame.size,
            )
            // .. and the result depends on the flags.
            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value)
                    } else {
                        &&& result is Undefined
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec
                        ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.index(vmem_idx)
                    } else {
                        &&& result is Undefined
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(
                vmem_idx,
            )
            // .. and the result is always a Undefined and an unchanged memory.

            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result is Undefined,
                RWOp::Load { is_exec, result } => result is Undefined,
            }
        },
    }
}

pub open spec fn step_Map_enabled(
    map: Map<nat, PageTableEntry>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    &&& !candidate_mapping_overlaps_existing_pmem(map, vaddr, pte)
}

//think about weather or not map start is valid if it overlaps with existing vmem
pub open spec fn step_Map_start(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& step_Map_enabled(s1.mappings, vaddr, pte)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === AbstractArguments::Empty
    &&& state_unchanged_besides_thread_state(s1, s2, thread_id, AbstractArguments::Map{vaddr,pte})

}

pub open spec fn step_Map_end(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    result: Result<(), ()>,
) -> bool {
    &&& valid_thread(c, thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, AbstractArguments::Empty)
    &&& match s1.thread_state[thread_id] {
        AbstractArguments::Map{vaddr,pte} => {
            &&& if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
                &&& result is Err
                &&& s2.mappings === s1.mappings
                &&& s2.mem === s1.mem
            } else {
                &&& result is Ok
                &&& s2.mappings === s1.mappings.insert(vaddr, pte)
                &&& (forall|idx: nat| #![auto] s1.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
                &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
            }
        },
        _ => { false }
    }
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& between(vaddr, PT_BOUND_LOW, PT_BOUND_HIGH as nat)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap_start(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
) -> bool {
    &&& step_Unmap_enabled(vaddr)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === AbstractArguments::Empty
    &&& s2.thread_state === s1.thread_state.insert(thread_id, AbstractArguments::Unmap{vaddr})
    //effect from unmap not visible yet (?) at least we cant make guarantees    
    //mem stays the same if vaddr is not valid
    //deleted from mem as we cant make guarantees about it anymore from accesses ????
    &&& s2.mappings === s1.mappings
    &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s1.mappings.remove(vaddr))
}

pub open spec fn step_Unmap_end(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    result: Result<(), ()>,
) -> bool {
    &&& valid_thread(c, thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, AbstractArguments::Empty)
    &&& match s1.thread_state[thread_id] {
        AbstractArguments::Unmap{vaddr} => {
            &&& if s1.mappings.dom().contains(vaddr) {
                &&& result is Ok
                &&& s2.mappings === s1.mappings.remove(vaddr)
                &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
                &&& (forall|idx: nat| #![auto] s2.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
            } else {
                &&& result is Err
                &&& s2.mappings === s1.mappings
                &&& s2.mem === s1.mem
            }
        },
        _ => { false }
    }
}

pub open spec fn step_Resolve_enabled(vaddr: nat) -> bool {
    &&& aligned(vaddr, 8)
}

pub open spec fn step_Resolve_start(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
) -> bool {
    &&& step_Resolve_enabled(vaddr)
    //thread is valid and ready
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id]  === AbstractArguments::Empty
    //thread gets resolve-started state
    &&& state_unchanged_besides_thread_state(s1, s2, thread_id, AbstractArguments::Resolve{vaddr},)
}

pub open spec fn step_Resolve_end(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    result: Result<(nat, PageTableEntry), ()>,
) -> bool {
    &&& valid_thread(c, thread_id)
    &&& state_unchanged_besides_thread_state(s1, s2, thread_id, AbstractArguments::Empty)
    &&& match s1.thread_state[thread_id] {
        AbstractArguments::Resolve{vaddr} => {
            &&& match result {
                Ok((base, pte)) => {
                // If result is Ok, it's an existing mapping that contains vaddr..
                    &&& s1.mappings.contains_pair(base, pte)
                    &&& between(vaddr, base, base + pte.frame.size)
                },
                Err(_) => {
                    let vmem_idx = mem::word_index_spec(vaddr);
                    // If result is Err, no mapping containing vaddr exists..
                    &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
                },
             }
        },
        _ => { false }
    }
}

pub open spec fn step_Stutter(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
) -> bool {
    s1 === s2
}

pub open spec fn next_step(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    step: AbstractStep,
) -> bool {
    match step {
        AbstractStep::ReadWrite      { thread_id, vaddr, op, pte }      => step_ReadWrite       ( c, s1, s2, thread_id, vaddr,  op, pte, ),
        AbstractStep::MapStart       { thread_id, vaddr, pte }          => step_Map_start       ( c, s1, s2, thread_id, vaddr, pte, ),
        AbstractStep::MapEnd         { thread_id, result }              => step_Map_end         ( c, s1, s2, thread_id, result, ),
        AbstractStep::UnmapStart     { thread_id, vaddr, }              => step_Unmap_start     ( c, s1, s2, thread_id, vaddr, ),
        AbstractStep::UnmapEnd       { thread_id, result }              => step_Unmap_end       ( c, s1, s2, thread_id, result,),
        AbstractStep::ResolveStart   { thread_id, vaddr, }              => step_Resolve_start   ( c, s1, s2, thread_id, vaddr, ),
        AbstractStep::ResolveEnd     { thread_id, result }              => step_Resolve_end     ( c, s1, s2, thread_id, result,),
        AbstractStep::Stutter                                           => step_Stutter         ( c, s1, s2),
    }
}

pub open spec fn next(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(c, s1, s2, step)
}

} // verus!
