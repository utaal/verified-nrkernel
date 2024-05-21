#![verus::trusted]
// trusted:
// this is the process-level specification of the kernel's behaviour

use crate::definitions_t::{
    aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, MemRegion, overlap, PageTableEntry, RWOp, L1_ENTRY_SIZE, L2_ENTRY_SIZE,
    L3_ENTRY_SIZE, MAX_PHYADDR, PT_BOUND_HIGH, PT_BOUND_LOW, WORD_SIZE,
};
use crate::spec_t::mem;
use vstd::prelude::*;

use crate::extra::{lemma_set_of_first_n_nat_is_finite, lemma_subset_is_finite};


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
    UnmapStart         { thread_id: nat, vaddr: nat, },
    UnmapEnd           { thread_id: nat, result: Result<(), ()> },
    ResolveStart       { thread_id: nat, vaddr: nat },
    ResolveEnd         { thread_id: nat, result: Result<(nat, PageTableEntry), ()> },
    Stutter,
}

//To allow two-step transitions that preserve arguments
#[allow(inconsistent_fields)]
pub enum AbstractArguments {
    Map           { vaddr: nat, pte: PageTableEntry },
    Unmap         { vaddr: nat, pte: Option<PageTableEntry> },
    Resolve       { vaddr: nat },
    Empty,
}

pub open spec fn wf(c: AbstractConstants, s:AbstractVariables) -> bool {
    &&& forall |id: nat| id <= c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
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
    exists|base: nat, pte: PageTableEntry|  {&&& #[trigger] mappings.contains_pair(base, pte) 
                                             &&& mem_domain_from_entry_contains( phys_mem_size, vaddr, base, pte,)} 
}

pub open spec fn mem_domain_from_entry_contains(
    phys_mem_size: nat,
    vaddr: nat,
    base: nat, 
    pte: PageTableEntry,
) -> bool {
    let paddr = (pte.frame.base + (vaddr - base)) as nat;
    let pmem_idx = mem::word_index_spec(paddr);
    &&& between(vaddr, base, base + pte.frame.size)
    &&& pmem_idx < phys_mem_size
}

pub open spec fn mem_domain_from_mappings(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub open spec fn mem_domain_from_entry(
    phys_mem_size: nat,
    base: nat,
    pte: PageTableEntry,
) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_entry_contains( phys_mem_size, (word_idx * WORD_SIZE as nat), base, pte,) )
}

pub proof fn lemma_mem_domain_from_entry_finite(
    phys_mem_size: nat,
    base: nat,
    pte: PageTableEntry,
)
    requires
    ensures mem_domain_from_entry(phys_mem_size, base, pte).finite(),
{
    let bound = base + pte.frame.size;
    let vaddrs = mem_domain_from_entry(phys_mem_size, base, pte);
    let n_nats =  Set::new(|i: nat| i < (bound + 1 as nat));
    assert(vaddrs.subset_of(n_nats));
    lemma_set_of_first_n_nat_is_finite(bound + 1);
    lemma_subset_is_finite(n_nats, vaddrs);
    assert(vaddrs.finite());
}
    

pub proof fn lemma_mem_domain_from_empty_mappings_finite(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
)
    requires
         mappings.dom() === Set::empty(),
    ensures
         mem_domain_from_mappings(phys_mem_size, mappings).finite(),
{
    assert(mem_domain_from_mappings(phys_mem_size, mappings) === Set::empty())
}



pub proof fn lemma_mem_domain_from_mapping_finite (
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
)
    requires mappings.dom().finite(),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings).finite(),
{
if (exists |bs: nat| mappings.dom().contains(bs)) {
        let  bs  = choose |bs: nat | mappings.dom().contains(bs);
        let pt = mappings[bs];
        let mappings_reduc = mappings.remove(bs);
        assert(!mappings_reduc.dom().contains(bs));
        assert(mappings_reduc.insert(bs,pt) == mappings);
        assert(mappings_reduc.dom().subset_of( mappings.dom() ));
        lemma_subset_is_finite(mappings.dom(), mappings_reduc.dom());
        lemma_mem_domain_from_mappings_finite_induction(
            phys_mem_size,
            mappings_reduc,
            bs,
            pt,
        );
    } else {
        assert(mappings.dom() === Set::empty());
        lemma_mem_domain_from_empty_mappings_finite(phys_mem_size, mappings);
    }
}



pub proof fn lemma_mem_domain_from_mappings_finite_induction (
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry, 
)
    requires mappings.dom().finite(),
            !mappings.dom().contains(base),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings.insert(base, pte)).finite(),
    decreases mappings.dom().len(),
{
if (exists |bs: nat| mappings.dom().contains(bs)) {
        let  bs  = choose |bs: nat | mappings.dom().contains(bs);
        let pt = mappings[bs];
        let mappings_reduc = mappings.remove(bs);
        assert(!mappings_reduc.dom().contains(bs));
        assert(mappings_reduc.insert(bs,pt) == mappings);
        assert(mappings_reduc.dom().subset_of( mappings.dom() ));
        lemma_subset_is_finite(mappings.dom(), mappings_reduc.dom());
        lemma_mem_domain_from_mappings_finite_induction(
            phys_mem_size,
            mappings_reduc,
            bs,
            pt,
        );
    } else {
        assert(mappings.dom() === Set::empty());
        lemma_mem_domain_from_empty_mappings_finite(phys_mem_size, mappings);
    }
    lemma_finite_step(phys_mem_size, mappings, base, pte);
}


pub proof fn lemma_finite_step(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    base: nat,
    pte: PageTableEntry, 
)
    requires mem_domain_from_mappings(phys_mem_size, mappings).finite(),
             mappings.dom().finite(),
            !mappings.dom().contains(base),
    ensures  mem_domain_from_mappings(phys_mem_size, mappings.insert(base, pte)).finite(),
{
    let mem_dom_ext = mem_domain_from_mappings(phys_mem_size, mappings.insert(base,pte));
    let mem_dom_union = mem_domain_from_mappings(phys_mem_size, mappings).union(mem_domain_from_entry(phys_mem_size, base, pte));
    assert forall |wrd : nat| mem_dom_ext.contains(wrd) implies mem_dom_union.contains(wrd) by {
    lemma_mem_domain_from_new_mappings_subset(phys_mem_size, mappings, base, pte, wrd);
    }
    assert(mem_dom_ext.subset_of(mem_dom_union));
    lemma_mem_domain_from_entry_finite(phys_mem_size, base, pte);
    assert(mem_dom_union.finite());
    lemma_subset_is_finite(mem_dom_union, mem_dom_ext);
}


pub proof fn lemma_mem_domain_from_new_mappings_subset(
    phys_mem_size: nat,
    mappings: Map<nat, PageTableEntry>,
    bs: nat,
    pt: PageTableEntry,
    word_idx: nat,
)
    requires
       mem_domain_from_mappings(phys_mem_size, mappings.insert(bs, pt)).contains(word_idx),
    ensures
       mem_domain_from_mappings(phys_mem_size, mappings).union(mem_domain_from_entry(phys_mem_size, bs, pt)).contains(word_idx)
        
{   
    let mappings_ext = mappings.insert(bs, pt);
    let vaddr = word_idx * WORD_SIZE as nat;
    let (base, pte) : (nat, PageTableEntry) = choose |base: nat, pte: PageTableEntry| {&&& #[trigger] mappings_ext.contains_pair(base, pte) 
                                                                                       &&& mem_domain_from_entry_contains( phys_mem_size, vaddr, base, pte,)};
    if (base === bs && pte === pt){
  
    assert(mem_domain_from_entry(phys_mem_size, bs, pt).contains(word_idx));
    
    } else {
    assert (mappings.contains_pair(base, pte));
    assert (mem_domain_from_mappings(phys_mem_size, mappings).contains(word_idx));

    }
        
}


//ensures that if a new mapping is added the old ones are still in there and no new other mappings appear
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

//since unmap deleted pte inflight pte == pagefault
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

//call with candidate_mapping_overlaps_inflight_vmem(threadstate.values(), pte)
pub open spec fn candidate_mapping_overlaps_inflight_vmem(inflightargs: Set<AbstractArguments>, base: nat, candidate: PageTableEntry) -> bool {
    &&& exists|b: AbstractArguments| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            AbstractArguments::Map {vaddr, pte} => { overlap( MemRegion { base: vaddr, size: pte.frame.size },
                                                              MemRegion { base: base,    size: candidate.frame.size }) }
            AbstractArguments::Unmap{vaddr, pte} =>  { &&& pte.is_some() 
                                                       &&& overlap( MemRegion { base: vaddr, size: pte.unwrap().frame.size },
                                                                     MemRegion { base: base,    size: candidate.frame.size }) }
            _ => {false}
            }
    }
}

pub open spec fn candidate_mapping_overlaps_inflight_pmem(inflightargs: Set<AbstractArguments>, candidate: PageTableEntry) -> bool {
    &&& exists|b: AbstractArguments| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            AbstractArguments::Map {vaddr, pte} => { overlap(candidate.frame, pte.frame)}
            AbstractArguments::Unmap{vaddr, pte} => { &&& pte.is_some() 
                                                      &&& overlap(candidate.frame, pte.unwrap().frame)}
            _ => {false}
            }
    }
}
/*
//call with candidate_mapping_overlaps_inflight_pmem2(threadstate, pte)
pub open spec fn candidate_mapping_overlaps_inflight_pmem2(threadstate : Map<nat,AbstractArguments>, pte: PageTableEntry) -> bool {
    &&& exists|b: nat| #![auto] {
        &&& threadstate.dom().contains(b)
        &&& match threadstate[b] {
            AbstractArguments::Map{vaddr, inflight_pte} => { overlap(pte.frame, inflight_pte.frame)}
            _ => {false}
            }
    }
}
*/
pub open spec fn step_Map_enabled(
    inflight: Set<AbstractArguments>,
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
    &&& !candidate_mapping_overlaps_existing_pmem(map, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(inflight, pte)
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
    &&& step_Map_enabled(s1.thread_state.values(), s1.mappings, vaddr, pte)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === AbstractArguments::Empty
    &&& if (!candidate_mapping_overlaps_inflight_vmem(s1.thread_state.values(), vaddr, pte)) {
        &&& state_unchanged_besides_thread_state(s1, s2, thread_id, AbstractArguments::Map{vaddr,pte})
    } else {
        &&& s2 === s1
    }

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
//shouldnt need to check for overlapping pmem bc:
// if its being mapped rn then itll cause Err anyways
// if its being unmapped rn then vmem is the way to go. 
pub open spec fn step_Unmap_start(
    c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
) -> bool {
     let pte = if (s1.mappings.dom().contains(vaddr)){Some (s1.mappings.index(vaddr))} else {Option::None};
     &&& step_Unmap_enabled(vaddr)
     &&& valid_thread(c, thread_id)
     &&& s1.thread_state[thread_id] === AbstractArguments::Empty
     &&& if (!candidate_mapping_overlaps_inflight_vmem(s1.thread_state.values(), vaddr, (s1.mappings.index(vaddr))) || pte is None) {
        &&& s2.thread_state === s1.thread_state.insert(thread_id, AbstractArguments::Unmap{ vaddr, pte })
        &&& if (pte is None ){s2.mappings === s1.mappings}
            else {s2.mappings === s1.mappings.remove(vaddr)}
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s1.mappings.remove(vaddr))
    } else {
        s2 === s1
    }


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
        AbstractArguments::Unmap{vaddr, pte} => {
            &&& if pte is Some {
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
        AbstractStep::UnmapStart     { thread_id, vaddr  }              => step_Unmap_start     ( c, s1, s2, thread_id, vaddr,  ),
        AbstractStep::UnmapEnd       { thread_id, result }              => step_Unmap_end       ( c, s1, s2, thread_id, result,),
        AbstractStep::ResolveStart   { thread_id, vaddr, }              => step_Resolve_start   ( c, s1, s2, thread_id, vaddr, ),
        AbstractStep::ResolveEnd     { thread_id, result }              => step_Resolve_end     ( c, s1, s2, thread_id, result,),
        AbstractStep::Stutter                                           => step_Stutter         ( c, s1, s2),
    }
}

pub open spec fn next(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables) -> bool {
    exists|step: AbstractStep| next_step(c, s1, s2, step)
}

proof fn init_implies_wf( c: AbstractConstants, s: AbstractVariables,)
    requires init(c, s),
    ensures wf(c, s),
{}

proof fn next_step_preserves_wf(c: AbstractConstants, s1: AbstractVariables, s2: AbstractVariables,)
    requires
        next(c, s1, s2),
        wf(c, s1),
    ensures
        wf(c, s2),

{
    let p = choose|step: AbstractStep| next_step(c, s1, s2, step);
    match p {
         AbstractStep::ReadWrite     { thread_id, vaddr, op, pte }      => {assert(wf(c,s2));},
        AbstractStep::MapStart       { thread_id, vaddr, pte }          => {assert(wf(c,s2));},
        AbstractStep::MapEnd         { thread_id, result }              => {lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
                                                                            assert(wf(c,s2));},
        AbstractStep::UnmapStart     { thread_id, vaddr  }              => {lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s1.mappings.remove(vaddr));
                                                                            assert(wf(c,s2));},
        AbstractStep::UnmapEnd       { thread_id, result }              => { lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
                                                                            assert(wf(c,s2));},
        AbstractStep::ResolveStart   { thread_id, vaddr, }              => {assert(wf(c,s2));},
        AbstractStep::ResolveEnd     { thread_id, result }              => {assert(wf(c,s2));},
        AbstractStep::Stutter                                           => {assert(wf(c,s2));},
    }
}


} // verus!
