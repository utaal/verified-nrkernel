#![verus::trusted]
// trusted:
// this is the process-level specification of the kernel's behaviour

use vstd::prelude::*;
use crate::spec_t::mmu::defs::{
    aligned, between, candidate_mapping_in_bounds,
    candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem, overlap,
    x86_arch_spec, MemRegion, PTE, MemOp, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
    MAX_PHYADDR, WORD_SIZE,
};
use crate::spec_t::mem;
use crate::theorem::RLbl;

use crate::spec_t::hlproof::{
    insert_non_map_preserves_unique, lemma_mem_domain_from_mapping_finite, map_end_preserves_inv,
    map_start_preserves_inv, unmap_start_preserves_inv,
};

verus! {

pub struct Constants {
    pub thread_no: nat,
    pub phys_mem_size: nat,
}

pub struct State {
    /// Word-indexed virtual memory
    pub mem: Map<nat, nat>,
    pub thread_state: Map<nat, ThreadState>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat, PTE>,
    pub sound: bool,
}

#[allow(inconsistent_fields)]
pub enum Step {
    MemOp { pte: Option<(nat, PTE)> },
    MemOpNA,
    MapStart,
    MapEnd,
    UnmapStart,
    UnmapEnd,
    Stutter,
}

#[allow(inconsistent_fields)]
pub enum ThreadState {
    Map { vaddr: nat, pte: PTE },
    Unmap { vaddr: nat, pte: Option<PTE> },
    Idle,
}

impl State {
    pub open spec fn vaddr_mapping_is_being_modified(self, c: Constants, va: nat) -> bool {
        exists|thread| {
            &&& c.valid_thread(thread)
            &&& match self.thread_state[thread] {
                ThreadState::Map { vaddr, pte } => between(va, vaddr, vaddr + pte.frame.size),
                ThreadState::Unmap { vaddr, pte: Some(pte) }
                    => between(va, vaddr, vaddr + pte.frame.size),
                _ => false,
            }
        }
    }

    pub open spec fn vaddr_mapping_is_being_modified_choose(self, c: Constants, va: nat) -> Option<(nat, PTE)>
        recommends self.vaddr_mapping_is_being_modified(c, va)
    {
        let thread = choose|thread| {
            &&& c.valid_thread(thread)
            &&& match self.thread_state[thread] {
                ThreadState::Map { vaddr, pte } => between(va, vaddr, vaddr + pte.frame.size),
                ThreadState::Unmap { vaddr, pte: Some(pte) }
                    => between(va, vaddr, vaddr + pte.frame.size),
                _ => false,
            }
        };
        match self.thread_state[thread] {
            // Non-atomic pagefault
            ThreadState::Map { vaddr, pte }              => None,
            // Non-atomic successful translation
            ThreadState::Unmap { vaddr, pte: Some(pte) } => Some((vaddr, pte)),
            _                                            => arbitrary(),
        }
    }
}


pub open spec fn wf(c: Constants, s: State) -> bool {
    &&& forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
    &&& s.mem.dom().finite()
}

pub open spec fn init(c: Constants, s: State) -> bool {
    &&& s.mem === Map::empty()
    &&& s.mappings === Map::empty()
    &&& forall|id: nat| id < c.thread_no ==> (s.thread_state[id] === ThreadState::Idle)
    &&& wf(c, s)
    &&& s.sound
}

pub open spec fn mem_domain_from_mappings_contains(
    phys_mem_size: nat,
    word_idx: nat,
    mappings: Map<nat, PTE>,
) -> bool {
    let vaddr = word_idx * WORD_SIZE as nat;
    exists|base: nat, pte: PTE|
        {
            &&& #[trigger] mappings.contains_pair(base, pte)
            &&& mem_domain_from_entry_contains(phys_mem_size, vaddr, base, pte)
        }
}

pub open spec fn mem_domain_from_entry_contains(
    phys_mem_size: nat,
    vaddr: nat,
    base: nat,
    pte: PTE,
) -> bool {
    let paddr = (pte.frame.base + (vaddr - base)) as nat;
    let pmem_idx = mem::word_index_spec(paddr);
    &&& between(vaddr, base, base + pte.frame.size)
    &&& pmem_idx < phys_mem_size
}

pub open spec fn mem_domain_from_mappings(phys_mem_size: nat, mappings: Map<nat, PTE>) -> Set<nat> {
    Set::new(|word_idx: nat| mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings))
}

pub open spec fn mem_domain_from_entry(phys_mem_size: nat, base: nat, pte: PTE) -> Set<nat> {
    Set::new(|word_idx: nat|
            mem_domain_from_entry_contains(phys_mem_size, (word_idx * WORD_SIZE as nat), base, pte),
    )
}

impl Constants {
    pub open spec fn valid_thread(self, thread_id: nat) -> bool {
        thread_id < self.thread_no
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Helper function to specify relation between 2 states
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn state_unchanged_besides_thread_state(
    s1: State,
    s2: State,
    thread_id: nat,
    thread_arguments: ThreadState,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings
    &&& s2.sound == s1.sound
}

pub open spec fn unsound_state(s1: State, s2: State) -> bool {
    !s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    inflightargs: Set<ThreadState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    &&& exists|b: ThreadState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                ThreadState::Map { vaddr, pte } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                ThreadState::Unmap { vaddr, pte } => {
                    let size = if pte.is_some() {
                        pte.unwrap().frame.size
                    } else {
                        0
                    };
                    overlap(
                        MemRegion { base: vaddr, size: size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                _ => { false },
            }
        }
}

pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    inflightargs: Set<ThreadState>,
    candidate: PTE,
) -> bool {
    exists|b: ThreadState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            ThreadState::Map { vaddr, pte } => overlap(candidate.frame, pte.frame),
            ThreadState::Unmap { vaddr, pte } => {
                &&& pte.is_some()
                &&& overlap(candidate.frame, pte.unwrap().frame)
            },
            _ => { false },
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// MMU atomic ReadWrite
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_MemOp(c: Constants, s1: State, s2: State, pte: Option<(nat, PTE)>, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }
    &&& {
    let vmem_idx = mem::word_index_spec(vaddr);
    &&& aligned(vaddr, 8)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            // .. and the result depends on the flags.
            &&& match op {
                MemOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value as nat)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                MemOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.index(vmem_idx)
                    } else {
                        &&& result is Pagefault
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& op.is_pagefault()
        },
    }
    &&& s2.mappings === s1.mappings
    &&& s2.thread_state === s1.thread_state
    &&& s2.sound == s1.sound
    }
}

/// If there's an inflight map/unmap for this virtual address, we might still see a stale result.
/// TODO: This duplicates all of the step_MemOp transition. Ideally we could find a way to combine
/// these. But we need to be precise enough to state that the only "unexpected" thing we can see is
/// the old stale result. (Combining is also better for use to reason about implementations but
/// generally we can easily show that this transition is irrelevant.)
pub open spec fn step_MemOpNA(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }

    &&& s1.vaddr_mapping_is_being_modified(c, vaddr)
    &&& {
    let pte = s1.vaddr_mapping_is_being_modified_choose(c, vaddr);
    let vmem_idx = mem::word_index_spec(vaddr);
    &&& aligned(vaddr, 8)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            // .. and the result depends on the flags.
            &&& match op {
                MemOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value as nat)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                MemOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.index(vmem_idx)
                    } else {
                        &&& result is Pagefault
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(vmem_idx)
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& op.is_pagefault()
        },
    }
    &&& s2.mappings === s1.mappings
    &&& s2.thread_state === s1.thread_state
    &&& s2.sound == s1.sound
    }

}

///////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_sound(
    mappings: Map<nat, PTE>,
    inflights: Set<ThreadState>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& !candidate_mapping_overlaps_inflight_vmem(inflights, vaddr, pte.frame.size)
    &&& !candidate_mapping_overlaps_existing_pmem(mappings, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(inflights, pte)
}

pub open spec fn step_Map_enabled(
    inflight: Set<ThreadState>,
    map: Map<nat, PTE>,
    vaddr: nat,
    pte: PTE,
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
}

// TODO: think about whether or not map start is valid if it overlaps with existing vmem
pub open spec fn step_MapStart(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapStart { thread_id, vaddr, pte }
    &&& step_Map_enabled(s1.thread_state.values(), s1.mappings, vaddr, pte)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Map_sound(s1.mappings, s1.thread_state.values(), vaddr, pte) {
        state_unchanged_besides_thread_state(s1, s2, thread_id, ThreadState::Map { vaddr, pte })
    } else {
        unsound_state(s1, s2)
    }
}

pub open spec fn step_MapEnd(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapEnd { thread_id, vaddr, result }
    &&& s2.sound == s1.sound
    &&& c.valid_thread(thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& s1.thread_state[thread_id] matches ThreadState::Map { vaddr: vaddr2, pte }
    &&& vaddr == vaddr2
    &&& if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
        &&& result is Err
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    } else {
        &&& result is Ok
        &&& s2.mappings === s1.mappings.insert(vaddr, pte)
        &&& (forall|idx: nat| #![auto] s1.mem.contains_key(idx) ==> s2.mem[idx] === s1.mem[idx])
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(
    inflights: Set<ThreadState>,
    vaddr: nat,
    pte_size: nat,
) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(inflights, vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

// TODO:
// shouldnt need to check for overlapping pmem because:
// - if currently being mapped it will cause Err anyways
// - if currently being unmapped then vmem is the way to go (?)
pub open spec fn step_UnmapStart(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapStart { thread_id, vaddr }
    &&& {
    let pte = if s1.mappings.contains_key(vaddr) { Some(s1.mappings[vaddr]) } else { Option::None };
    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };
    &&& step_Unmap_enabled(vaddr)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Unmap_sound(s1.thread_state.values(), vaddr, pte_size) {
            &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Unmap { vaddr, pte })
            &&& if pte is None {
                &&& s2.mappings === s1.mappings
                &&& s2.mem === s1.mem
            } else {
                &&& s2.mappings === s1.mappings.remove(vaddr)
                &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
                &&& forall|idx: nat| #![auto] s2.mem.contains_key(idx) ==> s2.mem[idx] === s1.mem[idx]
            }
            &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s1.mappings.remove(vaddr))
            &&& s2.sound == s1.sound
        } else {
            unsound_state(s1, s2)
        }
    }
}

pub open spec fn step_UnmapEnd(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapEnd { thread_id, vaddr, result }

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] matches ThreadState::Unmap { vaddr: v2, pte }
    &&& vaddr == v2
    &&& pte is Some <==> result is Ok

    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& s2.sound == s1.sound
    &&& s2.mappings === s1.mappings
    &&& s2.mem === s1.mem
}

pub open spec fn step_Stutter(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl is Tau
    &&& s1 === s2
}

//if s1.sound then match else !s2.sound
pub open spec fn next_step(c: Constants, s1: State, s2: State, step: Step, lbl: RLbl) -> bool {
    if s1.sound {
        match step {
            Step::MemOp { pte } => step_MemOp(c, s1, s2, pte, lbl),
            Step::MemOpNA       => step_MemOpNA(c, s1, s2, lbl),
            Step::MapStart      => step_MapStart(c, s1, s2, lbl),
            Step::MapEnd        => step_MapEnd(c, s1, s2, lbl),
            Step::UnmapStart    => step_UnmapStart(c, s1, s2, lbl),
            Step::UnmapEnd      => step_UnmapEnd(c, s1, s2, lbl),
            Step::Stutter       => step_Stutter(c, s1, s2, lbl),
        }
    } else {
        !s2.sound
    }
}

pub open spec fn next(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    exists|step: Step| next_step(c, s1, s2, step, lbl)
}

pub open spec fn pmem_no_overlap(mappings: Map<nat, PTE>) -> bool {
    forall|bs1: nat, bs2: nat|
        mappings.contains_key(bs1) && mappings.contains_key(bs2)
        && overlap(mappings.index(bs1).frame, mappings.index(bs2).frame)
        ==> bs1 == bs2
}

pub open spec fn inflight_map_no_overlap_pmem(
    inflightargs: Set<ThreadState>,
    mappings: Map<nat, PTE>,
) -> bool {
    forall|b: ThreadState| #![auto]
        inflightargs.contains(b) && b is Map
            ==> !candidate_mapping_overlaps_existing_pmem(mappings, b->Map_pte)

}

pub open spec fn inflight_map_no_overlap_inflight_pmem(inflightargs: Set<ThreadState>) -> bool {
    forall|b: ThreadState| #![auto]
        inflightargs.contains(b) && b is Map
            ==> !candidate_mapping_overlaps_inflight_pmem(inflightargs.remove(b), b->Map_pte)
}

pub open spec fn if_map_then_unique(thread_state: Map<nat, ThreadState>, id: nat) -> bool
    recommends thread_state.contains_key(id),
{
    thread_state[id] matches ThreadState::Map { vaddr, pte }
        ==> !thread_state.remove(id).values().contains(thread_state[id])
}

pub open spec fn inflight_maps_unique(thread_state: Map<nat, ThreadState>) -> bool {
    forall|a: nat| #[trigger] thread_state.contains_key(a) ==> if_map_then_unique(thread_state, a)
}

pub open spec fn inv(c: Constants, s: State) -> bool {
    &&& wf(c, s)
    &&& pmem_no_overlap(s.mappings)
    // invariants needed to prove the former
    &&& inflight_map_no_overlap_pmem(s.thread_state.values(), s.mappings)
    &&& inflight_map_no_overlap_inflight_pmem(s.thread_state.values())
    &&& inflight_maps_unique(s.thread_state)
}

pub proof fn init_implies_inv(c: Constants, s: State)
    requires init(c, s),
    ensures inv(c, s),
{
}

pub proof fn next_step_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        next(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
    ensures
        s2.sound ==> inv(c, s2),
{
    if s1.sound {
        let p = choose|step: Step| next_step(c, s1, s2, step, lbl);
        match p {
            Step::UnmapStart => unmap_start_preserves_inv(c, s1, s2, lbl),
            Step::UnmapEnd => {
                let thread_id = lbl->UnmapEnd_thread_id;
                assert(s2.thread_state.values().subset_of(s1.thread_state.values().insert(ThreadState::Idle)));
                lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
                insert_non_map_preserves_unique(s1.thread_state, thread_id, ThreadState::Idle);
            },
            Step::MapStart => map_start_preserves_inv(c, s1, s2, lbl),
            Step::MapEnd  => map_end_preserves_inv(c, s1, s2, lbl),
            _ => {},
        }
    } else {
        assert(!s2.sound);
    }
}

} // verus!
