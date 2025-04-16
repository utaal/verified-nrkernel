// #![cfg_attr(verus_keep_ghost, verus::trusted)]
// trusted:
// this is the process-level specification of the kernel's behaviour
// TODO: because we have the invariant defined and proved here as well we manually apply the
// trusted label to the relevant parts

use vstd::prelude::*;
use crate::spec_t::mmu::defs::{
    MemRegion, PTE, MemOp, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR,
};
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap, x86_arch_spec, update_range, MAX_BASE
};
use crate::theorem::RLbl;

#[cfg(verus_keep_ghost)]
use crate::spec_t::hlproof::{
    insert_non_map_preserves_unique, map_end_preserves_inv,
    map_start_preserves_inv, unmap_start_preserves_inv,
};

verus! {


// $line_count$Trusted${$

pub struct Constants {
    pub thread_no: nat,
    pub phys_mem_size: nat,
}

pub struct State {
    /// Byte-indexed virtual memory
    pub mem: Seq<u8>,
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

    pub open spec fn vaddr_mapping_is_being_modified_choose_thread(self, c: Constants, va: nat) -> nat
        recommends self.vaddr_mapping_is_being_modified(c, va)
    {
        choose|thread| {
            &&& c.valid_thread(thread)
            &&& match self.thread_state[thread] {
                ThreadState::Map { vaddr, pte } => between(va, vaddr, vaddr + pte.frame.size),
                ThreadState::Unmap { vaddr, pte: Some(pte) }
                    => between(va, vaddr, vaddr + pte.frame.size),
                _ => false,
            }
        }
    }

    // TODO this always returns Some, so it doesn't need to return Option
    pub open spec fn vaddr_mapping_is_being_modified_choose(self, c: Constants, va: nat) -> Option<(nat, PTE)>
        recommends self.vaddr_mapping_is_being_modified(c, va)
    {
        let thread = self.vaddr_mapping_is_being_modified_choose_thread(c, va);
        match self.thread_state[thread] {
            // Non-atomic pagefault
            ThreadState::Map { vaddr, pte }              => Some((vaddr, pte)),
            // Non-atomic successful translation
            ThreadState::Unmap { vaddr, pte: Some(pte) } => Some((vaddr, pte)),
            _                                            => arbitrary(),
        }
    }
}


pub open spec fn wf(c: Constants, s: State) -> bool {
    &&& forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
}

pub open spec fn init(c: Constants, s: State) -> bool {
    &&& s.mem.len() === MAX_BASE
    &&& s.mappings === Map::empty()
    &&& forall|id: nat| id < c.thread_no ==> (s.thread_state[id] === ThreadState::Idle)
    &&& wf(c, s)
    &&& s.sound
}

pub open spec fn is_in_mapped_region(phys_mem_size: nat, mappings: Map<nat, PTE>, vaddr: nat) -> bool {
    exists|base: nat, pte: PTE| {
        &&& #[trigger] mappings.contains_pair(base, pte)
        &&& between(vaddr, base, base + pte.frame.size)
        // TODO: This should arguably be something we require in step_Map_enabled so we'd know all
        // mapped memory is valid
        &&& pte.frame.base + (vaddr - base) < phys_mem_size
    }
}

impl Constants {
    pub open spec fn valid_thread(self, thread_id: nat) -> bool {
        thread_id < self.thread_no
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Helper function to specify relation between 2 states
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn state_unchanged_besides_thread_state_and_mem(
    s1: State,
    s2: State,
    thread_id: nat,
    thread_arguments: ThreadState,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
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

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& aligned(vaddr, op.op_size())
    &&& op.valid_op_size()

    &&& match pte {
        Some((base, pte)) => {
            let paddr = pte.frame.base + (vaddr - base);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            // .. and the result depends on the flags.
            &&& match op {
                MemOp::Store { new_value, result } => {
                    if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === update_range(s1.mem, vaddr as int, new_value)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                MemOp::Load { is_exec, result, .. } => {
                    &&& s2.mem === s1.mem
                    &&& if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.subrange(vaddr as int, vaddr + op.op_size() as int)
                    } else {
                        &&& result is Pagefault
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !is_in_mapped_region(c.phys_mem_size, s1.mappings, vaddr)
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& op.is_pagefault()
        },
    }
    &&& s2.mappings === s1.mappings
    &&& s2.thread_state === s1.thread_state
    &&& s2.sound == s1.sound
}

/// If there's an inflight map/unmap for this virtual address, we might still see a stale result.
/// TODO: This duplicates all of the step_MemOp transition. Ideally we could find a way to combine
/// these. But we need to be precise enough to state that the only "unexpected" thing we can see is
/// the old stale result. (Combining is also better for use to reason about implementations but
/// generally we can easily show that this transition is irrelevant.)
pub open spec fn step_MemOpNA(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& aligned(vaddr, op.op_size())
    &&& op.valid_op_size()

    &&& s1.vaddr_mapping_is_being_modified(c, vaddr)
    &&& {
    let pte = s1.vaddr_mapping_is_being_modified_choose(c, vaddr);
    &&& match pte {
        Some((base, pte)) => {
            ||| (s2.mem === s1.mem && op.is_pagefault())
            ||| ({
                let paddr = pte.frame.base + (vaddr - base);
                // the result depends on the flags
                &&& match op {
                    MemOp::Store { new_value, result } => {
                        if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                            &&& result is Ok
                            &&& s2.mem === update_range(s1.mem, vaddr as int, new_value)
                        } else {
                            &&& result is Pagefault
                            &&& s2.mem === s1.mem
                        }
                    },
                    MemOp::Load { is_exec, result, .. } => {
                        &&& s2.mem === s1.mem
                        &&& if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                            &&& result is Value
                            &&& result->0 == s1.mem.subrange(vaddr as int, vaddr + op.op_size() as int)
                        } else {
                            &&& result is Pagefault
                        }
                    },
                }
            })
        },
        None => {
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
        state_unchanged_besides_thread_state_and_mem(s1, s2, thread_id, ThreadState::Map { vaddr, pte })
        && (if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
            s1.mem == s2.mem
        } else {
            forall|vaddr: nat|  #[trigger] is_in_mapped_region(c.phys_mem_size, s1.mappings, vaddr) ==> s2.mem[vaddr as int] === s1.mem[vaddr as int]
        })
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
    } else {
        &&& result is Ok
        &&& s2.mappings === s1.mappings.insert(vaddr, pte)
    }
    &&& s2.mem === s1.mem
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(s1: State, vaddr: nat, pte_size: nat) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(s1.thread_state.values(), vaddr, pte_size)
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
    &&& if step_Unmap_sound(s1, vaddr, pte_size) {
            &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Unmap { vaddr, pte })
            &&& s2.mappings == if pte is None { s1.mappings } else { s1.mappings.remove(vaddr) }
            &&& s2.sound == s1.sound
            &&& s2.mem === s1.mem
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
    &&& forall|vaddr: nat|  #[trigger] is_in_mapped_region(c.phys_mem_size, s2.mappings, vaddr) ==> s2.mem[vaddr as int] === s1.mem[vaddr as int]
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

// $line_count$}$
// everything below here is invariant definition and/or proof, not trusted


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
                //lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
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
