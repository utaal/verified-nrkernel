#![cfg_attr(verus_keep_ghost, verus::trusted)]
// trusted:
// describes how the whole system behaves

use vstd::prelude::*;

use crate::spec_t::mmu::{ rl3, rl1 };
use crate::spec_t::{ hlspec, mmu };
use crate::spec_t::mmu::defs::{
    MemRegion, PTE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR, Core
};
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap, x86_arch_spec, MAX_BASE
};
use crate::theorem::RLbl;
use crate::spec_t::os_ext;
use crate::impl_u::{ wrapped_token, l2_impl::PT };

verus! {

pub struct Constants {
    pub mmu: mmu::Constants,
    //maps User Level Thread to its assigned core
    pub ult2core: Map<nat, Core>,
    //highest thread_id
    pub ult_no: nat,
}

pub struct State {
    pub mmu: rl3::State,
    pub os_ext: os_ext::State,
    pub core_states: Map<Core, CoreState>,
    /// `sound` is a history variable. It doesn't affect the behavior of the state machine but is
    /// used in the refinement.
    pub sound: bool,
}

#[allow(inconsistent_fields)]
pub enum CoreState {
    Idle,
    MapWaiting { ult_id: nat, vaddr: nat, pte: PTE },
    MapExecuting { ult_id: nat, vaddr: nat, pte: PTE },
    MapDone { ult_id: nat, vaddr: nat, pte: PTE, result: Result<(), ()> },
    UnmapWaiting { ult_id: nat, vaddr: nat },
    UnmapExecuting { ult_id: nat, vaddr: nat, result: Option<Result<PTE, ()>> },
    UnmapOpDone { ult_id: nat, vaddr: nat, result: Result<PTE, ()> },
    UnmapShootdownWaiting { ult_id: nat, vaddr: nat, result: Result<PTE, ()> },
}

#[allow(inconsistent_fields)]
pub enum Step {
    MMU,
    MemOp { core: Core },
    ReadPTMem { core: Core, paddr: usize, value: usize },
    Barrier { core: Core },
    Invlpg { core: Core, vaddr: usize },
    // Map
    MapStart { core: Core },
    MapOpStart { core: Core },
    Allocate { core: Core, res: MemRegion },
    MapOpStutter { core: Core, paddr: usize, value: usize },
    MapOpChange { core: Core, paddr: usize, value: usize },
    MapNoOp { core: Core },
    MapEnd { core: Core },
    // Unmap
    UnmapStart { core: Core },
    UnmapOpStart { core: Core },
    Deallocate { core: Core, reg: MemRegion },
    UnmapOpChange { core: Core, paddr: usize, value: usize },
    UnmapOpStutter { core: Core, paddr: usize, value: usize },
    UnmapOpFail { core: Core },
    UnmapInitiateShootdown { core: Core },
    UnmapWaitShootdown { core: Core },
    AckShootdownIPI { core: Core },
    UnmapEnd { core: Core },
}

impl CoreState {
    pub open spec fn is_mapping(self) -> bool {
        match self {
            CoreState::MapExecuting { .. }
            | CoreState::MapDone { .. } => true,
            _ => false,
        }
    }

    pub open spec fn is_in_crit_sect(self) -> bool {
        match self {
            CoreState::Idle
            | CoreState::MapWaiting { .. }
            | CoreState::UnmapWaiting { .. } => false,
            _ => true,
        }
    }

    #[verifier(inline)]
    pub open spec fn is_idle(self) -> bool {
        self is Idle
    }
}

impl Constants {
    pub open spec fn valid_ult(self, ult_id: nat) -> bool {
        ult_id < self.ult_no
    }

    pub open spec fn valid_core(self, core: Core) -> bool {
        self.mmu.valid_core(core)
    }

    pub open spec fn os_ext(self) -> os_ext::Constants {
        os_ext::Constants {
            node_count: self.mmu.node_count,
            core_count: self.mmu.core_count,
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions for HL-soundness
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    candidate: PTE,
) -> bool {
    exists|b: CoreState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            CoreState::MapWaiting { vaddr, pte, .. }
            | CoreState::MapExecuting { vaddr, pte, .. }
            | CoreState::MapDone { vaddr, pte, .. } => {
                overlap(candidate.frame, pte.frame)
            },
            CoreState::UnmapWaiting { ult_id, vaddr }
            | CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                &&& pt.contains_key(vaddr)
                &&& overlap(candidate.frame, pt[vaddr].frame)
            },
            CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
            | CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
            | CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                &&& result is Ok
                &&& overlap(candidate.frame, result.get_Ok_0().frame)
            },
            CoreState::Idle => false,
        }
    }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    exists|b: CoreState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            CoreState::MapWaiting { vaddr, pte, .. }
            | CoreState::MapExecuting { vaddr, pte, .. }
            | CoreState::MapDone { vaddr, pte, .. } => {
                overlap(
                    MemRegion { base: vaddr, size: pte.frame.size },
                    MemRegion { base: base, size: candidate_size },
                )
            },
            CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                let size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
                overlap(
                    MemRegion { base: vaddr, size: size },
                    MemRegion { base: base, size: candidate_size },
                )
            },
            CoreState::UnmapExecuting { vaddr, result: Some(result), .. }
            | CoreState::UnmapOpDone { vaddr, result, .. }
            | CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                let size = if result is Ok { result.get_Ok_0().frame.size } else { 0 };
                overlap(
                    MemRegion { base: vaddr, size: size },
                    MemRegion { base: base, size: candidate_size },
                )
            },
            _ => false,
        }
    }
}

pub open spec fn step_MMU(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Tau)
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_MemOp(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }
    &&& aligned(vaddr, 8)
    &&& core == c.ult2core[thread_id]
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    //mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::MemOp(core, vaddr as usize, op))
    &&& s2.os_ext == s1.os_ext
    // FIXME(MB): This additional enabling condition here is kind of fishy
    &&& vaddr <= usize::MAX
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can read from page table memory at any point. This transition is used by the
/// implementations of unmap and map to traverse the page table.
pub open spec fn step_ReadPTMem(c: Constants, s1: State, s2: State, core: Core, paddr: usize, value: usize, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Read(core, paddr, value))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can execute a barrier at any point. This transition has to be used after a map.
pub open spec fn step_Barrier(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Barrier(core))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can execute an invlpg at any point. This transition has to be used after an unmap.
pub open spec fn step_Invlpg(c: Constants, s1: State, s2: State, core: Core, vaddr: usize, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Invlpg(core, vaddr))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_sound(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& !candidate_mapping_overlaps_existing_pmem(pt, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(pt, inflightargs, pte)
    &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte.frame.size)
}

pub open spec fn step_Map_enabled(vaddr: nat, pte: PTE) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    //&&& pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_MapStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapStart { thread_id, vaddr, pte }
    &&& core == c.ult2core[thread_id]
    //enabling conditions
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    &&& step_Map_enabled(vaddr, pte)

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapWaiting { ult_id: thread_id, vaddr, pte })
    &&& s2.sound == (s1.sound && step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte))
}

pub open spec fn step_MapOpStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapWaiting { ult_id, vaddr, pte }

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::AcquireLock { core })

    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapExecuting { ult_id, vaddr, pte })
    &&& s2.sound == s1.sound
}

pub open spec fn step_MapOpStutter(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] is MapExecuting
    &&& value & 1 == 1

    // mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    &&& s2.os_ext == s1.os_ext

    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can only allocate pages when they are in a map operation.
/// TODO: We'll need to pre-allocate 4 pages before starting a map to avoid failing allocate calls.
pub open spec fn step_Allocate(c: Constants, s1: State, s2: State, core: Core, res: MemRegion, lbl: RLbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& s1.core_states[core] is MapExecuting

    //mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::Allocate { core, res })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_MapOpChange(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapExecuting { ult_id, vaddr, pte }
    &&& !candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)
    &&& value & 1 == 1
    &&& s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte)

    // mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapDone { ult_id, vaddr, pte, result: Ok(()) })
    &&& s1.sound == s2.sound
}

pub open spec fn step_MapNoOp(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapExecuting { ult_id, vaddr, pte }
    &&& candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapDone { ult_id, vaddr, pte, result: Err(()) })
    &&& s1.sound == s2.sound
}

pub open spec fn step_MapEnd(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapEnd { thread_id, vaddr, result }
    // enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapDone { ult_id, vaddr: vaddr2, pte, result: result2 }
    &&& thread_id == ult_id && vaddr == vaddr2 && result == result2
    &&& s1.mmu@.writes.tso === set![]
    &&& s1.mmu@.pending_maps === map![]
    &&& s2.inv_impl() // impl invariant is re-established

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::ReleaseLock { core })

    // new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(s1: State, vaddr: nat, pte_size: nat) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_UnmapStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapStart { thread_id, vaddr }
    &&& {
    let pt = s1.interp_pt_mem();
    let pte_size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
    //enabling conditions
    &&& core == c.ult2core[thread_id]
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    &&& step_Unmap_enabled(vaddr)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapWaiting { ult_id: thread_id, vaddr })
    &&& s2.sound == (s1.sound && step_Unmap_sound(s1, vaddr, pte_size))
    }
}

pub open spec fn step_UnmapOpStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapWaiting { ult_id, vaddr }
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::AcquireLock { core })
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapExecuting { ult_id, vaddr, result: None })
    &&& s2.sound == s1.sound
}

pub open spec fn step_Deallocate(c: Constants, s1: State, s2: State, core: Core, reg: MemRegion, lbl: RLbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& s1.core_states[core] is UnmapExecuting

    //mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::Deallocate { core, reg })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpChange(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: None }
    &&& value & 1 == 0
    // mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s1.interp_pt_mem().contains_key(vaddr)
    &&& s2.interp_pt_mem() == s1.interp_pt_mem().remove(vaddr)
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapExecuting { ult_id, vaddr, result: Some(Ok(s1.interp_pt_mem()[vaddr])) }
    )

    &&& s2.os_ext == s1.os_ext
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpStutter(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: Some(res) }
    &&& value & 1 == 0
    // mmu statemachine steps
    &&& rl3::next(s1.mmu, s2.mmu, c.mmu, mmu::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.os_ext == s1.os_ext
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpFail(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: None }
    &&& !s1.interp_pt_mem().contains_key(vaddr)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapOpDone { ult_id, vaddr, result: Err(()) }
    )
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapInitiateShootdown(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: Some(Ok(pte)) }
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::InitShootdown { core, vaddr })
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapShootdownWaiting { ult_id, vaddr, result: Ok(pte) },
    )
    &&& s2.sound == s1.sound
}

// Acknowledge TLB eviction to other core (in response to shootdown IPI)
// check if tlb shootdown/unmap has happend and send ACK
pub open spec fn step_AckShootdownIPI(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& !s1.mmu@.writes.nonpos.contains(core)
    &&& !s1.mmu@.tlbs[core].contains_key(s1.os_ext.shootdown_vec.vaddr as usize)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::AckShootdown { core })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapWaitShootdown(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] is UnmapShootdownWaiting
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::WaitShootdown { core })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapEnd(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapEnd { thread_id, vaddr, result }
    //enabling conditions
    &&& c.valid_core(core)
    &&& match s1.core_states[core] {
        CoreState::UnmapShootdownWaiting { result: r2, vaddr: v2, ult_id: id2, .. } => {
            &&& result is Ok
            &&& r2 is Ok
            &&& vaddr == v2
            &&& thread_id == id2
            &&& s1.os_ext.shootdown_vec.open_requests.is_empty()
        },
        CoreState::UnmapOpDone { result: r2, vaddr: v2, ult_id: id2, .. } => {
            &&& result is Err
            &&& r2 is Err
            &&& vaddr == v2
            &&& thread_id == id2
        },
        _ => false,
    }
    &&& s2.inv_impl() // impl invariant is re-established
    &&& s1.mmu@.writes.tso === set![]
    &&& s1.mmu@.writes.nonpos === set![]
    &&& s1.mmu@.pending_unmaps === map![]
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.os_ext(), os_ext::Lbl::ReleaseLock { core })
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s1.sound == s2.sound
}

pub open spec fn next_step(c: Constants, s1: State, s2: State, step: Step, lbl: RLbl) -> bool {
    match step {
        Step::MMU                                   => step_MMU(c, s1, s2, lbl),
        Step::MemOp { core }                        => step_MemOp(c, s1, s2, core, lbl),
        Step::ReadPTMem { core, paddr, value }      => step_ReadPTMem(c, s1, s2, core, paddr, value, lbl),
        Step::Barrier { core }                      => step_Barrier(c, s1, s2, core, lbl),
        Step::Invlpg { core, vaddr }                => step_Invlpg(c, s1, s2, core, vaddr, lbl),
        //Map steps
        Step::MapStart { core }                     => step_MapStart(c, s1, s2, core, lbl),
        Step::MapOpStart { core }                   => step_MapOpStart(c, s1, s2, core, lbl),
        Step::Allocate { core, res }                => step_Allocate(c, s1, s2, core, res, lbl),
        Step::MapOpStutter { core, paddr, value }   => step_MapOpStutter(c, s1, s2, core, paddr, value, lbl),
        Step::MapOpChange { core, paddr, value }    => step_MapOpChange(c, s1, s2, core, paddr, value, lbl),
        Step::MapNoOp { core }                      => step_MapNoOp(c, s1, s2, core, lbl),
        Step::MapEnd { core }                       => step_MapEnd(c, s1, s2, core, lbl),
        //Unmap steps
        Step::UnmapStart { core }                   => step_UnmapStart(c, s1, s2, core, lbl),
        Step::UnmapOpStart { core }                 => step_UnmapOpStart(c, s1, s2, core, lbl),
        Step::Deallocate { core, reg }              => step_Deallocate(c, s1, s2, core, reg, lbl),
        Step::UnmapOpChange { core, paddr, value }  => step_UnmapOpChange(c, s1, s2, core, paddr, value, lbl),
        Step::UnmapOpStutter { core, paddr, value } => step_UnmapOpStutter(c, s1, s2, core, paddr, value, lbl),
        Step::UnmapOpFail { core }                  => step_UnmapOpFail(c, s1, s2, core, lbl),
        Step::UnmapInitiateShootdown { core }       => step_UnmapInitiateShootdown(c, s1, s2, core, lbl),
        Step::UnmapWaitShootdown { core }           => step_UnmapWaitShootdown(c, s1, s2, core, lbl),
        Step::AckShootdownIPI { core }              => step_AckShootdownIPI(c, s1, s2, core, lbl),
        Step::UnmapEnd { core }                     => step_UnmapEnd(c, s1, s2, core, lbl),
    }
}

pub open spec fn next(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    exists|step: Step| next_step(c, s1, s2, step, lbl)
}

pub open spec fn init(c: Constants, s: State) -> bool {
    // hardware stuff
    //&&& s.interp_pt_mem() === Map::empty()
    &&& rl3::init(s.mmu, c.mmu)
    &&& os_ext::init(s.os_ext, c.os_ext())
    // We start with a single directory already allocated for PML4
    &&& s.os_ext.allocated === set![MemRegion { base: s.mmu@.pt_mem.pml4 as nat, size: 4096 }]
    // and that directory is empty
    &&& forall|i: usize| 0 <= i < 512 ==> #[trigger] s.mmu@.pt_mem.read(add(s.mmu@.pt_mem.pml4, mul(i, 8))) == 0
    //wf of ult2core mapping
    &&& forall|id: nat| #[trigger] c.valid_ult(id) <==> c.ult2core.contains_key(id)
    &&& forall|id: nat| c.valid_ult(id) ==> #[trigger] c.valid_core(c.ult2core[id])
    //core_state
    &&& forall|core: Core| c.valid_core(core) <==> #[trigger] s.core_states.contains_key(core)
    &&& forall|core: Core| #[trigger] c.valid_core(core) ==> s.core_states[core] === CoreState::Idle
    //sound
    &&& s.sound
}







// Invariants and definitions for refinement

impl Constants {
    pub open spec fn interp(self) -> hlspec::Constants {
        hlspec::Constants { thread_no: self.ult_no, phys_mem_size: self.mmu.phys_mem_size }
    }
}

impl CoreState {
    pub open spec fn vmem_pte_size(self, pt: Map<nat, PTE>) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. }
            | CoreState::MapDone { pte, .. } => {
                pte.frame.size
            },
            CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 }
            },
            CoreState::UnmapExecuting { result: Some(result), .. }
            | CoreState::UnmapOpDone { result, .. }
            | CoreState::UnmapShootdownWaiting { result, .. } => {
                if result is Ok { result.get_Ok_0().frame.size } else { 0 }
            },
            CoreState::Idle => arbitrary(),
        }
    }

    pub open spec fn vaddr(self) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { vaddr, .. }
            | CoreState::MapExecuting { vaddr, .. }
            | CoreState::MapDone { vaddr, .. }
            | CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, .. }
            | CoreState::UnmapOpDone { vaddr, .. }
            | CoreState::UnmapShootdownWaiting { vaddr, .. } => { vaddr },
            CoreState::Idle => arbitrary(),
        }
    }

    pub open spec fn ult_id(self) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { ult_id, .. }
            | CoreState::MapExecuting { ult_id, .. }
            | CoreState::MapDone { ult_id, .. }
            | CoreState::UnmapWaiting { ult_id, .. }
            | CoreState::UnmapExecuting { ult_id, .. }
            | CoreState::UnmapOpDone { ult_id, .. }
            | CoreState::UnmapShootdownWaiting { ult_id, .. } => { ult_id },
            CoreState::Idle => arbitrary(),
        }
    }
}

impl State {
    pub open spec fn interp_pt_mem(self) -> Map<nat, PTE> {
        crate::spec_t::mmu::defs::nat_keys(self.mmu@.pt_mem@)
    }

    pub open spec fn inflight_unmap_vaddr(self) -> Set<nat> {
        Set::new(|v_address: nat| {
            &&& self.interp_pt_mem().contains_key(v_address)
            &&& exists|core: Core|
                self.core_states.contains_key(core) && match self.core_states[core] {
                    CoreState::UnmapWaiting { ult_id, vaddr }
                    | CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                        vaddr === v_address
                    },
                    _ => false,
                }
        })
    }

    pub open spec fn inflight_vaddr(self) -> Set<nat> {
        Set::new(|v_address: nat| {
            &&& self.interp_pt_mem().contains_key(v_address)
            &&& exists|core: Core|
                self.core_states.contains_key(core) && match self.core_states[core] {
                    CoreState::UnmapWaiting { ult_id, vaddr }
                    | CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
                    | CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                        vaddr === v_address
                    },
                    _ => false,
                }
        })
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PTE> {
        self.interp_pt_mem().remove_keys(self.inflight_vaddr())
    }

    pub open spec fn has_base_and_pte_for_vaddr(effective_mappings: Map<nat, PTE>, vaddr: int) -> bool {
        exists|base: nat, pte: PTE| #![auto]
            effective_mappings.contains_pair(base, pte)
            && between(vaddr as nat, base, base + pte.frame.size)
    }

    pub open spec fn base_and_pte_for_vaddr(effective_mappings: Map<nat, PTE>, vaddr: int) -> (nat, PTE) {
        choose|base: nat, pte: PTE| #![auto]
            effective_mappings.contains_pair(base, pte)
            && between(vaddr as nat, base, base + pte.frame.size)
    }

    pub open spec fn vmem_apply_mappings(
        effective_mappings: Map<nat, PTE>,
        phys_mem: Seq<u8>
    ) -> Seq<u8> {
        Seq::new(
            MAX_BASE,
            |vaddr: int| {
                if Self::has_base_and_pte_for_vaddr(effective_mappings, vaddr) {
                    let (base, pte) = Self::base_and_pte_for_vaddr(effective_mappings, vaddr);
                    phys_mem[pte.frame.base + (vaddr - base)]
                } else {
                    0
                }
        })
    }

    pub open spec fn interp_vmem(self, c: Constants) -> Seq<u8> {
        Self::vmem_apply_mappings(self.effective_mappings(), self.mmu@.phys_mem)
    }

    pub open spec fn interp_thread_state(self, c: Constants) -> Map<nat, hlspec::ThreadState> {
        Map::new(
            |ult_id: nat| c.valid_ult(ult_id),
            |ult_id: nat| {
                    match self.core_states[c.ult2core[ult_id]] {
                        CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte }
                        | CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte }
                        | CoreState::MapDone { ult_id: ult_id2, vaddr, pte, .. } => {
                            if ult_id2 == ult_id {
                                hlspec::ThreadState::Map { vaddr, pte }
                            } else {
                                hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                        | CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None } => {
                            let pte = if self.interp_pt_mem().contains_key(vaddr) {
                                Some(self.interp_pt_mem()[vaddr])
                            } else {
                                None
                            };
                            if ult_id2 == ult_id {
                                hlspec::ThreadState::Unmap { vaddr, pte }
                            } else {
                                hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result) }
                        | CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result }
                        | CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result } => {
                            if ult_id2 == ult_id {
                                hlspec::ThreadState::Unmap { vaddr, pte:
                                    match result {
                                        Ok(pte) => Some(pte),
                                        Err(_) => None,
                                    }
                                }
                            } else {
                                hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::Idle => hlspec::ThreadState::Idle,
                    }
                },
        )
    }

    pub open spec fn interp(self, c: Constants) -> hlspec::State {
        let mappings = self.effective_mappings();
        let mem = self.interp_vmem(c);
        let thread_state = self.interp_thread_state(c);
        let sound = self.sound;
        hlspec::State { mem, mappings, thread_state, sound }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant and WF
    ///////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn valid_ids(self, c: Constants) -> bool {
        forall|core: Core|
            c.valid_core(core) ==> match self.core_states[core] {
                CoreState::MapWaiting { ult_id, .. }
                | CoreState::MapExecuting { ult_id, .. }
                | CoreState::MapDone { ult_id, .. }
                | CoreState::UnmapWaiting { ult_id, .. }
                | CoreState::UnmapExecuting { ult_id, .. }
                | CoreState::UnmapOpDone { ult_id, .. }
                | CoreState::UnmapShootdownWaiting { ult_id, .. } => {
                    &&& c.valid_ult(ult_id)
                    &&& c.ult2core[ult_id] === core
                },
                CoreState::Idle => true,
            }
    }

    pub open spec fn inv_mappings_in_bound(self, c: Constants) -> bool {
        &&& forall|core: Core| #![auto] c.valid_core(core) ==>
                match self.core_states[core] {
                    CoreState::MapWaiting { vaddr, pte, .. }
                    | CoreState::MapExecuting { vaddr, pte, .. }
                    | CoreState::MapDone { vaddr, pte, .. }
                        => candidate_mapping_in_bounds(vaddr, pte),
                    _ => true,
                }
        &&& forall|vaddr, pte| #![auto] self.interp_pt_mem().contains_pair(vaddr, pte) ==> candidate_mapping_in_bounds(vaddr, pte)
    }

    pub open spec fn inv_inflight_pte_above_zero_pte_result_consistent(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. }
                | CoreState::MapDone { vaddr, pte, .. }
                    => pte.frame.size > 0,
                CoreState::UnmapWaiting { vaddr, .. }
                | CoreState::UnmapExecuting { vaddr, result: None, .. }
                    => self.interp_pt_mem().contains_key(vaddr)
                        ==> self.interp_pt_mem()[vaddr].frame.size > 0,
                CoreState::UnmapExecuting { result: Some(result), .. }
                | CoreState::UnmapOpDone { result, .. }
                | CoreState::UnmapShootdownWaiting { result, .. }
                    => result is Ok ==> result.get_Ok_0().frame.size > 0,
                CoreState::Idle => true,
            }
    }

    pub open spec fn inv_successful_maps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapDone { vaddr, pte, result: Result::Ok(_), .. }
                    => self.interp_pt_mem().contains_pair(vaddr, pte),
                _ => true,
            }
    }

    pub open spec fn inv_overlap_of_mapped_maps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapDone { vaddr, pte, result: Result::Ok(_), .. }
                    => !candidate_mapping_overlaps_existing_vmem(self.interp_pt_mem().remove(vaddr), vaddr, pte),
                CoreState::MapDone { vaddr, pte, result: Result::Err(_), .. }
                    => candidate_mapping_overlaps_existing_vmem(self.interp_pt_mem(), vaddr, pte),
                _ => true,
            }
    }


    pub open spec fn inv_successful_unmaps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::UnmapExecuting { vaddr, result: Some(_), .. }
                | CoreState::UnmapOpDone { vaddr, .. }
                | CoreState::UnmapShootdownWaiting { vaddr, .. }
                    => !self.interp_pt_mem().contains_key(vaddr),
                _ => true,
            }
    }

    pub open spec fn inv_lock(self, c: Constants) -> bool {
        forall|core: Core| #[trigger] c.valid_core(core) ==>
            (self.os_ext.lock === Some(core) <==> self.core_states[core].is_in_crit_sect())
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& self.valid_ids(c)
        &&& forall|id: nat| #[trigger] c.valid_ult(id) <==> c.ult2core.contains_key(id)
        &&& forall|id: nat| c.valid_ult(id) ==> #[trigger] c.valid_core(c.ult2core[id])
        &&& forall|core: Core| c.valid_core(core) <==> #[trigger] self.core_states.contains_key(core)
    }

    pub open spec fn inv_mapped_ptes_above_zero(self) -> bool {
        forall|vaddr| #[trigger] self.interp_pt_mem().dom().contains(vaddr) ==> self.interp_pt_mem()[vaddr].frame.size > 0
    }

    pub open spec fn inv_basic(self, c: Constants) -> bool {
        &&& self.wf(c)
        &&& self.inv_mmu(c)
        &&& self.inv_mapped_ptes_above_zero()
        &&& self.inv_mappings_in_bound(c)
        &&& self.inv_inflight_pte_above_zero_pte_result_consistent(c)
        &&& self.inv_successful_unmaps(c)
        &&& self.inv_successful_maps(c)
        &&& self.inv_overlap_of_mapped_maps(c)
        &&& self.inv_lock(c)
    }

    pub open spec fn inv_pending_maps(self, c: Constants) -> bool {
        &&& forall |base| #[trigger] self.mmu@.pending_maps.dom().contains(base) ==>
            exists |core| Self::is_pending_for_core(c, base, core,
                self.core_states, self.mmu@.pending_maps)
    }

    pub open spec fn is_pending_for_core(c: Constants, base: usize, core: Core, core_states: Map<Core, CoreState>, pending_maps: Map<usize, PTE>) -> bool
        recommends pending_maps.dom().contains(base)
    {
        core_states.dom().contains(core)
            && match core_states[core] {
                CoreState::MapDone { ult_id, vaddr, pte, result } =>
                    vaddr == base
                     && pte == pending_maps[base],
                _ => false,
            }
    }

    pub open spec fn inv_mmu(self, c: Constants) -> bool {
        &&& self.mmu.inv(c.mmu)
        // The rl3 invariant is closed, the rl2 one is not but maybe it should be. Keeping it open
        // for now because it accidentally helps with some of the wrapped_token proofs.
        &&& self.mmu.interp().inv(c.mmu)
        &&& self.mmu@.happy
        &&& forall|va| aligned(va as nat, 8) ==> #[trigger] self.mmu@.pt_mem.mem.contains_key(va)
        &&& aligned(self.mmu@.pt_mem.pml4 as nat, 4096)
        &&& self.mmu@.pt_mem.pml4 + 4096 <= MAX_PHYADDR
    }

    pub open spec fn inv_osext(self) -> bool {
        &&& forall|r| #[trigger] self.os_ext.allocated.contains(r) ==> {
            &&& aligned(r.base, 4096)
            &&& r.base + 4096 <= MAX_PHYADDR
            &&& r.size == 4096
        }
        &&& self.allocated_regions_disjoint()
    }

    pub open spec fn allocated_regions_disjoint(self) -> bool {
        forall|r1, r2|
            self.os_ext.allocated.contains(r1)
            && self.os_ext.allocated.contains(r2)
            && r1 != r2
            ==> !(#[trigger] overlap(r1, r2))
    }

    pub open spec fn inv_shootdown(self, c: Constants) -> bool {
        &&& !(self.os_ext.lock matches Some(core) && self.core_states[core] is UnmapShootdownWaiting)
            ==> self.os_ext.shootdown_vec.open_requests.is_empty()
        &&& (self.os_ext.lock matches Some(core) && 
            self.core_states[core] matches CoreState::UnmapShootdownWaiting { .. })
            ==> self.mmu@.writes.nonpos.subset_of(self.os_ext.shootdown_vec.open_requests)
    }

    pub open spec fn inv_writes(self, c: Constants) -> bool {
        &&& self.mmu@.writes.nonpos.subset_of(Set::new(|core| c.valid_core(core)))
        &&& (self.os_ext.lock matches Some(core) && self.core_states[core].is_mapping())
                ==> self.mmu@.writes.nonpos === set![]
        &&& (self.os_ext.lock matches Some(core) && 
            self.core_states[core] matches CoreState::UnmapExecuting { result: None, .. })
                ==> self.mmu@.writes.tso === set![] && self.mmu@.writes.nonpos === set![]
        &&& self.os_ext.lock is None ==> {
            &&& self.mmu@.writes.tso === set![]
            &&& self.mmu@.writes.nonpos === set![]
        }
        &&& forall|core|
            #[trigger] c.valid_core(core)
            && self.core_states[core].is_in_crit_sect()
            && self.mmu@.writes.tso !== set![]
                ==> self.mmu@.writes.core == core
    }

    /// This invariant isn't particularly meaningful in the OS state machine. It's trivially
    /// preserved when no thread holds the lock, and its preservation when the lock is held is
    /// ensured by the implementation, via enabling conditions on the corresponding transitions.
    /// The only tricky part is proving it from `init`.
    pub open spec fn inv_impl(self) -> bool {
        self.os_ext.lock is None ==>
            forall|wtok: wrapped_token::WrappedTokenView| ({
                &&& wtok.pt_mem == self.mmu@.pt_mem
                &&& wtok.regions.dom() == self.os_ext.allocated
                &&& #[trigger] wtok.regions_derived_from_view()
            }) ==> exists|pt| PT::inv_and_nonempty(wtok, pt)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.inv_basic(c)
        &&& self.inv_impl()
        &&& self.inv_writes(c)
        &&& self.inv_shootdown(c)
        &&& self.inv_osext()
        //&&& self.tlb_inv(c)
        &&& self.overlapping_vmem_inv(c)
        &&& self.inv_pending_maps(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about the TLB
    ///////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn shootdown_cores_valid(self, c: Constants) -> bool {
        forall|core| #[trigger]
            self.os_ext.shootdown_vec.open_requests.contains(core) ==> c.valid_core(core)
    }

    pub open spec fn successful_IPI(self, c: Constants) -> bool {
        forall|dispatcher: Core| {
                c.valid_core(dispatcher) ==> match self.core_states[dispatcher] {
                    CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                        forall|handler: Core|
                            !(#[trigger] self.os_ext.shootdown_vec.open_requests.contains(handler))
                                ==> !self.mmu@.tlbs[handler].contains_key(vaddr as usize)
                    },
                    _ => true,
                }
            }
    }

    //returns set with the vaddr that is currently unmapped.
    pub open spec fn unmap_vaddr(self) -> Set<nat> {
        Set::new(|v_address: nat| exists|core: Core|
            self.core_states.contains_key(core) && match self.core_states[core] {
                CoreState::UnmapOpDone { vaddr, result, .. }
                | CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                    (result is Ok) && (vaddr === v_address)
                },
                _ => false,
            }

        )
    }

    pub open spec fn TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(self, c: Constants) -> bool {
        forall|core: Core| {
                #[trigger] c.valid_core(core)
                        // FIXME(MB): I added the map here. Not yet sure if this will cause
                        // problems. If so, might have to switch the MMU models over to using nat
                        // instead of usize.
                    ==> self.mmu@.tlbs[core].dom().map(|v| v as nat).subset_of(
                        self.interp_pt_mem().dom().union(self.unmap_vaddr())
                )
            }
    }

    //pub open spec fn shootdown_exists(self, c: Constants) -> bool {
    //    !(self.shootdown_vec.open_requests === Set::<Core>::empty())
    //        ==> exists|core| c.valid_core(core)
    //            && self.core_states[core] matches (CoreState::UnmapShootdownWaiting { vaddr, .. })
    //}

    pub open spec fn tlb_inv(self, c: Constants) -> bool {
        &&& self.shootdown_cores_valid(c)
        &&& self.successful_IPI(c)
        &&& self.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about overlapping
    ///////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn inflight_map_no_overlap_inflight_vmem(self, c: Constants) -> bool {
        forall|core1: Core, core2: Core|
            (c.valid_core(core1) && c.valid_core(core2)
                && !self.core_states[core1].is_idle() && !self.core_states[core2].is_idle()
                && overlap(
                MemRegion {
                    base: self.core_states[core1].vaddr(),
                    size: self.core_states[core1].vmem_pte_size(self.interp_pt_mem()),
                },
                MemRegion {
                    base: self.core_states[core2].vaddr(),
                    size: self.core_states[core2].vmem_pte_size(self.interp_pt_mem()),
                },
            )) ==> core1 === core2
    }

    pub open spec fn existing_map_no_overlap_existing_vmem(self, c: Constants) -> bool {
        forall|vaddr| #[trigger] self.interp_pt_mem().contains_key(vaddr)
                ==> !candidate_mapping_overlaps_existing_vmem(
                        self.interp_pt_mem().remove(vaddr),
                        vaddr,
                        self.interp_pt_mem()[vaddr],
            )
    }

    pub open spec fn overlapping_vmem_inv(self, c: Constants) -> bool {
        self.sound ==> {
            &&& self.inflight_map_no_overlap_inflight_vmem(c)
            &&& self.existing_map_no_overlap_existing_vmem(c)
        }
    }

}

impl Step {
    pub open spec fn interp(self, pre: State, post: State, c: Constants, lbl: RLbl) -> hlspec::Step {
        match self {
            Step::MemOp { core } => {
                let vaddr = lbl->MemOp_vaddr;
                let op = lbl->MemOp_op;
                let lbl = mmu::Lbl::MemOp(core, vaddr as usize, op);
                // The transition is defined on rl3 but we're doing the case distinction on rl1
                // because in the OS refinement proofs we're working with the rl1 transitions.
                let mmu_step = choose|step| rl1::next_step(pre.mmu@, post.mmu@, c.mmu, step, lbl);
                match mmu_step {
                    rl1::Step::MemOpNoTr => hlspec::Step::MemOp { pte: None },
                    rl1::Step::MemOpNoTrNA { .. } => hlspec::Step::MemOpNA,
                    rl1::Step::MemOpTLB { tlb_va } =>
                        hlspec::Step::MemOp {
                            pte: Some((tlb_va as nat, pre.effective_mappings()[tlb_va as nat]))
                        },
                    _ => arbitrary(),
                }
            },
            // Map steps
            Step::MapStart { .. } => hlspec::Step::MapStart,
            Step::MapEnd { .. } => hlspec::Step::MapEnd,
            // Unmap steps
            Step::UnmapStart { .. } => hlspec::Step::UnmapStart,
            Step::UnmapEnd { core } => hlspec::Step::UnmapEnd,
            _ => hlspec::Step::Stutter,
        }
    }
}

} // verus!
