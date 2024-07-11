#![verus::trusted]
// trusted:
// describes how the whole system behaves
//
// this refers to definitions in an untrusted file, but uses them in a way that the
// state-machine refinement can check

use vstd::prelude::*;

use crate::impl_u::spec_pt;
use crate::spec_t::{hardware, hlspec, mem};
//TODO move core to definitions
use crate::definitions_t::{
    aligned, between, candidate_mapping_in_bounds, candidate_mapping_overlaps_existing_pmem,
    overlap, x86_arch_spec, MemRegion, PageTableEntry, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE,
    MAX_PHYADDR, WORD_SIZE,
};
use crate::spec_t::hardware::Core;

//TODO think about labels
verus! {

pub struct OSConstants {
    pub hw: hardware::HWConstants,
    //maps User Level Thread to its assigned core
    pub ULT2core: Map<nat, Core>,
    //highest thread_id
    pub ULT_no: nat,
}

pub struct OSVariables {
    pub hw: hardware::HWVariables,
    // maps numa node to ULT operation spinning/operating on it
    pub core_states: Map<Core, CoreState>,
    pub TLB_Shootdown: ShootdownVector,
    //Does not affect behaviour of os_specs, just set when operations with overlapping operations are used
    pub sound: bool,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}

// MB: This is not necessarily complete and I didn't add the necessary fields
pub enum CoreState {
    Idle,
    MapWaiting { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    MapExecuting { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    UnmapWaiting { ULT_id: nat, vaddr: nat },
    UnmapOpExecuting { ULT_id: nat, vaddr: nat },
    UnmapOpDone { ULT_id: nat, vaddr: nat, result: Result<(), ()> },
    UnmapShootdownWaiting { ULT_id: nat, vaddr: nat, result: Result<(), ()> },
}

impl CoreState {
    pub open spec fn holds_lock(self) -> bool {
        match self {
            CoreState::Idle
            | CoreState::MapWaiting { .. }
            | CoreState::UnmapWaiting { .. } => false,
            _ => true,
        }
    }
}

impl OSVariables {
    pub open spec fn kernel_lock(self, consts: OSConstants) -> Option<Core> {
        if exists|c: Core|
            hardware::valid_core_id(consts.hw, c) && self.core_states[c].holds_lock() {
            Some(
                choose|c: Core|
                    hardware::valid_core_id(consts.hw, c) && self.core_states[c].holds_lock(),
            )
        } else {
            None
        }
    }

    /*
    pub open spec fn NUMA_pt_mappings_dont_overlap_in_vmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: pte1.frame.size },
                    MemRegion { base: b2, size: pte2.frame.size }))
    }

    pub open spec fn pt_mappings_dont_overlap_in_pmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(pte1.frame, pte2.frame))
    }

    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, pte| self.hw.tlb.contains_pair(base, pte) ==> #[trigger] self.interp_pt_mem().contains_pair(base, pte)
    }

    pub open spec fn pt_entry_sizes_are_valid(self) -> bool {
        forall|base, pte| self.interp_pt_mem().contains_pair(base, pte) ==> {
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        }
    }

    #[verifier(opaque)]
    pub open spec fn pt_entries_aligned(self) -> bool {
        forall|base, pte| self.interp_pt_mem().contains_pair(base, pte)
            ==> aligned(base, 8) && aligned(pte.frame.base, 8)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.pt_mappings_dont_overlap_in_vmem()
        &&& self.pt_mappings_dont_overlap_in_pmem()
        &&& self.pt_entry_sizes_are_valid()
        &&& self.pt_entries_aligned()
        &&& self.tlb_is_submap_of_pt()
    }
	*/
    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables { pt_mem: self.hw.global_pt }
    }

    pub open spec fn interp_pt_mem(self) -> Map<nat, PageTableEntry> {
        hardware::interp_pt_mem(self.hw.global_pt)
    }

    pub open spec fn is_effective_mappings(self, vmem_idx: nat, pte: PageTableEntry) -> bool {
        exists|core: Core| #[trigger]
            self.hw.NUMAs.contains_key(core.NUMA_id)
                && #[trigger] self.hw.NUMAs[core.NUMA_id].cores.contains_key(core.core_id)
                && #[trigger] self.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.contains_pair(
                vmem_idx,
                pte,
            )
    }

    pub open spec fn joint_tlbs(self) -> Map<nat, PageTableEntry> {
        Map::new(
            |vmem_idx: nat|
                {
                    exists|core: Core|
                        #![auto]
                        self.hw.NUMAs.contains_key(core.NUMA_id)
                            && self.hw.NUMAs[core.NUMA_id].cores.contains_key(core.core_id)
                            && self.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.contains_key(
                            vmem_idx,
                        )
                },
            |vmem_idx: nat|
                { choose|pte: PageTableEntry| self.is_effective_mappings(vmem_idx, pte) },
        )
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PageTableEntry> {
        self.interp_pt_mem().union_prefer_right(self.joint_tlbs())
    }

    pub open spec fn interp_vmem(self, c: OSConstants) -> Map<nat, nat> {
        let phys_mem_size = self.interp_constants(c).phys_mem_size;
        let mappings: Map<nat, PageTableEntry> = self.effective_mappings();
        Map::new(
            |vmem_idx: nat|
                hlspec::mem_domain_from_mappings_contains(phys_mem_size, vmem_idx, mappings),
            |vmem_idx: nat|
                {
                    let vaddr = vmem_idx * WORD_SIZE as nat;
                    let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry|
                        #![auto]
                        mappings.contains_pair(base, pte) && between(
                            vaddr,
                            base,
                            base + pte.frame.size,
                        );
                    let paddr = (pte.frame.base + (vaddr - base)) as nat;
                    let pmem_idx = mem::word_index_spec(paddr);
                    self.hw.mem[pmem_idx as int]
                },
        )
    }

    pub open spec fn interp_thread_state(self, c: OSConstants) -> Map<
        nat,
        hlspec::AbstractArguments,
    > {
        Map::new(
            |ult_id: nat| ult_id < c.ULT_no,
            |ult_id: nat|
                {
                    match self.core_states[c.ULT2core[ult_id]] {
                        CoreState::MapWaiting { ULT_id, vaddr, pte } => {
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Map { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::MapExecuting { ULT_id, vaddr, pte } => {
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Map { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapWaiting { ULT_id, vaddr } => {
                            let pte = if (self.interp_pt_mem().dom().contains(vaddr)) {
                                Some(self.interp_pt_mem().index(vaddr))
                            } else {
                                Option::None
                            };
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                            let pte = if (self.interp_pt_mem().dom().contains(vaddr)) {
                                Some(self.interp_pt_mem().index(vaddr))
                            } else {
                                Option::None
                            };
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapOpDone { ULT_id, vaddr, result } => {
                            let pte = if (self.interp_pt_mem().dom().contains(vaddr)) {
                                Some(self.interp_pt_mem().index(vaddr))
                            } else {
                                Option::None
                            };
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result } => {
                            let pte = if (self.interp_pt_mem().dom().contains(vaddr)) {
                                Some(self.interp_pt_mem().index(vaddr))
                            } else {
                                Option::None
                            };
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        _ => hlspec::AbstractArguments::Empty,
                    }
                },
        )
    }

    pub open spec fn interp(self, c: OSConstants) -> hlspec::AbstractVariables {
        let mappings: Map<nat, PageTableEntry> = self.effective_mappings();
        let mem: Map<nat, nat> = self.interp_vmem(c);
        let thread_state: Map<nat, hlspec::AbstractArguments> = self.interp_thread_state(c);
        let sound: bool = self.sound;
        hlspec::AbstractVariables { mem, mappings, thread_state, sound }
    }

    pub open spec fn interp_constants(self, c: OSConstants) -> hlspec::AbstractConstants {
        hlspec::AbstractConstants { thread_no: c.ULT_no, phys_mem_size: self.hw.mem.len() }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions for HL-soundness
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    candidate: PageTableEntry,
) -> bool {
    &&& exists|b: CoreState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                CoreState::MapWaiting { ULT_id, vaddr, pte } => {
                    overlap(candidate.frame, pte.frame)
                },
                CoreState::MapExecuting { ULT_id, vaddr, pte } => {
                    overlap(candidate.frame, pte.frame)
                },
                CoreState::UnmapWaiting { ULT_id, vaddr } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                CoreState::UnmapOpDone { ULT_id, vaddr, result } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                _ => { false },
            }
        }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate: PageTableEntry,
) -> bool {
    &&& exists|b: CoreState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                CoreState::MapWaiting { ULT_id, vaddr, pte } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                CoreState::MapExecuting { ULT_id, vaddr, pte } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                CoreState::UnmapWaiting { ULT_id, vaddr } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(
                        MemRegion { base: vaddr, size: pt.index(vaddr).frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(
                        MemRegion { base: vaddr, size: pt.index(vaddr).frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                CoreState::UnmapOpDone { ULT_id, vaddr, result } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(
                        MemRegion { base: vaddr, size: pt.index(vaddr).frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(
                        MemRegion { base: vaddr, size: pt.index(vaddr).frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                _ => { false },
            }
        }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// HW-Statemachine steps
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_HW(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    system_step: hardware::HWStep,
) -> bool {
    //enabling conditions
    &&& !(system_step is PTMemOp)
    //hw/spec_pt-statemachine steps

    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_sound(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& !candidate_mapping_overlaps_existing_pmem(pt, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(pt, inflightargs, pte)
    &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte)
}

pub open spec fn step_Map_enabled(
    pt_mem: mem::PageTableMemory,
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
    &&& pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_Map_Start(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] is Idle
    &&& step_Map_enabled(
        s1.hw.global_pt,
        vaddr,
        pte,
    )
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapWaiting { ULT_id, vaddr, pte })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound && step_Map_sound(
        hardware::interp_pt_mem(s1.hw.global_pt),
        s1.core_states.values(),
        vaddr,
        pte,
    )
}

pub open spec fn step_Map_op_Start(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::MapWaiting { ULT_id: ult_id, vaddr, pte }
    &&& ULT_id == ult_id
    &&& s1.kernel_lock(c) is None
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Map_Start(
        s1.pt_variables(),
        s2.pt_variables(),
        vaddr,
        pte,
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::MapExecuting { ULT_id, vaddr, pte },
    )
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    result: Result<(), ()>,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::MapExecuting { ULT_id: ult_id, vaddr, pte }
    &&& ULT_id == ult_id
    //hw/spec_pt-statemachine steps

    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Map_End(
        s1.pt_variables(),
        s2.pt_variables(),
        vaddr,
        pte,
        result,
    )
    //new state

    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap_Start(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    vaddr: nat,
) -> bool {
    let pt = hardware::interp_pt_mem(s1.hw.global_pt);
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] is Idle
    &&& step_Unmap_enabled(vaddr)
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapWaiting { ULT_id, vaddr })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound && (!pt.contains_key(vaddr) || step_Unmap_sound(
        hardware::interp_pt_mem(s1.hw.global_pt),
        s1.core_states.values(),
        vaddr,
        pt.index(vaddr),
    ))
}

pub open spec fn step_Unmap_Op_Start(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::UnmapWaiting { ULT_id: ult_id, vaddr }
    &&& ULT_id == ult_id
    &&& s1.kernel_lock(c) is None
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Unmap_Start(
        s1.pt_variables(),
        s2.pt_variables(),
        vaddr,
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapOpExecuting { ULT_id, vaddr })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    result: Result<(), ()>,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr }
    &&& ULT_id == ult_id
    //hw/spec_pt-statemachine steps

    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Unmap_End(
        s1.pt_variables(),
        s2.pt_variables(),
        vaddr,
        result,
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapOpDone { ULT_id, vaddr, result },
    )
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

//TODO dont do this operation if unmap resulted in error
pub open spec fn step_Unmap_Initiate_Shootdown(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, result }
    &&& ULT_id == ult_id
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, result },
    )
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: vaddr,
        open_requests: Set::new(|core: Core| hardware::valid_core_id(c.hw, core)),
    }
    &&& s2.sound == s1.sound
}

// Acknowledge TLB eviction to other core (in response to shootdown IPI)
//check if tlb shootdown/unmap has happend and send ACK
pub open spec fn step_Ack_Shootdown_IPI(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core_id(c.hw, core)  //not needed

    &&& s1.TLB_Shootdown.open_requests.contains(core)
    &&& !s1.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().contains(s1.TLB_Shootdown.vaddr)
    &&& !s1.interp_pt_mem().contains_key(
        s1.TLB_Shootdown.vaddr,
    )
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: s1.TLB_Shootdown.vaddr,
        open_requests: s1.TLB_Shootdown.open_requests.remove(core),
    }
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    result: Result<(), ()>,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    //enabling conditions
    &&& s1.core_states[core] matches CoreState::UnmapShootdownWaiting {
        ULT_id: ult_id,
        vaddr,
        result: Result,
    }
    &&& ULT_id == ult_id
    //TODO discuss this

    &&& result == Result
    &&& s1.TLB_Shootdown.open_requests.is_empty()
    //hw/spec_pt-statemachine steps

    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states.insert((core), CoreState::Idle)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Statemachine functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//TODO add new steps
#[allow(inconsistent_fields)]
pub enum OSStep {
    HW { ULT_id: nat, step: hardware::HWStep },
    //map
    MapStart { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    MapOpStart { ULT_id: nat },
    MapEnd { ULT_id: nat, result: Result<(), ()> },
    //unmap
    UnmapStart { ULT_id: nat, vaddr: nat },
    UnmapOpStart { ULT_id: nat },
    UnmapOpEnd { ULT_id: nat, result: Result<(), ()> },
    UnmapInitiateShootdown { ULT_id: nat },
    AckShootdownIPI { core: Core },
    UnmapEnd { ULT_id: nat, result: Result<(), ()> },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { ULT_id, step } => match step {
                hardware::HWStep::ReadWrite {
                    vaddr,
                    paddr,
                    op,
                    pte,
                    core,
                } => hlspec::AbstractStep::ReadWrite { thread_id: ULT_id, vaddr, op, pte },
                hardware::HWStep::PTMemOp => arbitrary(),
                hardware::HWStep::TLBFill { vaddr, pte, core } => hlspec::AbstractStep::Stutter,
                hardware::HWStep::TLBEvict { vaddr, core } => hlspec::AbstractStep::Stutter,
                //TODO discuss this
                hardware::HWStep::Stutter => hlspec::AbstractStep::Stutter,
            },
            //Map steps
            OSStep::MapStart { ULT_id, vaddr, pte } => {
                hlspec::AbstractStep::MapStart { thread_id: ULT_id, vaddr, pte }
            },
            OSStep::MapOpStart { ULT_id } => hlspec::AbstractStep::Stutter,
            OSStep::MapEnd { ULT_id, result } => {
                hlspec::AbstractStep::MapEnd { thread_id: ULT_id, result }
            },
            //Unmap steps
            OSStep::UnmapStart { ULT_id, vaddr } => {
                hlspec::AbstractStep::UnmapStart { thread_id: ULT_id, vaddr }
            },
            OSStep::UnmapOpStart { ULT_id } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapOpEnd { ULT_id, result } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapInitiateShootdown { ULT_id } => hlspec::AbstractStep::Stutter,
            OSStep::AckShootdownIPI { core } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapEnd { ULT_id, result } => {
                hlspec::AbstractStep::UnmapEnd { thread_id: ULT_id, result }
            },
        }
    }
}

pub open spec fn next_step(c: OSConstants, s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW { ULT_id, step } => step_HW(c, s1, s2, step),
        //Map steps
        OSStep::MapStart { ULT_id, vaddr, pte } => step_Map_Start(c, s1, s2, ULT_id, vaddr, pte),
        OSStep::MapOpStart { ULT_id } => step_Map_op_Start(c, s1, s2, ULT_id),
        OSStep::MapEnd { ULT_id, result } => step_Map_End(c, s1, s2, ULT_id, result),
        //Unmap steps
        OSStep::UnmapStart { ULT_id, vaddr } => step_Unmap_Start(c, s1, s2, ULT_id, vaddr),
        OSStep::UnmapOpStart { ULT_id } => step_Unmap_Op_Start(c, s1, s2, ULT_id),
        OSStep::UnmapOpEnd { ULT_id, result } => step_Unmap_Op_End(c, s1, s2, ULT_id, result),
        OSStep::UnmapInitiateShootdown { ULT_id } => step_Unmap_Initiate_Shootdown(
            c,
            s1,
            s2,
            ULT_id,
        ),
        OSStep::AckShootdownIPI { core } => step_Ack_Shootdown_IPI(c, s1, s2, core),
        OSStep::UnmapEnd { ULT_id, result } => step_Unmap_End(c, s1, s2, ULT_id, result),
    }
}

pub open spec fn next(c: OSConstants, s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(c, s1, s2, step)
}

pub open spec fn init(c: OSConstants, s: OSVariables) -> bool {
    // hardware stuff
    &&& hardware::interp_pt_mem(s.hw.global_pt) === Map::empty()
    &&& hardware::init(c.hw, s.hw)
    //spec_pt

    &&& spec_pt::init(s.pt_variables())
    //wf of ULT2core mapping

    &&& forall|id: nat| id <= c.ULT_no <==> c.ULT2core.contains_key(id)
    &&& forall|id: nat|
        id <= c.ULT_no ==> #[trigger] hardware::valid_core_id(
            c.hw,
            c.ULT2core.index(id),
        )
    //wf of shootdown

    &&& s.TLB_Shootdown.open_requests.is_empty()
}

} // verus!
