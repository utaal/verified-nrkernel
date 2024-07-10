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
    between, candidate_mapping_overlaps_existing_pmem, overlap, MemRegion, PageTableEntry,
    WORD_SIZE,
};
use crate::spec_t::hardware::{ Core, valid_core_id };

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
    pub core_state: Map<Core, OSArguments>,
    //TODO change to Map<core, Set<Core>>
    pub TLB_Shootdown: Map<(Core, Core), bool>,
    //Does not affect behaviour of os_specs, just set when operations with overlapping operations are used
    pub sound: bool,
    //TODO maybe have option<ULT_id:nat> instead
    pub lock: Option<Core>,
}

pub enum OSArguments {
    Map { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    Unmap { ULT_id: nat, vaddr: nat },
    Empty,
}

// MB: This is not necessarily complete and I didn't add the necessary fields
pub enum KCoreState {
    Idle,
    MapWaiting { },
    MapExecuting { },
    UnmapWaiting { },
    UnmapOpExecuting { },
    UnmapOpDone { },
    UnmapShootdownWaiting { },
}

impl KCoreState {
    pub open spec fn holds_lock(self) -> bool {
        match self {
            KCoreState::Idle | KCoreState::MapWaiting { .. } | KCoreState::UnmapWaiting { .. } => false,
            _ => true
        }
    }
}


impl OSVariables {
    pub open spec fn kernel_lock(self, consts: OSConstants) -> Option<Core> {
        // This should work if the core_state is KCoreState instead of OSArguments
        //if exists|c: Core| valid_core_id(consts.hw, c) && self.core_state[c].holds_lock() {
        //    Some(choose|c: Core| valid_core_id(consts.hw, c) && self.core_state[c].holds_lock())
        //} else {
        //    None
        //}
        None
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
                    match self.core_state[c.ULT2core[ult_id]] {
                        OSArguments::Map { ULT_id, vaddr, pte } => {
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Map { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        OSArguments::Unmap { ULT_id, vaddr } => {
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
    inflightargs: Set<OSArguments>,
    candidate: PageTableEntry,
) -> bool {
    &&& exists|b: OSArguments|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                OSArguments::Map { vaddr, pte, ULT_id } => { overlap(candidate.frame, pte.frame) },
                OSArguments::Unmap { vaddr, ULT_id } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                _ => { false },
            }
        }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<OSArguments>,
    base: nat,
    candidate: PageTableEntry,
) -> bool {
    &&& exists|b: OSArguments|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                OSArguments::Map { vaddr, pte, ULT_id } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    )
                },
                OSArguments::Unmap { vaddr, ULT_id } => {
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
    &&& !(system_step is PTMemOp)
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
    &&& s2.lock == s1.lock
    &&& s2.core_state == s1.core_state
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Acquire lock
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_set_lock(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    core: Core,
) -> bool {
    &&& s1.lock.is_none()
    &&& s1.core_state[core] is Map || s1.core_state[core] is Unmap
    &&& s2.lock == Some(core)
    &&& s2.core_state == s1.core_state
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Map_sound(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<OSArguments>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    &&& !candidate_mapping_overlaps_existing_pmem(pt, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(pt, inflightargs, pte)
    &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte)
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
    let os_arg = OSArguments::Map { ULT_id, vaddr, pte };
    &&& s1.core_state[core] is Empty
    &&& s2.core_state == s1.core_state.insert(core, os_arg)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Map_Start(s1.pt_variables(), s2.pt_variables(), vaddr, pte)
    &&& s2.lock == s1.lock
    &&& s2.sound == s1.sound && step_Map_sound(
        hardware::interp_pt_mem(s1.hw.global_pt),
        s1.core_state.values(),
        vaddr,
        pte,
    )
}

pub open spec fn step_Map_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    result: Result<(), ()>,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    &&& s1.core_state[core] matches OSArguments::Map { ULT_id: ult_id, vaddr, pte }
    &&& s2.core_state == s1.core_state.insert(core, OSArguments::Empty)
    &&& ULT_id == ult_id
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& spec_pt::step_Map_End(s1.pt_variables(), s2.pt_variables(), vaddr, pte, result)
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw)
    &&& s1.sound == s2.sound
    &&& s1.lock == Some(core)
    &&& s2.lock.is_none()
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<OSArguments>,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte)
}

pub open spec fn step_UnmapOp_Start(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    vaddr: nat,
) -> bool {
    let pt = hardware::interp_pt_mem(s1.hw.global_pt);
    let core = c.ULT2core.index(ULT_id);
    let os_arg = OSArguments::Unmap { ULT_id, vaddr };
    &&& s1.core_state[core] is Empty
    &&& s2.core_state == s1.core_state.insert(core, os_arg)
    &&& s2.hw
        == s1.hw
    //NR shootsdown all cores that run the same process -> entire shootdown row is set true at beginning of shootdown

    &&& forall|handler: Core| #[trigger]
        hardware::valid_core_id(c.hw, handler) ==> s2.TLB_Shootdown[(core, handler)]
    &&& forall|dispatcher: Core, handler: Core|
        hardware::valid_core_id(c.hw, handler) && hardware::valid_core_id(c.hw, dispatcher) && (
        dispatcher !== core) ==> s2.TLB_Shootdown[(dispatcher, handler)]
            === #[trigger] s1.TLB_Shootdown[(dispatcher, handler)]
    &&& s2.TLB_Shootdown.dom() === s1.TLB_Shootdown.dom()
    &&& s2.sound == s1.sound && (!pt.contains_key(vaddr) || step_Unmap_sound(
        hardware::interp_pt_mem(s1.hw.global_pt),
        s1.core_state.values(),
        vaddr,
        pt.index(vaddr),
    ))
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Unmap_Start(s1.pt_variables(), s2.pt_variables(), vaddr)
    &&& s2.lock == s1.lock
}

pub open spec fn step_UnmapOp_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    result: Result<(), ()>,
    ULT_id: nat,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    &&& s1.core_state[core] matches OSArguments::Unmap { ULT_id: ult_id, vaddr }
    &&& ULT_id == ult_id
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.core_state == s1.core_state
    &&& spec_pt::step_Unmap_End(s1.pt_variables(), s2.pt_variables(), vaddr, result)
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw)
    &&& s2.sound == s1.sound
    &&& s1.lock == Some(core)
    &&& s2.lock == s1.lock
}

pub open spec fn step_Unmap_Initiate_Shootdown(/* ... */) -> bool {
    /* ... */
    true
}

// Acknowledge TLB eviction to other core (in response to shootdown IPI)
pub open spec fn step_Ack_Shootdown_IPI(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    core: Core,
    dispatcher: Core,
) -> bool {
    &&& s1.core_state[dispatcher] matches OSArguments::Unmap { ULT_id: ult_id, vaddr }
    &&& !s1.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().contains(vaddr)
    &&& hardware::valid_core_id(c.hw, core)
    &&& hardware::valid_core_id(c.hw, dispatcher)
    &&& !(s1.core_state[core] is Map && s1.lock == Some(core))
    &&& s2.core_state
        == s1.core_state
    //check if tlb shootdown has happend and send ACK

    &&& !s1.interp_pt_mem().contains_key(vaddr)
    &&& s1.TLB_Shootdown[(dispatcher, core)]
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown.insert((dispatcher, core), false)
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
    &&& s2.sound == s1.sound
    &&& s2.lock == s1.lock
}

pub open spec fn step_Unmap_End(
    c: OSConstants,
    s1: OSVariables,
    s2: OSVariables,
    ULT_id: nat,
    result: Result<(), ()>,
) -> bool {
    let core = c.ULT2core.index(ULT_id);
    &&& s1.core_state[core] matches OSArguments::Unmap { ULT_id: ult_id, vaddr }
    &&& ULT_id == ult_id
    &&& forall|id: Core| #[trigger]
        hardware::valid_core_id(c.hw, id) ==> !s1.TLB_Shootdown[(core, id)]
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& s2.core_state == s1.core_state.insert((core), OSArguments::Empty)
    &&& s1.sound == s2.sound
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
    &&& s1.lock == Some(core)
    &&& s2.lock.is_none()
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Statemachine functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[allow(inconsistent_fields)]
pub enum OSStep {
    HW { ULT_id: nat, step: hardware::HWStep },
    MapStart { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    MapEnd { ULT_id: nat, result: Result<(), ()> },
    UnmapStart { ULT_id: nat, vaddr: nat },
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
            OSStep::MapStart { ULT_id, vaddr, pte } => {
                hlspec::AbstractStep::MapStart { thread_id: ULT_id, vaddr, pte }
            },
            OSStep::MapEnd { ULT_id, result } => {
                hlspec::AbstractStep::MapEnd { thread_id: ULT_id, result }
            },
            OSStep::UnmapStart { ULT_id, vaddr } => {
                hlspec::AbstractStep::UnmapStart { thread_id: ULT_id, vaddr }
            },
            OSStep::UnmapEnd { ULT_id, result } => {
                hlspec::AbstractStep::UnmapEnd { thread_id: ULT_id, result }
            },
        }
    }
}

pub open spec fn next_step(c: OSConstants, s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW { ULT_id, step } => step_HW(c, s1, s2, step),
        OSStep::MapStart { ULT_id, vaddr, pte } => step_Map_Start(c, s1, s2, ULT_id, vaddr, pte),
        OSStep::MapEnd { ULT_id, result } => step_Map_End(c, s1, s2, ULT_id, result),
        OSStep::UnmapStart { ULT_id, vaddr } => step_UnmapOp_Start(c, s1, s2, ULT_id, vaddr),
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
    //wf of ULT2core mapping

    &&& forall|id: nat| id <= c.ULT_no <==> c.ULT2core.contains_key(id)
    &&& forall|id: nat|
        id <= c.ULT_no ==> #[trigger] hardware::valid_core_id(
            c.hw,
            c.ULT2core.index(id),
        )
    //wf of shootdown

    &&& forall|dispatcher: Core, handler: Core|
        hardware::valid_core_id(c.hw, dispatcher) && hardware::valid_core_id(c.hw, handler)
            <==> #[trigger] s.TLB_Shootdown.dom().contains((dispatcher, handler))
    &&& forall|dispatcher: Core, handler: Core|
        #![auto]
        hardware::valid_core_id(c.hw, dispatcher) && hardware::valid_core_id(c.hw, handler)
            ==> !s.TLB_Shootdown[(dispatcher, handler)]
        //spec_pt

    &&& spec_pt::init(s.pt_variables())
}

} // verus!
