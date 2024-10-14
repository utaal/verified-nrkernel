#![verus::trusted]
// trusted:
// describes how the whole system behaves
//
// this refers to definitions in an untrusted file, but uses them in a way that the
// state-machine refinement can check

use vstd::prelude::*;

//use crate::impl_u::spec_pt;
use crate::spec_t::{hardware, hlspec, mem, mmu};
use crate::definitions_t::{
    above_zero, aligned, between, candidate_mapping_in_bounds,
    candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem, overlap,
    x86_arch_spec, HWLoadResult, HWRWOp, HWStoreResult, LoadResult, MemRegion, PageTableEntry,
    RWOp, StoreResult, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR, WORD_SIZE, Core,
};
use crate::extra::result_map_ok;

verus! {

pub struct OSConstants {
    pub hw: hardware::HWConstants,
    //maps User Level Thread to its assigned core
    pub ULT2core: Map<nat, Core>,
    //highest thread_id
    pub ULT_no: nat,
}

pub struct OSVariables<M: mmu::MMU> {
    pub hw: hardware::HWVariables<M>,
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

#[allow(inconsistent_fields)]
pub enum CoreState {
    Idle,
    MapWaiting { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    MapExecuting { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    UnmapWaiting { ULT_id: nat, vaddr: nat },
    UnmapOpExecuting { ULT_id: nat, vaddr: nat, result: Option<Result<PageTableEntry, ()>> },
    UnmapOpDone { ULT_id: nat, vaddr: nat, result: Result<PageTableEntry, ()> },
    UnmapShootdownWaiting {
        ULT_id: nat,
        vaddr: nat,
        result: Result<PageTableEntry, ()>,
    },
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

    pub open spec fn is_idle(self) -> bool {
        self is Idle
    }

    pub open spec fn vmem_pte_size(self, pt: Map<nat, PageTableEntry>) -> nat
        recommends
            !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { pte, .. } | CoreState::MapExecuting { pte, .. } => {
                pte.frame.size
            },
            CoreState::UnmapWaiting { vaddr, .. } | CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
                if pt.contains_key(vaddr) {
                    pt[vaddr].frame.size
                } else {
                    0
                }
            },
            CoreState::UnmapOpExecuting { result: Some(result), .. }
            | CoreState::UnmapOpDone { result, .. }
            | CoreState::UnmapShootdownWaiting { result, .. } => {
                if result is Ok {
                    result.get_Ok_0().frame.size
                } else {
                    0
                }
            },
            CoreState::Idle => arbitrary(),
        }
    }

    pub open spec fn vaddr(self) -> nat
        recommends
            !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { vaddr, .. }
            | CoreState::MapExecuting { vaddr, .. }
            | CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapOpExecuting { vaddr, .. }
            | CoreState::UnmapOpDone { vaddr, .. }
            | CoreState::UnmapShootdownWaiting { vaddr, .. } => { vaddr },
            CoreState::Idle => arbitrary(),
        }
    }
}

impl OSConstants {
    pub open spec fn valid_ULT(self, ULT_id: nat) -> bool {
        ULT_id < self.ULT_no
    }

    pub open spec fn interp(self) -> hlspec::AbstractConstants {
        hlspec::AbstractConstants { thread_no: self.ULT_no, phys_mem_size: self.hw.phys_mem_size }
    }
}

impl<M: mmu::MMU> OSVariables<M> {
    pub open spec fn kernel_lock(self, consts: OSConstants) -> Option<Core> {
        if exists|c: Core|
            hardware::valid_core(consts.hw, c) && (#[trigger] self.core_states[c].holds_lock()) {
            Some(
                choose|c: Core|
                    hardware::valid_core(consts.hw, c) && (
                    #[trigger] self.core_states[c].holds_lock()),
            )
        } else {
            None
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant and WF
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn valid_ids(self, c: OSConstants) -> bool {
        forall|core: Core|
            hardware::valid_core(c.hw, core) ==> match self.core_states[core] {
                CoreState::MapWaiting { ULT_id, .. }
                | CoreState::MapExecuting { ULT_id, .. }
                | CoreState::UnmapWaiting { ULT_id, .. }
                | CoreState::UnmapOpExecuting { ULT_id, .. }
                | CoreState::UnmapOpDone { ULT_id, .. }
                | CoreState::UnmapShootdownWaiting { ULT_id, .. } => {
                    &&& c.valid_ULT(ULT_id)
                    &&& c.ULT2core[ULT_id] === core
                },
                CoreState::Idle => true,
            }
    }

    pub open spec fn inflight_pte_above_zero_pte_result_consistant(self, c: OSConstants) -> bool {
        forall|core: Core|
            {
                hardware::valid_core(c.hw, core) ==> match self.core_states[core] {
                    CoreState::MapWaiting { vaddr, pte, .. }
                    | CoreState::MapExecuting { vaddr, pte, .. } => { above_zero(pte.frame.size) },
                    CoreState::UnmapWaiting { vaddr, .. }
                    | CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
                        self.interp_pt_mem().dom().contains(vaddr) ==> above_zero(
                            self.interp_pt_mem()[vaddr].frame.size,
                        )
                    }
                    CoreState::UnmapOpExecuting { result: Some(result), .. }
                    | CoreState::UnmapOpDone { result, .. }
                    | CoreState::UnmapShootdownWaiting { result, .. } => {
                        result is Ok ==> above_zero(result.get_Ok_0().frame.size)
                    },
                    CoreState::Idle => { true },
                }
            }
    }

    pub open spec fn successful_unmaps(self, c: OSConstants) -> bool {
        forall|core: Core|
            {
                hardware::valid_core(c.hw, core) ==> match self.core_states[core] {
                    CoreState::UnmapOpExecuting { vaddr, result: Some(_), .. }
                    | CoreState::UnmapOpDone { vaddr, .. }
                    | CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                        !self.interp_pt_mem().dom().contains(vaddr)
                    },
                    _ => { true },
                }
            }
    }

    pub open spec fn wf(self, c: OSConstants) -> bool {
        &&& forall|id: nat| #[trigger] c.valid_ULT(id) <==> c.ULT2core.contains_key(id)
        &&& forall|id: nat|
            c.valid_ULT(id) ==> #[trigger] hardware::valid_core(c.hw, c.ULT2core[id])
        &&& forall|core: Core|
            hardware::valid_core(c.hw, core) <==> #[trigger] self.core_states.contains_key(core)
        &&& forall|core1: Core, core2: Core|
            (hardware::valid_core(c.hw, core1) && #[trigger] self.core_states[core1].holds_lock()
                && #[trigger] hardware::valid_core(c.hw, core2)
                && self.core_states[core2].holds_lock()) ==> core1 === core2
    }

    pub open spec fn basic_inv(self, c: OSConstants) -> bool {
        &&& self.wf(c)
        &&& self.valid_ids(c)
        &&& self.inflight_pte_above_zero_pte_result_consistant(c)
        &&& self.successful_unmaps(c)
        //&&& self.tlb_inv(c)

    }

    pub open spec fn inv(self, c: OSConstants) -> bool {
        &&& self.basic_inv(c)
        //&&& self.tlb_inv(c)
        //&&& self.overlapping_inv(c)
        &&& self.overlapping_vmem_inv(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about the TLB
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn shootdown_cores_valid(self, c: OSConstants) -> bool {
        forall|core| #[trigger]
            self.TLB_Shootdown.open_requests.contains(core) ==> hardware::valid_core(c.hw, core)
    }

    pub open spec fn successful_IPI(self, c: OSConstants) -> bool {
        forall|dispatcher: Core|
            {
                hardware::valid_core(c.hw, dispatcher) ==> match self.core_states[dispatcher] {
                    CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                        forall|handler: Core|
                            !(#[trigger] self.TLB_Shootdown.open_requests.contains(handler))
                                ==> !self.hw.NUMAs[handler.NUMA_id].cores[handler.core_id].tlb.dom().contains(
                            vaddr)
                    },
                    _ => true,
                }
            }
    }

    //returns set with the vaddr that is currently unmapped.
    pub open spec fn Unmap_vaddr(self) -> Set<nat> {
        Set::new(
            |v_address: nat|
                {
                    &&& exists|core: Core|
                        self.core_states.dom().contains(core) && match self.core_states[core] {
                            CoreState::UnmapOpDone { vaddr, result, .. }
                            | CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                                (result is Ok) && (vaddr === v_address)
                            },
                            _ => false,
                        }
                },
        )
    }

    pub open spec fn TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(self, c: OSConstants) -> bool {
        forall|core: Core|
            {
                #[trigger] hardware::valid_core(c.hw, core)
                    ==> self.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().subset_of(
                    self.interp_pt_mem().dom().union(self.Unmap_vaddr()),
                )
            }
    }

    pub open spec fn shootdown_exists(self, c: OSConstants) -> bool {
        !(self.TLB_Shootdown.open_requests === Set::<Core>::empty()) ==> exists|core|
            hardware::valid_core(c.hw, core)
                && self.core_states[core] matches (CoreState::UnmapShootdownWaiting { vaddr, .. })
    }

    pub open spec fn tlb_inv(self, c: OSConstants) -> bool {
        &&& self.shootdown_cores_valid(c)
        &&& self.successful_IPI(c)
        &&& self.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about overlapping
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn set_core_idle(self, c: OSConstants, core: Core) -> OSVariables<M>
        recommends
            hardware::valid_core(c.hw, core),
    {
        OSVariables {
            hw: self.hw,
            core_states: self.core_states.insert(core, CoreState::Idle),
            TLB_Shootdown: self.TLB_Shootdown,
            sound: self.sound,
        }
    }

    pub open spec fn inflight_map_no_overlap_inflight_vmem(self, c: OSConstants) -> bool {
        forall|core1: Core, core2: Core|
            (hardware::valid_core(c.hw, core1) && hardware::valid_core(c.hw, core2)
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

    pub open spec fn existing_map_no_overlap_existing_vmem(self, c: OSConstants) -> bool {
        forall|vaddr| #[trigger]
            self.interp_pt_mem().dom().contains(vaddr)
                ==> !candidate_mapping_overlaps_existing_vmem(
                self.interp_pt_mem().remove(vaddr),
                vaddr,
                self.interp_pt_mem()[vaddr],
            )
    }

    pub open spec fn overlapping_vmem_inv(self, c: OSConstants) -> bool {
        self.sound ==> {
            &&& self.inflight_map_no_overlap_inflight_vmem(c)
            &&& self.existing_map_no_overlap_existing_vmem(c)
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Interpretation functions
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //pub open spec fn pt_variables(self, core: Core) -> spec_pt::PageTableVariables {
    //    spec_pt::PageTableVariables {
    //        pt_mem: self.hw.global_pt,
    //        thread_state: match self.core_states[core] {
    //            CoreState::MapExecuting { .. } => spec_pt::ThreadState::Mapping,
    //            CoreState::UnmapOpExecuting { result, .. } => spec_pt::ThreadState::Unmapping { result },
    //            _ => spec_pt::ThreadState::Idle,
    //        },
    //    }
    //}

    pub open spec fn interp_pt_mem(self) -> Map<nat, PageTableEntry> {
        hardware::interp_pt_mem(self.hw.mmu.pt_mem())
    }

    pub open spec fn inflight_unmap_vaddr(self) -> Set<nat> {
        Set::new(
            |v_address: nat|
                {
                    &&& self.interp_pt_mem().dom().contains(v_address)
                    &&& exists|core: Core|
                        self.core_states.dom().contains(core) && match self.core_states[core] {
                            CoreState::UnmapWaiting { ULT_id, vaddr }
                            | CoreState::UnmapOpExecuting { ULT_id, vaddr, .. }
                            | CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                            | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                                vaddr === v_address
                            },
                            _ => false,
                        }
                },
        )
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PageTableEntry> {
        let effective_mappings = self.interp_pt_mem();
        let unmap_dom = self.inflight_unmap_vaddr();
        Map::new(
            |vmem_idx: nat|
                effective_mappings.dom().contains(vmem_idx) && !unmap_dom.contains(vmem_idx),
            |vmem_idx: nat| effective_mappings[vmem_idx],
        )
    }

    pub open spec fn interp_vmem(self, c: OSConstants) -> Map<nat, nat> {
        let phys_mem_size = c.interp().phys_mem_size;
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
            |ult_id: nat| c.valid_ULT(ult_id),
            |ult_id: nat|
                {
                    match self.core_states[c.ULT2core[ult_id]] {
                        CoreState::MapWaiting { ULT_id, vaddr, pte }
                        | CoreState::MapExecuting { ULT_id, vaddr, pte } => {
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Map { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapWaiting { ULT_id, vaddr }
                        | CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None } => {
                            let pte = if self.interp_pt_mem().dom().contains(vaddr) {
                                Some(self.interp_pt_mem()[vaddr])
                            } else {
                                None
                            };
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(result) }
                        | CoreState::UnmapOpDone { ULT_id, vaddr, result }
                        | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result } => {
                            if ULT_id == ult_id {
                                hlspec::AbstractArguments::Unmap { vaddr, pte:
                                    match result {
                                        Ok(pte) => Some(pte),
                                        Err(_) => None,
                                    }
                                }
                            } else {
                                hlspec::AbstractArguments::Empty
                            }
                        },
                        CoreState::Idle => hlspec::AbstractArguments::Empty,
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
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions for HL-soundness
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    candidate: PageTableEntry,
) -> bool {
    exists|b: CoreState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. } => {
                    overlap(candidate.frame, pte.frame)
                },
                CoreState::UnmapWaiting { ULT_id, vaddr }
                | CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None, .. } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt[vaddr].frame)
                },
                CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(result), .. }
                | CoreState::UnmapOpDone { ULT_id, vaddr, result, .. }
                | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result, .. } => {
                    &&& result is Ok
                    &&& overlap(candidate.frame, result.get_Ok_0().frame)
                },
                CoreState::Idle => false,
            }
        }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PageTableEntry>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    exists|b: CoreState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                CoreState::UnmapWaiting { vaddr, .. }
                | CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
                    let size = if pt.dom().contains(vaddr) {
                        pt[vaddr].frame.size
                    } else {
                        0
                    };
                    overlap(
                        MemRegion { base: vaddr, size: size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                CoreState::UnmapOpExecuting { vaddr, result: Some(result), .. }
                | CoreState::UnmapOpDone { vaddr, result, .. }
                | CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                    let size = if result is Ok {
                        result.get_Ok_0().frame.size
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

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// HW-Statemachine steps
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_HW<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    ULT_id: nat,
    system_step: hardware::HWStep,
) -> bool {
    let core = c.ULT2core[ULT_id];
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
        || system_step is TLBFill
        || system_step is TLBEvict
        || (system_step matches hardware::HWStep::MMUStep { lbl: mmu::Lbl::Tau })
    &&& !(system_step is Stutter)
    //hw/spec_pt-statemachine steps
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
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
    &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte.frame.size)
}

pub open spec fn step_Map_enabled(
    //pt_mem: mem::PageTableMemory,
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
    //&&& pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_Map_Start<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    ULT_id: nat,
    vaddr: nat,
    pte: PageTableEntry,
) -> bool {
    let core = c.ULT2core[ULT_id];
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
    &&& step_Map_enabled(
        //s1.hw.global_pt,
        vaddr,
        pte,
    )
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapWaiting { ULT_id, vaddr, pte })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound && step_Map_sound(
        s1.interp_pt_mem(),
        //TODO reallllllly think about this
        s1.core_states.values(),
        vaddr,
        pte,
    )
}

pub open spec fn step_Map_op_Start<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::MapWaiting { ULT_id, vaddr, pte }
    &&& s1.kernel_lock(c) is None
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Map_Start(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //    vaddr,
    //    pte,
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::MapExecuting { ULT_id, vaddr, pte },
    )
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_op_Stutter<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
    addr: usize,
    value: usize,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] is MapExecuting
    //hw/spec_pt-statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, addr, value))
    &&& arbitrary()
    //&&& spec_pt::step_Map_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_End<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
    addr: usize,
    value: usize,
    result: Result<(), ()>,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::MapExecuting {
        ULT_id,
        vaddr,
        pte,
    }
    //hw/spec_pt-statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, addr, value))
    &&& arbitrary()
    //&&& spec_pt::step_Map_End(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //    vaddr,
    //    pte,
    //    result,
    //)
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
    pte_size: nat,
) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& {  // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_Unmap_Start<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    ULT_id: nat,
    vaddr: nat,
) -> bool {
    let pt = s1.interp_pt_mem();
    let core = c.ULT2core[ULT_id];
    let pte_size = if pt.contains_key(vaddr) {
        pt[vaddr].frame.size
    } else {
        0
    };
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
    &&& step_Unmap_enabled(vaddr)
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapWaiting { ULT_id, vaddr })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound && step_Unmap_sound(
        pt,
        s1.core_states.values(),
        vaddr,
        pte_size,
    )
}

pub open spec fn step_Unmap_Op_Start<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapWaiting { ULT_id, vaddr }
    &&& s1.kernel_lock(c) is None
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Unmap_Start(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //    vaddr,
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_Change<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
    addr: usize,
    value: usize,
    result: Result<PageTableEntry, ()>,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting {
        ULT_id,
        vaddr,
        result: None
    }
    //hw/spec_pt-statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, addr, value))
    &&& arbitrary()
    //&&& spec_pt::step_Unmap_Change(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //    vaddr,
    //    result
    //)
    //new state
    &&& if result is Ok {
        s2.core_states == s1.core_states.insert(
            core,
            CoreState::UnmapOpExecuting {
                ULT_id,
                vaddr,
                result: Some(Ok(s1.interp_pt_mem()[vaddr])),
            },
        )
    } else {
        s2.core_states == s1.core_states.insert(
            core,
            CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(Err(())) },
        )
    }
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_Stutter<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
    addr: usize,
    value: usize,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting {
        ULT_id,
        vaddr,
        result: Some(res)
    }
    //hw/spec_pt-statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, addr, value))
    &&& arbitrary()
    //&&& spec_pt::step_Unmap_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_End<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting {
        ULT_id,
        vaddr,
        result: Some(res)
    }
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Unmap_End(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapOpDone { ULT_id, vaddr, result: res },
    )
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Initiate_Shootdown<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, result }
    &&& result is Ok
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, result },
    )
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: vaddr,
        open_requests: Set::new(|core: Core| hardware::valid_core(c.hw, core)),
    }
    &&& s2.sound == s1.sound
}

// Acknowledge TLB eviction to other core (in response to shootdown IPI)
//check if tlb shootdown/unmap has happend and send ACK
pub open spec fn step_Ack_Shootdown_IPI<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    //TODO discuss: only valid cores are in the open_requests
    &&& s1.TLB_Shootdown.open_requests.contains(core)
    &&& !s1.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().contains(s1.TLB_Shootdown.vaddr)
    // TODO: Why do we have this enabling condition?
    &&& !s1.interp_pt_mem().contains_key(
        s1.TLB_Shootdown.vaddr,
    )
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: s1.TLB_Shootdown.vaddr,
        open_requests: s1.TLB_Shootdown.open_requests.remove(core),
    }
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_End<M: mmu::MMU>(
    c: OSConstants,
    s1: OSVariables<M>,
    s2: OSVariables<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& match s1.core_states[core] {
        CoreState::UnmapShootdownWaiting { result, ULT_id, .. } => {
            s1.TLB_Shootdown.open_requests.is_empty()
        },
        CoreState::UnmapOpDone { result, ULT_id, .. } => { result is Err },
        _ => false,
    }
    //hw/spec_pt-statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    &&& arbitrary()
    //&&& spec_pt::step_Stutter(
    //    s1.pt_variables(core),
    //    s2.pt_variables(core),
    //)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Statemachine functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[allow(inconsistent_fields)]
pub enum OSStep {
    HW { ULT_id: nat, step: hardware::HWStep },
    //map
    MapStart { ULT_id: nat, vaddr: nat, pte: PageTableEntry },
    MapOpStart { core: Core },
    MapOpStutter { core: Core, addr: usize, value: usize },
    MapEnd { core: Core, addr: usize, value: usize, result: Result<(), ()> },
    //unmap
    UnmapStart { ULT_id: nat, vaddr: nat },
    UnmapOpStart { core: Core },
    UnmapOpChange { core: Core, addr: usize, value: usize, result: Result<PageTableEntry, ()> },
    UnmapOpStutter { core: Core, addr: usize, value: usize },
    UnmapOpEnd { core: Core },
    UnmapInitiateShootdown { core: Core },
    AckShootdownIPI { core: Core },
    UnmapEnd { core: Core },
}

//TODO simplify this
impl OSStep {
    pub open spec fn interp<M: mmu::MMU>(self, c: OSConstants, s: OSVariables<M>) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { ULT_id, step } => match step {
                hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, core } => {
                    let hl_pte = if pte is None || (pte matches Some((base, _))
                        && !s.effective_mappings().dom().contains(base)) {
                        None
                    } else {
                        pte
                    };
                    let rwop = match (op, hl_pte) {
                        (
                            HWRWOp::Store { new_value, result: HWStoreResult::Ok },
                            Some(_),
                        ) => RWOp::Store { new_value, result: StoreResult::Ok },
                        (
                            HWRWOp::Store { new_value, result: HWStoreResult::Ok },
                            None,
                        ) => RWOp::Store { new_value, result: StoreResult::Undefined },
                        (
                            HWRWOp::Store { new_value, result: HWStoreResult::Pagefault },
                            _,
                        ) => RWOp::Store { new_value, result: StoreResult::Undefined },
                        (
                            HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) },
                            Some(_),
                        ) => RWOp::Load { is_exec, result: LoadResult::Value(v) },
                        (
                            HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) },
                            None,
                        ) => RWOp::Load { is_exec, result: LoadResult::Undefined },
                        (
                            HWRWOp::Load { is_exec, result: HWLoadResult::Pagefault },
                            _,
                        ) => RWOp::Load { is_exec, result: LoadResult::Undefined },
                    };
                    hlspec::AbstractStep::ReadWrite {
                        thread_id: ULT_id,
                        vaddr,
                        op: rwop,
                        pte: hl_pte,
                    }
                },
                hardware::HWStep::TLBFill { vaddr, pte, core } => hlspec::AbstractStep::Stutter,
                hardware::HWStep::TLBEvict { vaddr, core } => hlspec::AbstractStep::Stutter,
                hardware::HWStep::Stutter => arbitrary(),
                hardware::HWStep::MMUStep { lbl } => arbitrary(),
            },
            //Map steps
            OSStep::MapStart { ULT_id, vaddr, pte } => {
                hlspec::AbstractStep::MapStart { thread_id: ULT_id, vaddr, pte }
            },
            OSStep::MapOpStart { .. } => hlspec::AbstractStep::Stutter,
            OSStep::MapOpStutter { .. } => hlspec::AbstractStep::Stutter,
            OSStep::MapEnd { core, result, addr, value } => {
                match s.core_states[core] {
                    CoreState::MapExecuting { ULT_id, .. } => {
                        hlspec::AbstractStep::MapEnd { thread_id: ULT_id, result }
                    },
                    _ => { arbitrary() },
                }
            },
            //Unmap steps
            OSStep::UnmapStart { ULT_id, vaddr } => {
                hlspec::AbstractStep::UnmapStart { thread_id: ULT_id, vaddr }
            },
            OSStep::UnmapOpStart { .. } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapOpChange { .. } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapOpStutter { .. } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapOpEnd { .. } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapInitiateShootdown { .. } => hlspec::AbstractStep::Stutter,
            OSStep::AckShootdownIPI { .. } => hlspec::AbstractStep::Stutter,
            OSStep::UnmapEnd { core } => {
                match s.core_states[core] {
                    CoreState::UnmapShootdownWaiting { result, ULT_id, .. } => {
                        hlspec::AbstractStep::UnmapEnd { thread_id: ULT_id, result: result_map_ok(result, |r| ()) }
                    },
                    CoreState::UnmapOpDone { result, ULT_id, .. } => {
                        hlspec::AbstractStep::UnmapEnd { thread_id: ULT_id, result: result_map_ok(result, |r| ()) }
                    },
                    _ => arbitrary(),
                }
            },
        }
    }
}

pub open spec fn next_step<M: mmu::MMU>(c: OSConstants, s1: OSVariables<M>, s2: OSVariables<M>, step: OSStep) -> bool {
    match step {
        OSStep::HW { ULT_id, step }                         => step_HW(c, s1, s2, ULT_id, step),
        //Map steps
        OSStep::MapStart { ULT_id, vaddr, pte }             => step_Map_Start(c, s1, s2, ULT_id, vaddr, pte),
        OSStep::MapOpStart { core }                         => step_Map_op_Start(c, s1, s2, core),
        OSStep::MapOpStutter { core, addr, value }          => step_Map_op_Stutter(c, s1, s2, core, addr, value),
        OSStep::MapEnd { core, addr, value, result }        => step_Map_End(c, s1, s2, core, addr, value, result),
        //Unmap steps
        OSStep::UnmapStart { ULT_id, vaddr }                => step_Unmap_Start(c, s1, s2, ULT_id, vaddr),
        OSStep::UnmapOpStart { core }                       => step_Unmap_Op_Start(c, s1, s2, core),
        OSStep::UnmapOpChange { core, addr, value, result } => step_Unmap_Op_Change(c, s1, s2, core, addr, value, result),
        OSStep::UnmapOpStutter { core, addr, value }        => step_Unmap_Op_Stutter(c, s1, s2, core, addr, value),
        OSStep::UnmapOpEnd { core }                         => step_Unmap_Op_End(c, s1, s2, core),
        OSStep::UnmapInitiateShootdown { core }             => step_Unmap_Initiate_Shootdown(c, s1, s2, core),
        OSStep::AckShootdownIPI { core }                    => step_Ack_Shootdown_IPI(c, s1, s2, core),
        OSStep::UnmapEnd { core }                           => step_Unmap_End(c, s1, s2, core),
    }
}

pub open spec fn next<M: mmu::MMU>(c: OSConstants, s1: OSVariables<M>, s2: OSVariables<M>) -> bool {
    exists|step: OSStep| next_step(c, s1, s2, step)
}

pub open spec fn init<M: mmu::MMU>(c: OSConstants, s: OSVariables<M>) -> bool {
    // hardware stuff
    &&& s.interp_pt_mem() === Map::empty()
    &&& hardware::init(c.hw, s.hw)
    //spec_pt
    &&& arbitrary()
    //&&& forall|core: Core| #[trigger] hardware::valid_core(c.hw, core) ==> spec_pt::init(s.pt_variables(core))
    //wf of ULT2core mapping
    &&& forall|id: nat| #[trigger] c.valid_ULT(id) <==> c.ULT2core.contains_key(id)
    &&& forall|id: nat|
        c.valid_ULT(id) ==> #[trigger] hardware::valid_core(
            c.hw,
            c.ULT2core[id],
        )
    //core_state
    &&& forall|core: Core|
        hardware::valid_core(c.hw, core) <==> #[trigger] s.core_states.contains_key(core)
    &&& forall|core: Core| #[trigger]
        hardware::valid_core(c.hw, core) ==> s.core_states[core]
            === CoreState::Idle
        //shootdown
    &&& s.TLB_Shootdown.open_requests === Set::empty()
    //sound
    &&& s.sound
}

} // verus!
