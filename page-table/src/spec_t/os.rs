#![verus::trusted]
// trusted:
// describes how the whole system behaves
//
// this refers to definitions in an untrusted file, but uses them in a way that the
// state-machine refinement can check

use vstd::prelude::*;

use crate::spec_t::{hardware, hlspec, mem, mmu};
use crate::spec_t::mmu::{WalkResult, pt_mem};
use crate::definitions_t::{
    aligned, between, candidate_mapping_in_bounds,
    candidate_mapping_overlaps_existing_pmem, candidate_mapping_overlaps_existing_vmem, overlap,
    x86_arch_spec, HWLoadResult, HWRWOp, HWStoreResult, LoadResult, MemRegion, PTE,
    RWOp, StoreResult, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MAX_PHYADDR, WORD_SIZE, Core,
};
use crate::extra::result_map_ok;

verus! {

pub struct Constants {
    pub hw: hardware::Constants,
    //maps User Level Thread to its assigned core
    pub ULT2core: Map<nat, Core>,
    //highest thread_id
    pub ULT_no: nat,
}

pub struct State<M: mmu::MMU> {
    pub hw: hardware::State<M>,
    // maps numa node to ULT operation spinning/operating on it
    pub core_states: Map<Core, CoreState>,
    pub TLB_Shootdown: ShootdownVector,
    /// We track a simple view of the page table memory here, which changes everytime we do a write
    /// transition in the MMU. This memory view is used for two things:
    /// - Determining the `sound` history variable
    /// - Encoding the desired semantics of the implementation, e.g. Map_End has to change the
    ///   memory such that the interpretation contains a new entry.
    pub pt_mem: pt_mem::PTMem,
    // history variables: writes, neg_writes
    // TODO: invariant: No core holds lock ==> writes is empty && neg_writes is empty for all cores
    //                  (and some aux inv to prove it, where shootdown acked ==> neg_writes empty
    //                  for that core)
    //
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
    MapWaiting { ULT_id: nat, vaddr: nat, pte: PTE },
    MapExecuting { ULT_id: nat, vaddr: nat, pte: PTE },
    UnmapWaiting { ULT_id: nat, vaddr: nat },
    UnmapOpExecuting { ULT_id: nat, vaddr: nat, result: Option<Result<PTE, ()>> },
    UnmapOpDone { ULT_id: nat, vaddr: nat, result: Result<PTE, ()> },
    UnmapShootdownWaiting { ULT_id: nat, vaddr: nat, result: Result<PTE, ()> },
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

    pub open spec fn vmem_pte_size(self, pt: Map<nat, PTE>) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. } => {
                pte.frame.size
            },
            CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
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

impl Constants {
    pub open spec fn valid_ULT(self, ULT_id: nat) -> bool {
        ULT_id < self.ULT_no
    }

    pub open spec fn interp(self) -> hlspec::Constants {
        hlspec::Constants { thread_no: self.ULT_no, phys_mem_size: self.hw.phys_mem_size }
    }
}

impl<M: mmu::MMU> State<M> {
    pub open spec fn kernel_lock(self, consts: Constants) -> Option<Core> {
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
    pub open spec fn valid_ids(self, c: Constants) -> bool {
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

    pub open spec fn inflight_pte_above_zero_pte_result_consistent(self, c: Constants) -> bool {
        forall|core: Core| hardware::valid_core(c.hw, core) ==>
            match self.core_states[core] {
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. }
                    => pte.frame.size > 0,
                CoreState::UnmapWaiting { vaddr, .. }
                | CoreState::UnmapOpExecuting { vaddr, result: None, .. }
                    => self.interp_pt_mem().contains_key(vaddr)
                        ==> self.interp_pt_mem()[vaddr].frame.size > 0,
                CoreState::UnmapOpExecuting { result: Some(result), .. }
                | CoreState::UnmapOpDone { result, .. }
                | CoreState::UnmapShootdownWaiting { result, .. }
                    => result is Ok ==> result.get_Ok_0().frame.size > 0,
                CoreState::Idle => true,
            }
    }

    pub open spec fn successful_unmaps(self, c: Constants) -> bool {
        forall|core: Core| hardware::valid_core(c.hw, core) ==>
            match self.core_states[core] {
                CoreState::UnmapOpExecuting { vaddr, result: Some(_), .. }
                | CoreState::UnmapOpDone { vaddr, .. }
                | CoreState::UnmapShootdownWaiting { vaddr, .. }
                    => !self.interp_pt_mem().contains_key(vaddr),
                _ => true,
            }
    }

    pub open spec fn wf(self, c: Constants) -> bool {
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

    pub open spec fn basic_inv(self, c: Constants) -> bool {
        &&& self.wf(c)
        &&& self.valid_ids(c)
        &&& self.inflight_pte_above_zero_pte_result_consistent(c)
        &&& self.successful_unmaps(c)

    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.basic_inv(c)
        //&&& self.tlb_inv(c)
        &&& self.overlapping_vmem_inv(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about the TLB
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn shootdown_cores_valid(self, c: Constants) -> bool {
        forall|core| #[trigger]
            self.TLB_Shootdown.open_requests.contains(core) ==> hardware::valid_core(c.hw, core)
    }

    pub open spec fn successful_IPI(self, c: Constants) -> bool {
        forall|dispatcher: Core|
            {
                hardware::valid_core(c.hw, dispatcher) ==> match self.core_states[dispatcher] {
                    CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                        forall|handler: Core|
                            !(#[trigger] self.TLB_Shootdown.open_requests.contains(handler))
                                ==> !self.hw.nodes[handler.node_id].cores[handler.core_id].tlb.contains_key(
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
                        self.core_states.contains_key(core) && match self.core_states[core] {
                            CoreState::UnmapOpDone { vaddr, result, .. }
                            | CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                                (result is Ok) && (vaddr === v_address)
                            },
                            _ => false,
                        }
                },
        )
    }

    pub open spec fn TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(self, c: Constants) -> bool {
        forall|core: Core|
            {
                #[trigger] hardware::valid_core(c.hw, core)
                    ==> self.hw.nodes[core.node_id].cores[core.core_id].tlb.dom().subset_of(
                    self.interp_pt_mem().dom().union(self.Unmap_vaddr()),
                )
            }
    }

    pub open spec fn shootdown_exists(self, c: Constants) -> bool {
        !(self.TLB_Shootdown.open_requests === Set::<Core>::empty()) ==> exists|core|
            hardware::valid_core(c.hw, core)
                && self.core_states[core] matches (CoreState::UnmapShootdownWaiting { vaddr, .. })
    }

    pub open spec fn tlb_inv(self, c: Constants) -> bool {
        &&& self.shootdown_cores_valid(c)
        &&& self.successful_IPI(c)
        &&& self.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Invariants about overlapping
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    pub open spec fn set_core_idle(self, c: Constants, core: Core) -> State<M>
        recommends
            hardware::valid_core(c.hw, core),
    {
        State {
            core_states: self.core_states.insert(core, CoreState::Idle),
            ..self
        }
    }

    pub open spec fn inflight_map_no_overlap_inflight_vmem(self, c: Constants) -> bool {
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

    pub open spec fn existing_map_no_overlap_existing_vmem(self, c: Constants) -> bool {
        forall|vaddr| #[trigger]
            self.interp_pt_mem().contains_key(vaddr)
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

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Interpretation functions
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    pub open spec fn interp_pt_mem(self) -> Map<nat, PTE> {
        hardware::interp_pt_mem(self.pt_mem)
    }

    pub open spec fn inflight_unmap_vaddr(self) -> Set<nat> {
        Set::new(|v_address: nat| {
            &&& self.interp_pt_mem().contains_key(v_address)
            &&& exists|core: Core|
                self.core_states.contains_key(core) && match self.core_states[core] {
                    CoreState::UnmapWaiting { ULT_id, vaddr }
                    | CoreState::UnmapOpExecuting { ULT_id, vaddr, .. }
                    | CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                    | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                        vaddr === v_address
                    },
                    _ => false,
                }
        })
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PTE> {
        let effective_mappings = self.interp_pt_mem();
        let unmap_dom = self.inflight_unmap_vaddr();
        Map::new(
            |vmem_idx: nat| effective_mappings.contains_key(vmem_idx) && !unmap_dom.contains(vmem_idx),
            |vmem_idx: nat| effective_mappings[vmem_idx],
        )
    }

    pub open spec fn interp_vmem(self, c: Constants) -> Map<nat, nat> {
        let phys_mem_size = c.interp().phys_mem_size;
        let mappings: Map<nat, PTE> = self.effective_mappings();
        Map::new(
            |vmem_idx: nat| hlspec::mem_domain_from_mappings_contains(phys_mem_size, vmem_idx, mappings),
            |vmem_idx: nat| {
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let (base, pte) = choose|base: nat, pte: PTE| #![auto]
                    mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
                self.hw.mem[pmem_idx as int]
            },
        )
    }

    pub open spec fn interp_thread_state(self, c: Constants) -> Map<
        nat,
        hlspec::ThreadState,
    > {
        Map::new(
            |ult_id: nat| c.valid_ULT(ult_id),
            |ult_id: nat|
                {
                    match self.core_states[c.ULT2core[ult_id]] {
                        CoreState::MapWaiting { ULT_id, vaddr, pte }
                        | CoreState::MapExecuting { ULT_id, vaddr, pte } => {
                            if ULT_id == ult_id {
                                hlspec::ThreadState::Map { vaddr, pte }
                            } else {
                                hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapWaiting { ULT_id, vaddr }
                        | CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None } => {
                            let pte = if self.interp_pt_mem().contains_key(vaddr) {
                                Some(self.interp_pt_mem()[vaddr])
                            } else {
                                None
                            };
                            if ULT_id == ult_id {
                                hlspec::ThreadState::Unmap { vaddr, pte }
                            } else {
                                hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(result) }
                        | CoreState::UnmapOpDone { ULT_id, vaddr, result }
                        | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result } => {
                            if ULT_id == ult_id {
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
        let mappings: Map<nat, PTE> = self.effective_mappings();
        let mem: Map<nat, nat> = self.interp_vmem(c);
        let thread_state: Map<nat, hlspec::ThreadState> = self.interp_thread_state(c);
        let sound: bool = self.sound;
        hlspec::State { mem, mappings, thread_state, sound }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Overlapping inflight memory helper functions for HL-soundness
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    candidate: PTE,
) -> bool {
    exists|b: CoreState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            CoreState::MapWaiting { vaddr, pte, .. }
            | CoreState::MapExecuting { vaddr, pte, .. } => {
                overlap(candidate.frame, pte.frame)
            },
            CoreState::UnmapWaiting { ULT_id, vaddr }
            | CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None, .. } => {
                &&& pt.contains_key(vaddr)
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
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    exists|b: CoreState| #![auto] {
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
                let size = if pt.contains_key(vaddr) {
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
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    ULT_id: nat,
    system_step: hardware::Step,
) -> bool {
    let core = c.ULT2core[ULT_id];
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
        || system_step is TLBFill
        || system_step is TLBEvict
        || (system_step matches hardware::Step::MMUStep { lbl: mmu::Lbl::Tau })
    &&& !(system_step is Stutter)
    //hw statemachine steps
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
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

pub open spec fn step_Map_enabled(
    //pt_mem: mem::PageTableMemory,
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
    //&&& pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_Map_Start<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    ULT_id: nat,
    vaddr: nat,
    pte: PTE,
) -> bool {
    let core = c.ULT2core[ULT_id];
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
    &&& step_Map_enabled(vaddr, pte)

    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapWaiting { ULT_id, vaddr, pte })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound && step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte)
}

pub open spec fn step_Map_op_Start<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::MapWaiting { ULT_id, vaddr, pte }
    &&& s1.kernel_lock(c) is None

    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapExecuting { ULT_id, vaddr, pte })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_op_Stutter<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
    paddr: usize,
    value: usize,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] is MapExecuting

    // hw statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, paddr, value))
    &&& s2.interp_pt_mem() == s1.interp_pt_mem() // restrict possible writes
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem.write(paddr, value)
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_End<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
    paddr: usize,
    value: usize,
    result: Result<(), ()>,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::MapExecuting { ULT_id, vaddr, pte }
    // hw statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, paddr, value))
    &&& if candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte) {
        &&& result is Err
        &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    } else {
        &&& result is Ok
        &&& s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte)
    }
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem.write(paddr, value)
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn step_Unmap_sound(
    pt: Map<nat, PTE>,
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
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    ULT_id: nat,
    vaddr: nat,
) -> bool {
    let pt = s1.interp_pt_mem();
    let core = c.ULT2core[ULT_id];
    let pte_size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
    //enabling conditions
    &&& c.valid_ULT(ULT_id)
    &&& s1.core_states[core] is Idle
    &&& step_Unmap_enabled(vaddr)
    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapWaiting { ULT_id, vaddr })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound && step_Unmap_sound(pt, s1.core_states.values(), vaddr, pte_size)
}

pub open spec fn step_Unmap_Op_Start<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapWaiting { ULT_id, vaddr }
    &&& s1.kernel_lock(c) is None
    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None })
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_Change<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
    paddr: usize,
    value: usize,
    result: Result<PTE, ()>,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting { ULT_id, vaddr, result: None }
    // hw statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, paddr, value))
    &&& if s1.interp_pt_mem().contains_key(vaddr) {
        &&& result is Ok
        &&& s2.interp_pt_mem() == s1.interp_pt_mem().remove(vaddr)
        &&& s2.core_states == s1.core_states.insert(
            core,
            CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(Ok(s1.interp_pt_mem()[vaddr])) }
        )
    } else {
        &&& result is Err
        &&& s2.interp_pt_mem() == s1.interp_pt_mem()
        &&& s2.core_states == s1.core_states.insert(
            core,
            CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(Err(())) }
        )
    }
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem.write(paddr, value)
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_Stutter<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
    paddr: usize,
    value: usize,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(res) }
    // hw statemachine steps
    &&& hardware::step_MMUStep(c.hw, s1.hw, s2.hw, mmu::Lbl::Write(core, paddr, value))
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem.write(paddr, value)
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Op_End<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpExecuting { ULT_id, vaddr, result: Some(res) }
    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapOpDone { ULT_id, vaddr, result: res }
    )
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_Initiate_Shootdown<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& s1.core_states[core] matches CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, result }
    &&& result is Ok
    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, result },
    )
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: vaddr,
        open_requests: Set::new(|core: Core| hardware::valid_core(c.hw, core)),
    }
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

// Acknowledge TLB eviction to other core (in response to shootdown IPI)
// check if tlb shootdown/unmap has happend and send ACK
// TODO: Maybe rename this since we're actually doing the invlpg here as well
pub open spec fn step_Ack_Shootdown_IPI<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& s1.TLB_Shootdown.open_requests.contains(core)
    &&& !s1.hw.nodes[core.node_id].cores[core.core_id].tlb.contains_key(s1.TLB_Shootdown.vaddr)
    // hw statemachine steps
    &&& hardware::step_Invlpg(c.hw, s1.hw, s2.hw, core, s1.TLB_Shootdown.vaddr as usize)
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.TLB_Shootdown == ShootdownVector {
        vaddr: s1.TLB_Shootdown.vaddr,
        open_requests: s1.TLB_Shootdown.open_requests.remove(core),
    }
    &&& s2.pt_mem == s1.pt_mem
    &&& s2.sound == s1.sound
}

pub open spec fn step_Unmap_End<M: mmu::MMU>(
    c: Constants,
    s1: State<M>,
    s2: State<M>,
    core: Core,
) -> bool {
    //enabling conditions
    &&& hardware::valid_core(c.hw, core)
    &&& match s1.core_states[core] {
        CoreState::UnmapShootdownWaiting { result, ULT_id, .. } => {
            s1.TLB_Shootdown.open_requests.is_empty()
        },
        CoreState::UnmapOpDone { result, ULT_id, .. } => result is Err,
        _ => false,
    }
    // hw statemachine steps
    &&& hardware::step_Stutter(c.hw, s1.hw, s2.hw)
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s2.pt_mem == s1.pt_mem
    &&& s1.sound == s2.sound
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Statemachine functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[allow(inconsistent_fields)]
pub enum Step {
    HW { ULT_id: nat, step: hardware::Step },
    // Map
    MapStart { ULT_id: nat, vaddr: nat, pte: PTE },
    MapOpStart { core: Core },
    MapOpStutter { core: Core, paddr: usize, value: usize },
    MapEnd { core: Core, paddr: usize, value: usize, result: Result<(), ()> },
    // Unmap
    UnmapStart { ULT_id: nat, vaddr: nat },
    UnmapOpStart { core: Core },
    UnmapOpChange { core: Core, paddr: usize, value: usize, result: Result<PTE, ()> },
    UnmapOpStutter { core: Core, paddr: usize, value: usize },
    UnmapOpEnd { core: Core },
    UnmapInitiateShootdown { core: Core },
    AckShootdownIPI { core: Core },
    UnmapEnd { core: Core },
}

//TODO simplify this
impl Step {
    pub open spec fn interp<M: mmu::MMU>(self, c: Constants, s: State<M>) -> hlspec::Step {
        match self {
            Step::HW { ULT_id, step } => match step {
                hardware::Step::ReadWrite { vaddr, paddr, op, walk_result, core } => {
                    let hl_pte = match walk_result {
                        WalkResult::Valid { vbase, pte } => {
                            if s.effective_mappings().contains_key(vbase as nat) {
                                Some((vbase as nat, pte))
                            } else {
                                None
                            }
                        },
                        WalkResult::Invalid { .. } => None,
                    };
                    let rwop = match (op, hl_pte) {
                        (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, Some(_))
                            => RWOp::Store { new_value, result: StoreResult::Ok },
                        (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, None)
                            => RWOp::Store { new_value, result: StoreResult::Undefined },
                        (HWRWOp::Store { new_value, result: HWStoreResult::Pagefault }, _)
                            => RWOp::Store { new_value, result: StoreResult::Undefined },
                        (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, Some(_))
                            => RWOp::Load { is_exec, result: LoadResult::Value(v) },
                        (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, None)
                            => RWOp::Load { is_exec, result: LoadResult::Undefined },
                        (HWRWOp::Load { is_exec, result: HWLoadResult::Pagefault }, _)
                            => RWOp::Load { is_exec, result: LoadResult::Undefined },
                    };
                    hlspec::Step::ReadWrite { thread_id: ULT_id, vaddr, op: rwop, pte: hl_pte }
                },
                hardware::Step::Invlpg { core, vaddr } => hlspec::Step::Stutter,
                hardware::Step::TLBFill { vaddr, pte, core } => hlspec::Step::Stutter,
                hardware::Step::TLBEvict { vaddr, core } => hlspec::Step::Stutter,
                hardware::Step::Stutter => arbitrary(),
                hardware::Step::MMUStep { lbl } => hlspec::Step::Stutter,
            },
            //Map steps
            Step::MapStart { ULT_id, vaddr, pte } => {
                hlspec::Step::MapStart { thread_id: ULT_id, vaddr, pte }
            },
            Step::MapOpStart { .. } => hlspec::Step::Stutter,
            Step::MapOpStutter { .. } => hlspec::Step::Stutter,
            Step::MapEnd { core, result, paddr, value } => {
                match s.core_states[core] {
                    CoreState::MapExecuting { ULT_id, .. } => {
                        hlspec::Step::MapEnd { thread_id: ULT_id, result }
                    },
                    _ => { arbitrary() },
                }
            },
            //Unmap steps
            Step::UnmapStart { ULT_id, vaddr } => {
                hlspec::Step::UnmapStart { thread_id: ULT_id, vaddr }
            },
            Step::UnmapOpStart { .. } => hlspec::Step::Stutter,
            Step::UnmapOpChange { .. } => hlspec::Step::Stutter,
            Step::UnmapOpStutter { .. } => hlspec::Step::Stutter,
            Step::UnmapOpEnd { .. } => hlspec::Step::Stutter,
            Step::UnmapInitiateShootdown { .. } => hlspec::Step::Stutter,
            Step::AckShootdownIPI { .. } => hlspec::Step::Stutter,
            Step::UnmapEnd { core } => {
                match s.core_states[core] {
                    CoreState::UnmapShootdownWaiting { result, ULT_id, .. } => {
                        hlspec::Step::UnmapEnd { thread_id: ULT_id, result: result_map_ok(result, |r| ()) }
                    },
                    CoreState::UnmapOpDone { result, ULT_id, .. } => {
                        hlspec::Step::UnmapEnd { thread_id: ULT_id, result: result_map_ok(result, |r| ()) }
                    },
                    _ => arbitrary(),
                }
            },
        }
    }
}

pub open spec fn next_step<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>, step: Step) -> bool {
    match step {
        Step::HW { ULT_id, step }                          => step_HW(c, s1, s2, ULT_id, step),
        //Map steps
        Step::MapStart { ULT_id, vaddr, pte }              => step_Map_Start(c, s1, s2, ULT_id, vaddr, pte),
        Step::MapOpStart { core }                          => step_Map_op_Start(c, s1, s2, core),
        Step::MapOpStutter { core, paddr, value }          => step_Map_op_Stutter(c, s1, s2, core, paddr, value),
        Step::MapEnd { core, paddr, value, result }        => step_Map_End(c, s1, s2, core, paddr, value, result),
        //Unmap steps
        Step::UnmapStart { ULT_id, vaddr }                 => step_Unmap_Start(c, s1, s2, ULT_id, vaddr),
        Step::UnmapOpStart { core }                        => step_Unmap_Op_Start(c, s1, s2, core),
        Step::UnmapOpChange { core, paddr, value, result } => step_Unmap_Op_Change(c, s1, s2, core, paddr, value, result),
        Step::UnmapOpStutter { core, paddr, value }        => step_Unmap_Op_Stutter(c, s1, s2, core, paddr, value),
        Step::UnmapOpEnd { core }                          => step_Unmap_Op_End(c, s1, s2, core),
        Step::UnmapInitiateShootdown { core }              => step_Unmap_Initiate_Shootdown(c, s1, s2, core),
        Step::AckShootdownIPI { core }                     => step_Ack_Shootdown_IPI(c, s1, s2, core),
        Step::UnmapEnd { core }                            => step_Unmap_End(c, s1, s2, core),
    }
}

pub open spec fn next<M: mmu::MMU>(c: Constants, s1: State<M>, s2: State<M>) -> bool {
    exists|step: Step| next_step(c, s1, s2, step)
}

pub open spec fn init<M: mmu::MMU>(c: Constants, s: State<M>) -> bool {
    // hardware stuff
    &&& s.interp_pt_mem() === Map::empty()
    &&& hardware::init(c.hw, s.hw)
    //wf of ULT2core mapping
    &&& forall|id: nat| #[trigger] c.valid_ULT(id) <==> c.ULT2core.contains_key(id)
    &&& forall|id: nat| c.valid_ULT(id) ==> #[trigger] hardware::valid_core(c.hw, c.ULT2core[id])
    //core_state
    &&& forall|core: Core| hardware::valid_core(c.hw, core) <==> #[trigger] s.core_states.contains_key(core)
    &&& forall|core: Core| #[trigger] hardware::valid_core(c.hw, core) ==> s.core_states[core] === CoreState::Idle
    //shootdown
    &&& s.TLB_Shootdown.open_requests === Set::empty()
    //sound
    &&& s.sound
}

} // verus!
