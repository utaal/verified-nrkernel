use vstd::prelude::*;

//use crate::impl_u::spec_pt;
//use crate::spec_t::hardware::Core;
use crate::definitions_t::{
    above_zero, candidate_mapping_overlaps_existing_vmem, overlap, MemRegion, PageTableEntry,
};
use crate::impl_u::os_refinement::{
    lemma_map_insert_values_equality, map_values_contain_value_of_contained_key,
};
use crate::spec_t::{hardware, hlspec, os};

verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of Invariant
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_inv(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s),
    ensures
        s.inv(c),
{
    assert(s.basic_inv(c));
    init_implies_tlb_inv(c, s);
}

pub proof fn next_preserves_inv(c: os::OSConstants, s1: os::OSVariables, s2: os::OSVariables)
    requires
        s1.inv(c),
        os::next(c, s1, s2),
    ensures
        s2.inv(c),
{
    let step = choose|step| os::next_step(c, s1, s2, step);
    next_step_preserves_inv(c, s1, s2, step);
}

pub proof fn next_step_preserves_inv(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.inv(c),
{
    assert forall|core1, core2|
        (hardware::valid_core(c.hw, core1) && #[trigger] s2.core_states[core1].holds_lock()
            && hardware::valid_core(c.hw, core2)
            && #[trigger] s2.core_states[core2].holds_lock()) implies core1 === core2 by {
        let _ = s1.core_states[core1].holds_lock();
        let _ = s1.core_states[core2].holds_lock();
    }
    assert forall|core| hardware::valid_core(c.hw, core) implies {
        match s2.core_states[core] {
            os::CoreState::UnmapOpExecuting { vaddr,.. }
            | os::CoreState::UnmapOpDone { vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                !s2.interp_pt_mem().dom().contains(vaddr)
            },
            _ => { true },
        }
    } by {
        let _ = s1.core_states[core].holds_lock();
    }
    assert(s2.basic_inv(c));
    //next_step_preserves_tlb_inv(c, s1, s2, step);
    next_step_preserves_overlap_vmem_inv(c, s1, s2, step);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of TLB Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_tlb_inv(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s),
    ensures
        s.tlb_inv(c),
{
    assert(s.TLB_Shootdown.open_requests.is_empty());
    Set::lemma_len0_is_empty(s.TLB_Shootdown.open_requests);
    assert(s.TLB_Shootdown.open_requests === Set::empty());
    assert(forall|core| #[trigger]
        hardware::valid_core(c.hw, core)
            ==> s.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().is_empty());
    assert(s.shootdown_cores_valid(c));
    assert(s.successful_IPI(c));
    //assert(s.successful_shootdown(c));
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
}

/*
    assert (s2.shootdown_cores_valid(c));
    assert (s2.successful_IPI(c));
    assert (s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));


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
*/

pub proof fn next_step_preserves_tlb_inv(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        s1.tlb_inv(c),
        s1.basic_inv(c),
        s2.basic_inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.tlb_inv(c),
{
    match step {
        os::OSStep::HW { ULT_id, step } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::MapOpStart { core } => {
            assume(s2.Unmap_vaddr() == Set::<nat>::empty());
            assume(s1.Unmap_vaddr() == Set::<nat>::empty());
            assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::MapEnd { core, result } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.Unmap_vaddr() == Set::<nat>::empty());
            assume(s1.Unmap_vaddr() == Set::<nat>::empty());
            //assert(s1.interp_pt_mem().dom().subset_of(s2.interp_pt_mem().dom()));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        //Unmap steps
        os::OSStep::UnmapStart { ULT_id, vaddr } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::UnmapOpStart { core, result } => {
            assume(false);
        },
        os::OSStep::UnmapOpEnd { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::UnmapInitiateShootdown { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
        os::OSStep::UnmapEnd { core } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::AckShootdownIPI { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::ViewStutter { .. } => {
            assume(false);
        },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of overlapping virtual memory Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn next_step_preserves_overlap_vmem_inv(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        s1.inv(c),
        s2.basic_inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.overlapping_vmem_inv(c),
{
    if s2.sound {
        match step {
            os::OSStep::HW { ULT_id, step } => {
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            //Map steps
            os::OSStep::MapStart { ULT_id, vaddr, pte } => {
                let core = c.ULT2core[ULT_id];
                let corestate = os::CoreState::MapWaiting { ULT_id, vaddr, pte };
                Lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::OSStep::MapOpStart { core } => {
                let vaddr = s1.core_states[core]->MapWaiting_vaddr;
                let pte = s1.core_states[core]->MapWaiting_pte;
                let ULT_id = s1.core_states[core]->MapWaiting_ULT_id;
                let corestate = os::CoreState::MapExecuting { ULT_id, vaddr, pte };
                Lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::OSStep::MapEnd { core, result } => {
                let vaddr = s1.core_states[core]->MapWaiting_vaddr;
                assert(unique_CoreStates(s2.core_states));
                assert forall|state1: os::CoreState, state2: os::CoreState|
                    s2.core_states.values().contains(state1) && s2.core_states.values().contains(
                        state2,
                    ) && !state1.is_idle() && !state2.is_idle() && overlap(
                        MemRegion {
                            base: state1.vaddr(),
                            size: state1.vmem_pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: state2.vaddr(),
                            size: state2.vmem_pte_size(s2.interp_pt_mem()),
                        },
                    ) implies state1 == state2 by {
                    if (state1.vaddr() == vaddr || state2.vaddr() == vaddr) {
                        admit();
                    } else {
                        if (s1.interp_pt_mem().dom().contains(state1.vaddr())) {
                            assert(overlap(
                                MemRegion {
                                    base: state1.vaddr(),
                                    size: state1.vmem_pte_size(s1.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: state2.vaddr(),
                                    size: state2.vmem_pte_size(s1.interp_pt_mem()),
                                },
                            ));
                        } else {
                            assume(s2.interp_pt_mem().dom().subset_of(
                                s1.interp_pt_mem().dom().insert(vaddr),
                            ));
                            assert(!s2.interp_pt_mem().dom().contains(state1.vaddr()));
                        }
                    }
                }
                assert(no_overlap_vmem_values(c, s2.core_states, s2.interp_pt_mem()));

                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inflight_map_no_overlap_inflight_vmem(c));

                assume(s2.existing_map_no_overlap_existing_vmem(c));
            },
            //Unmap steps
            os::OSStep::UnmapStart { ULT_id, vaddr } => {
                let core = c.ULT2core[ULT_id];
                let corestate = os::CoreState::UnmapWaiting { ULT_id, vaddr };
                Lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::OSStep::UnmapOpStart { core, result } => {
                let vaddr = s1.core_states[core]->UnmapWaiting_vaddr;
                let ULT_id = s1.core_states[core]->UnmapWaiting_ULT_id;
                let result = match result {
                    Ok(_) => Ok(s1.interp_pt_mem()[vaddr]),
                    Err(_) => Err(()),
                };
                let corestate = os::CoreState::UnmapOpExecuting { ULT_id, vaddr, result };
                Lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_submap_preserves_no_overlap(
                    c,
                    s2.core_states,
                    s1.interp_pt_mem(),
                    s2.interp_pt_mem(),
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));

                assert forall|base| #[trigger]
                    s2.interp_pt_mem().dom().contains(
                        base,
                    ) implies !candidate_mapping_overlaps_existing_vmem(
                    s2.interp_pt_mem().remove(base),
                    base,
                    s2.interp_pt_mem()[base],
                ) by {
                    assert(s2.interp_pt_mem().dom().contains(base));
                    if (candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base],
                    )) {
                        let overlap_vaddr = choose|b: nat|
                            #![auto]
                            {
                                &&& s2.interp_pt_mem().remove(base).dom().contains(b)
                                &&& overlap(
                                    MemRegion {
                                        base: base,
                                        size: s2.interp_pt_mem()[base].frame.size,
                                    },
                                    MemRegion { base: b, size: s2.interp_pt_mem()[b].frame.size },
                                )
                            };
                        assert(s1.interp_pt_mem().remove(base).dom().contains(overlap_vaddr));
                        // assert(s1.existing_map_no_overlap_existing_vmem(c));
                        assert(false);
                    }
                }
                assert(s2.existing_map_no_overlap_existing_vmem(c));

            },
            os::OSStep::UnmapOpEnd { core } => {
                let vaddr = s1.core_states[core]->UnmapOpExecuting_vaddr;
                let ULT_id = s1.core_states[core]->UnmapOpExecuting_ULT_id;
                let result = s1.core_states[core]->UnmapOpExecuting_result;
                let corestate = os::CoreState::UnmapOpDone { ULT_id, vaddr, result };
                Lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::OSStep::UnmapInitiateShootdown { core } => {
                let vaddr = s1.core_states[core]->UnmapOpDone_vaddr;
                let ULT_id = s1.core_states[core]->UnmapOpDone_ULT_id;
                let result = s1.core_states[core]->UnmapOpDone_result;
                let corestate = os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result };
                Lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                Lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::OSStep::UnmapEnd { core } => {
                assert(s2.overlapping_vmem_inv(c));
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            _ => {
                assert(s2.overlapping_vmem_inv(c));
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Alternative Definition for inflight_map_no_overlap_inflight_vmem and Equivalence proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn unique_CoreStates(map: Map<hardware::Core, os::CoreState>) -> bool {
    forall|a|
        #![auto]
        map.dom().contains(a) && !map.index(a).is_idle() ==> !map.remove(a).values().contains(
            map.index(a),
        )
}

pub open spec fn no_overlap_vmem_values(
    c: os::OSConstants,
    core_states: Map<hardware::Core, os::CoreState>,
    pt: Map<nat, PageTableEntry>,
) -> bool {
    forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) ==> state1 == state2
}

pub proof fn Lemma_overlapping_inv_implies_unique_and_overlap_values(
    c: os::OSConstants,
    s: os::OSVariables,
)
    requires
        s.basic_inv(c),
        s.inflight_map_no_overlap_inflight_vmem(c),
    ensures
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(c, s.core_states, s.interp_pt_mem()),
{
}

pub proof fn Lemma_unique_and_overlap_values_implies_overlap_vmem(
    c: os::OSConstants,
    s: os::OSVariables,
)
    requires
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(c, s.core_states, s.interp_pt_mem()),
        s.basic_inv(c),
    ensures
        s.inflight_map_no_overlap_inflight_vmem(c),
{
    assert forall|core1: hardware::Core, core2: hardware::Core|
        (hardware::valid_core(c.hw, core1) && hardware::valid_core(c.hw, core2)
            && !s.core_states[core1].is_idle() && !s.core_states[core2].is_idle() && overlap(
            MemRegion {
                base: s.core_states[core1].vaddr(),
                size: s.core_states[core1].vmem_pte_size(s.interp_pt_mem()),
            },
            MemRegion {
                base: s.core_states[core2].vaddr(),
                size: s.core_states[core2].vmem_pte_size(s.interp_pt_mem()),
            },
        )) implies (core1 === core2) by {
        if (hardware::valid_core(c.hw, core1) && hardware::valid_core(c.hw, core2)
            && !s.core_states[core1].is_idle() && !s.core_states[core2].is_idle() && overlap(
            MemRegion {
                base: s.core_states[core1].vaddr(),
                size: s.core_states[core1].vmem_pte_size(s.interp_pt_mem()),
            },
            MemRegion {
                base: s.core_states[core2].vaddr(),
                size: s.core_states[core2].vmem_pte_size(s.interp_pt_mem()),
            },
        )) {
            map_values_contain_value_of_contained_key(s.core_states, core1);
            map_values_contain_value_of_contained_key(s.core_states, core2);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata to help proof inflight_map_no_overlap_inflight_vmem
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn Lemma_insert_idle_corestate_preserves_no_overlap(
    c: os::OSConstants,
    core_states: Map<hardware::Core, os::CoreState>,
    pt: Map<nat, PageTableEntry>,
    core: hardware::Core,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(c, core_states, pt),
    ensures
        unique_CoreStates(core_states.insert(core, os::CoreState::Idle)),
        no_overlap_vmem_values(c, core_states.insert(core, os::CoreState::Idle), pt),
{
    assert forall|a|
        #![auto]
        core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
            core,
            os::CoreState::Idle,
        ).index(a).is_idle() implies !core_states.insert(core, os::CoreState::Idle).remove(
        a,
    ).values().contains(core_states.insert(core, os::CoreState::Idle).index(a)) by {
        if (core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
            core,
            os::CoreState::Idle,
        ).index(a).is_idle() && a != core) {
            assert(core_states.dom().contains(a));
            assert(core_states.index(a) == core_states.insert(core, os::CoreState::Idle).index(a));
            assert(!core_states.index(a).is_idle());
            assert(!core_states.remove(a).values().contains(core_states.index(a)));

            assert(core_states.insert(core, os::CoreState::Idle).remove(a) =~= core_states.remove(
                a,
            ).insert(core, os::CoreState::Idle));

            lemma_map_insert_values_equality(core_states.remove(a), core, os::CoreState::Idle);
        }
    };
    assert(no_overlap_vmem_values(c, core_states.insert(core, os::CoreState::Idle), pt));
}

pub proof fn Lemma_insert_preserves_no_overlap(
    c: os::OSConstants,
    core_states: Map<hardware::Core, os::CoreState>,
    pt: Map<nat, PageTableEntry>,
    core: hardware::Core,
    corestate: os::CoreState,
)
    requires
        corestate.holds_lock(),
        forall|cr|
            #![auto]
            core_states.dom().contains(cr) && core_states[cr].holds_lock() ==> cr == core,
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(c, core_states, pt),
        !core_states[core].is_idle(),
        !corestate.is_idle(),
        core_states[core].vaddr() == corestate.vaddr(),
        core_states[core].vmem_pte_size(pt) >= corestate.vmem_pte_size(pt),
        core_states[core] != corestate,
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(c, core_states.insert(core, corestate), pt),
{
    assert forall|a|
        #![auto]
        core_states.insert(core, corestate).dom().contains(a) && !core_states.insert(
            core,
            corestate,
        ).index(a).is_idle() implies !core_states.insert(core, corestate).remove(
        a,
    ).values().contains(core_states.insert(core, corestate).index(a)) by {
        if (a != core) {
            assert(!core_states[a].holds_lock());
            if (core_states.insert(core, corestate).remove(a).values().contains(
                core_states.insert(core, corestate).index(a),
            )) {
                let same_core = choose|cr|
                    #![auto]
                    core_states.insert(core, corestate).dom().contains(cr) && core_states.insert(
                        core,
                        corestate,
                    )[cr] == core_states.insert(core, corestate)[a] && cr != a;
                assert(core_states.remove(a).dom().contains(same_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, corestate).values().contains(state1) && core_states.insert(
            core,
            corestate,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) implies state1 == state2 by {
        if (state1 == corestate || state2 == corestate) {
            let other = if (state1 != corestate) {
                state1
            } else {
                state2
            };
            if (other != corestate) {
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.vmem_pte_size(pt) },
                    MemRegion {
                        base: core_states[core].vaddr(),
                        size: core_states[core].vmem_pte_size(pt),
                    },
                ));
                let other_core = choose|b|
                    #![auto]
                    core_states.insert(core, corestate).dom().contains(b) && core_states[b] == other
                        && b != core;
                assert(core_states.remove(core).dom().contains(other_core));
                assert(false);
            }
        }
    }
}

pub proof fn Lemma_insert_no_overlap_preserves_no_overlap(
    c: os::OSConstants,
    core_states: Map<hardware::Core, os::CoreState>,
    pt: Map<nat, PageTableEntry>,
    core: hardware::Core,
    corestate: os::CoreState,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(c, core_states, pt),
        core_states[core].is_idle(),
        !corestate.is_idle(),
        !os::candidate_mapping_overlaps_inflight_vmem(
            pt,
            core_states.values(),
            corestate.vaddr(),
            corestate.vmem_pte_size(pt),
        ),
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(c, core_states.insert(core, corestate), pt),
{
    assert forall|a|
        #![auto]
        core_states.insert(core, corestate).dom().contains(a) && !core_states.insert(
            core,
            corestate,
        ).index(a).is_idle() implies !core_states.insert(core, corestate).remove(
        a,
    ).values().contains(core_states.insert(core, corestate).index(a)) by {
        if (core_states.insert(core, corestate).remove(a).values().contains(
            core_states.insert(core, corestate).index(a),
        )) {
            let some_core = choose|cr|
                #![auto]
                cr != a && core_states.insert(core, corestate).dom().contains(cr)
                    && core_states.insert(core, corestate)[cr] == core_states.insert(
                    core,
                    corestate,
                )[a];
            if (a == core || some_core == core) {
                let other = if (some_core != core) {
                    some_core
                } else {
                    a
                };
                assert(core_states.values().contains(core_states[other]));
                assert(overlap(
                    MemRegion {
                        base: core_states[other].vaddr(),
                        size: core_states[other].vmem_pte_size(pt),
                    },
                    MemRegion { base: corestate.vaddr(), size: corestate.vmem_pte_size(pt) },
                ));
            } else {
                assert(core_states.remove(a).dom().contains(some_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, corestate).values().contains(state1) && core_states.insert(
            core,
            corestate,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) implies state1 == state2 by {
        if (state1 == corestate || state2 == corestate) {
            let other = if (state1 != corestate) {
                state1
            } else {
                state2
            };
            if (other != corestate) {
                assert(core_states.values().contains(other));
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.vmem_pte_size(pt) },
                    MemRegion { base: corestate.vaddr(), size: corestate.vmem_pte_size(pt) },
                ));
                assert(false);
            }
        }
    }
}

pub proof fn Lemma_submap_preserves_no_overlap(
    c: os::OSConstants,
    core_states: Map<hardware::Core, os::CoreState>,
    pt: Map<nat, PageTableEntry>,
    sub_pt: Map<nat, PageTableEntry>,
)
    requires
        unique_CoreStates(core_states),
        no_overlap_vmem_values(c, core_states, pt),
        sub_pt.submap_of(pt),
    ensures
        no_overlap_vmem_values(c, core_states, sub_pt),
{
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(sub_pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(sub_pt) },
        ) implies state1 == state2 by {
        assert(overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ));
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(
    c: os::OSConstants,
    s: os::OSVariables,
    base: nat,
    candidate_size: nat,
)
    requires
        s.basic_inv(c),
    ensures
        os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    )) by {
        if (os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        )) {
            let corestate = choose|b: os::CoreState| #![auto]
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapWaiting { vaddr, .. } => {
                            let size = if s.interp_pt_mem().dom().contains(vaddr) {
                                s.interp_pt_mem().index(vaddr).frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapOpExecuting { vaddr, result, .. }
                        | os::CoreState::UnmapOpDone { vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
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
                };
            let core = choose|core|
                hardware::valid_core(c.hw, core) && s.core_states[core] == corestate;
            match corestate {
                os::CoreState::MapWaiting { ULT_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ULT_id, vaddr, pte, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state[ULT_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Map {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& p_te === pte
                        &&& overlap(
                            MemRegion { base: v_address, size: p_te.frame.size },
                            MemRegion { base: base, size: candidate_size },
                        )
                    });
                },
                os::CoreState::UnmapWaiting { ULT_id, vaddr } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    if (s.interp_pt_mem().dom().contains(vaddr)) {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_address,
                                pte: Some(p_te),
                            }
                            &&& v_address === vaddr
                            &&& s.interp_pt_mem()[vaddr] === p_te
                            &&& overlap(
                                MemRegion { base: v_address, size: p_te.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        });
                    } else {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_address,
                                pte: None,
                            }
                            &&& v_address === vaddr
                            &&& overlap(
                                MemRegion { base: v_address, size: 0 },
                                MemRegion { base: base, size: candidate_size },
                            )
                        });
                    }
                },
                os::CoreState::UnmapOpExecuting { ULT_id, vaddr, result, .. }
                | os::CoreState::UnmapOpDone { ULT_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    if result is Ok {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_address,
                                pte: Some(pte),
                            }
                            &&& v_address === vaddr
                            &&& result.get_Ok_0() === pte
                            &&& overlap(
                                MemRegion { base: v_address, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        });
                    } else {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_address,
                                pte: None,
                            }
                            &&& v_address === vaddr
                            &&& overlap(
                                MemRegion { base: v_address, size: 0 },
                                MemRegion { base: base, size: candidate_size },
                            )
                        });
                    }
                },
                _ => {},
            };
        } else {
        };
    };
}

pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(
    c: os::OSConstants,
    s: os::OSVariables,
    base: nat,
    candidate_size: nat,
)
    requires
        s.basic_inv(c),
    ensures
        hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ) ==> os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    ) ==> os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    )) by {
        if (hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        )) {
            let thread_state = choose|b|
                {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::AbstractArguments::Map { vaddr, pte } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        hlspec::AbstractArguments::Unmap { vaddr, pte } => {
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
                };
            let ULT_id = choose|id| #[trigger]
                c.valid_ULT(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ULT(ULT_id));
            let core = c.ULT2core[ULT_id];
            assert(hardware::valid_core(c.hw, core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ULT_id: ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ULT_id: ult_id, vaddr, pte, .. } => {
                    assert(ult_id == ULT_id);
                    //assert(above_zero(pte.frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    ));
                },
                os::CoreState::UnmapWaiting { ULT_id: ult_id, vaddr } => {
                    assert(ult_id == ULT_id);
                    if s.interp_pt_mem().dom().contains(vaddr) {
                        let pte = s.interp_pt_mem()[vaddr];
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_addr,
                                pte: Some(entry),
                            }
                            &&& vaddr === v_addr
                            &&& entry === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    }
                },
                os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr, result, .. }
                | os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, result, .. } => {
                    if result is Ok {
                        assert(ult_id == ULT_id);
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_addr,
                                pte: Some(pte),
                            }
                            &&& vaddr === v_addr
                            &&& result.get_Ok_0() === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: result.get_Ok_0().frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));

                    }
                },
                _ => {},
            };
        } else {
        }
    };

}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(
    c: os::OSConstants,
    s: os::OSVariables,
    candidate: PageTableEntry,
)
    requires
        s.basic_inv(c),
        above_zero(candidate.frame.size),
    ensures
        os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    )) by {
        if os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) {
            let corestate = choose|b: os::CoreState| #![auto]
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        os::CoreState::UnmapWaiting { ULT_id, vaddr } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                        },
                        os::CoreState::UnmapOpExecuting { ULT_id, vaddr, result, .. }
                        | os::CoreState::UnmapOpDone { ULT_id, vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result, .. } => {
                            &&& result is Ok
                            &&& overlap(candidate.frame, result.get_Ok_0().frame)
                        },
                        os::CoreState::Idle => false,
                    }
                };
            let core = choose|core| #[trigger]
                s.core_states.dom().contains(core) && s.core_states[core] == corestate;
            assert(hardware::valid_core(c.hw, core));
            match corestate {
                os::CoreState::MapWaiting { ULT_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ULT_id, vaddr, pte, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state[ULT_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Map {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& p_te === pte
                        &&& overlap(candidate.frame, pte.frame)
                    });
                },
                os::CoreState::UnmapWaiting { ULT_id, vaddr } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(pte),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === pte
                        &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                    });
                },
                os::CoreState::UnmapOpExecuting { ULT_id, vaddr, result, .. }
                | os::CoreState::UnmapOpDone { ULT_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, result, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: pte,
                        }
                        &&& v_address === vaddr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                        &&& overlap(candidate.frame, pte->0.frame)
                    });
                },
                _ => {},
            };
        } else {
        };
    };
}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(
    c: os::OSConstants,
    s: os::OSVariables,
    candidate: PageTableEntry,
)
    requires
        s.basic_inv(c),
        above_zero(candidate.frame.size),
    ensures
        hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ) ==> os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    ) ==> os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    )) by {
        if (hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        )) {
            let thread_state = choose|b|
                {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::AbstractArguments::Map { vaddr, pte } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        hlspec::AbstractArguments::Unmap { vaddr, pte } => {
                            &&& pte.is_some()
                            &&& overlap(candidate.frame, pte.unwrap().frame)
                        },
                        _ => { false },
                    }
                };
            let ULT_id = choose|id| #[trigger]
                c.valid_ULT(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ULT(ULT_id));
            let core = c.ULT2core[ULT_id];
            assert(hardware::valid_core(c.hw, core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ULT_id: ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ULT_id: ult_id, vaddr, pte, .. } => {
                    assert(ult_id == ULT_id);
                  //  assert(above_zero(pte.frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, pte.frame));
                },
                os::CoreState::UnmapWaiting { ULT_id: ult_id, vaddr } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ULT_id);
                    let pte = s.interp_pt_mem()[vaddr];
                   // assert(above_zero(pte.frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame));
                },
                os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr, result, .. }
                | os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, result, .. } => {
                    assert(ult_id == ULT_id);
                 //   assert(above_zero(result.get_Ok_0().frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_addr,
                            pte,
                        }
                        &&& vaddr === v_addr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                    });
                    assert(overlap(candidate.frame, result.get_Ok_0().frame));
                },
                _ => {},
            };
        } else {
        }
    };
}

} // verus!
