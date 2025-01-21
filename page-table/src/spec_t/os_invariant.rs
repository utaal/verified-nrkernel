use vstd::prelude::*;

//use crate::impl_u::spec_pt;
use crate::definitions_t::{
    candidate_mapping_overlaps_existing_vmem, overlap, MemRegion, PTE, Core
};
use crate::spec_t::{hardware, hlspec, os, mmu};

verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of Invariant
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_inv<M: mmu::MMU>(c: os::Constants, s: os::State<M>)
    requires
        os::init(c, s),
    ensures
        s.inv(c),
{
    assert(s.basic_inv(c));
    init_implies_tlb_inv(c, s);
}

pub proof fn next_preserves_inv<M: mmu::MMU>(c: os::Constants, s1: os::State<M>, s2: os::State<M>)
    requires
        s1.inv(c),
        os::next(c, s1, s2),
    ensures
        s2.inv(c),
{
    let step = choose|step| os::next_step(c, s1, s2, step);
    next_step_preserves_inv(c, s1, s2, step);
}

pub proof fn next_step_preserves_inv<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    step: os::Step,
)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.inv(c),
{
    // TODO: unnecessary?
    //assert(s2.successful_unmaps(c)) by {
    //    assert forall|core| hardware::valid_core(c.hw, core) implies {
    //        match s2.core_states[core] {
    //            os::CoreState::UnmapOpExecuting { vaddr, result: Some(_),.. }
    //            | os::CoreState::UnmapOpDone { vaddr, .. }
    //            | os::CoreState::UnmapShootdownWaiting { vaddr, .. }
    //                => !s2.interp_pt_mem().dom().contains(vaddr),
    //            _ => true,
    //        }
    //    } by { let _ = s1.core_states[core].holds_lock(); }
    //};
    assert forall|core: Core| hardware::valid_core(c.hw, core) implies
        match s2.core_states[core] {
            os::CoreState::MapWaiting { vaddr, pte, .. }
            | os::CoreState::MapExecuting { vaddr, pte, .. }
                => pte.frame.size > 0,
            os::CoreState::UnmapWaiting { vaddr, .. }
            | os::CoreState::UnmapOpExecuting { vaddr, result: None, .. }
                => s2.interp_pt_mem().contains_key(vaddr)
                    ==> s2.interp_pt_mem()[vaddr].frame.size > 0,
            os::CoreState::UnmapOpExecuting { result: Some(result), .. }
            | os::CoreState::UnmapOpDone { result, .. }
            | os::CoreState::UnmapShootdownWaiting { result, .. }
                => result is Ok ==> result.get_Ok_0().frame.size > 0,
            os::CoreState::Idle => true,
    } by {
        match s2.core_states[core] {
            os::CoreState::MapWaiting { vaddr, pte, .. }
            | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                assert(pte.frame.size > 0);
            },
            os::CoreState::UnmapWaiting { vaddr, .. }
            | os::CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
                if s2.interp_pt_mem().contains_key(vaddr) {
                    assert(s1.interp_pt_mem().contains_key(vaddr));
                    if step matches os::Step::UnmapStart { ult_id, vaddr } {
                        // Not sure how this would be provable here but I think the proof worked at
                        // some point?
                        // May have to split invariant into two:
                        // 1. all entries in interp have size > 0
                        // 2. all entries in the core state are also in the interp
                        assume(s2.interp_pt_mem()[vaddr].frame.size > 0);
                    }
                    assert(s2.interp_pt_mem()[vaddr].frame.size > 0);
                }
            },
            os::CoreState::UnmapOpExecuting { result: Some(result), .. }
            | os::CoreState::UnmapOpDone { result, .. }
            | os::CoreState::UnmapShootdownWaiting { result, .. } => {
                assert(result is Ok ==> result.get_Ok_0().frame.size > 0);
            },
            os::CoreState::Idle => {},
        }
    };
    assert(s2.inflight_pte_above_zero_pte_result_consistent(c));

    assert(s2.basic_inv(c));
    //next_step_preserves_tlb_inv(c, s1, s2, step);
    next_step_preserves_overlap_vmem_inv(c, s1, s2, step);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of TLB Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_tlb_inv<M: mmu::MMU>(c: os::Constants, s: os::State<M>)
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
            ==> s.hw.nodes[core.node_id].cores[core.core_id].tlb.dom().is_empty());
    assert(s.shootdown_cores_valid(c));
    assert(s.successful_IPI(c));
    //assert(s.successful_shootdown(c));
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
}

pub proof fn next_step_preserves_tlb_inv<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    step: os::Step,
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
        os::Step::HW { ult_id, step } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        //Map steps
        os::Step::MapStart { ult_id, vaddr, pte } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::MapOpStart { core } => {
            assume(s2.Unmap_vaddr() == Set::<nat>::empty());
            assume(s1.Unmap_vaddr() == Set::<nat>::empty());
            assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::MapOpStutter { core, paddr, value } => {
            assume(false);
        },
        os::Step::MapEnd { core, result, paddr, value } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.Unmap_vaddr() == Set::<nat>::empty());
            assume(s1.Unmap_vaddr() == Set::<nat>::empty());
            //assert(s1.interp_pt_mem().dom().subset_of(s2.interp_pt_mem().dom()));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        //Unmap steps
        os::Step::UnmapStart { ult_id, vaddr } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::UnmapOpStart { core } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.Unmap_vaddr() == Set::<nat>::empty());
            assume(s1.Unmap_vaddr() == Set::<nat>::empty());
            assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::UnmapOpChange { .. } => {
            assume(false);
        },
        os::Step::UnmapOpStutter { .. } => {
            assume(false);
        },
        os::Step::UnmapOpEnd { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
        },
        os::Step::UnmapEnd { core } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::Step::AckShootdownIPI { core } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assert(s2.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));

        },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of overlapping virtual memory Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn next_step_preserves_overlap_vmem_inv<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    step: os::Step,
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
            //Map steps
            os::Step::MapStart { ult_id, vaddr, pte } => {
                let core = c.ult2core[ult_id];
                let corestate = os::CoreState::MapWaiting { ult_id, vaddr, pte };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::MapOpStart { core } => {
                let vaddr = s1.core_states[core]->MapWaiting_vaddr;
                let pte = s1.core_states[core]->MapWaiting_pte;
                let ult_id = s1.core_states[core]->MapWaiting_ult_id;
                let corestate = os::CoreState::MapExecuting { ult_id, vaddr, pte };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::MapEnd { core, result, paddr, value } => {
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
                    if state1.vaddr() == vaddr || state2.vaddr() == vaddr {
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
                assert(no_overlap_vmem_values(s2.core_states, s2.interp_pt_mem()));

                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inflight_map_no_overlap_inflight_vmem(c));

                assume(s2.existing_map_no_overlap_existing_vmem(c));
            },
            //Unmap steps
            os::Step::UnmapStart { ult_id, vaddr } => {
                let core = c.ult2core[ult_id];
                let corestate = os::CoreState::UnmapWaiting { ult_id, vaddr };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapOpStart { core } => {
                let vaddr = s1.core_states[core]->UnmapWaiting_vaddr;
                let ult_id = s1.core_states[core]->UnmapWaiting_ult_id;
                let corestate = os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: None };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapOpChange { core, result, .. } => {
                let vaddr = s1.core_states[core]->UnmapOpExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapOpExecuting_ult_id;
                let corestate = os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: Some(result) };
                lemma_insert_preserves_no_overlap(c, s1.core_states, s1.interp_pt_mem(), core, corestate);
                if s1.interp_pt_mem().contains_key(vaddr) {
                    assert(no_overlap_vmem_values(s2.core_states, s1.interp_pt_mem()));
                } else {
                    assume(no_overlap_vmem_values(s2.core_states, s1.interp_pt_mem()));
                }
                lemma_submap_preserves_no_overlap(c, s2.core_states, s1.interp_pt_mem(), s2.interp_pt_mem());
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));

                assert forall|base| #[trigger] s2.interp_pt_mem().dom().contains(base) implies
                    !candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base])
                by {
                    assert(s2.interp_pt_mem().dom().contains(base));
                    if candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base],
                    ) {
                        let overlap_vaddr = choose|b: nat| #![auto] {
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
            os::Step::UnmapOpEnd { core } => {
                let vaddr = s1.core_states[core]->UnmapOpExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapOpExecuting_ult_id;
                let result = s1.core_states[core]->UnmapOpExecuting_result->Some_0;
                let corestate = os::CoreState::UnmapOpDone { ult_id, vaddr, result };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapInitiateShootdown { core } => {
                let vaddr = s1.core_states[core]->UnmapOpDone_vaddr;
                let ult_id = s1.core_states[core]->UnmapOpDone_ult_id;
                let result = s1.core_states[core]->UnmapOpDone_result;
                let corestate = os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            //os::Step::HW { ult_id, step } => {},
            //os::Step::UnmapEnd { core } => {},
            _ => {},
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Alternative Definition for inflight_map_no_overlap_inflight_vmem and Equivalence proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn unique_CoreStates(map: Map<Core, os::CoreState>) -> bool {
    forall|core| #![auto] map.contains_key(core) && !map[core].is_idle()
        ==> !map.remove(core).values().contains(map[core])
}

pub open spec fn no_overlap_vmem_values(
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
) -> bool {
    forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) ==> state1 == state2
}

//pub proof fn lemma_overlapping_inv_implies_unique_and_overlap_values<M: mmu::MMU>(
//    c: os::Constants,
//    s: os::State<M>,
//)
//    requires
//        s.basic_inv(c),
//        s.inflight_map_no_overlap_inflight_vmem(c),
//    ensures
//        unique_CoreStates(s.core_states),
//        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
//{
//}

pub proof fn lemma_unique_and_overlap_values_implies_overlap_vmem<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
)
    requires
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
        s.basic_inv(c),
    ensures
        s.inflight_map_no_overlap_inflight_vmem(c),
{
    assert(forall|core| #[trigger] hardware::valid_core(c.hw, core) ==> s.core_states.contains_key(core));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata to help proof inflight_map_no_overlap_inflight_vmem
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//pub proof fn lemma_insert_idle_corestate_preserves_no_overlap(
//    c: os::Constants,
//    core_states: Map<Core, os::CoreState>,
//    pt: Map<nat, PTE>,
//    core: Core,
//)
//    requires
//        core_states.dom().contains(core),
//        unique_CoreStates(core_states),
//        no_overlap_vmem_values(core_states, pt),
//    ensures
//        unique_CoreStates(core_states.insert(core, os::CoreState::Idle)),
//        no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt),
//{
//    assert forall|a|
//        #![auto]
//        core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() implies !core_states.insert(core, os::CoreState::Idle).remove(
//        a,
//    ).values().contains(core_states.insert(core, os::CoreState::Idle).index(a)) by {
//        if (core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() && a != core) {
//            assert(core_states.dom().contains(a));
//            assert(core_states.index(a) == core_states.insert(core, os::CoreState::Idle).index(a));
//            assert(!core_states.index(a).is_idle());
//            assert(!core_states.remove(a).values().contains(core_states.index(a)));
//
//            assert(core_states.insert(core, os::CoreState::Idle).remove(a) =~= core_states.remove(
//                a,
//            ).insert(core, os::CoreState::Idle));
//
//            lemma_map_insert_values_equality(core_states.remove(a), core, os::CoreState::Idle);
//        }
//    };
//    assert(no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt));
//}

pub proof fn lemma_insert_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    corestate: os::CoreState,
)
    requires
        corestate.holds_lock(),
        forall|cr|
            #![auto]
            core_states.dom().contains(cr) && core_states[cr].holds_lock() ==> cr == core,
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        !core_states[core].is_idle(),
        !corestate.is_idle(),
        core_states[core].vaddr() == corestate.vaddr(),
        core_states[core].vmem_pte_size(pt) >= corestate.vmem_pte_size(pt),
        core_states[core] != corestate,
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(core_states.insert(core, corestate), pt),
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

pub proof fn lemma_insert_no_overlap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    corestate: os::CoreState,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
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
        no_overlap_vmem_values(core_states.insert(core, corestate), pt),
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

pub proof fn lemma_submap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    sub_pt: Map<nat, PTE>,
)
    requires
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        sub_pt.submap_of(pt),
    ensures
        no_overlap_vmem_values(core_states, sub_pt),
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
pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
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
    assert  (os::candidate_mapping_overlaps_inflight_vmem(
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
                        os::CoreState::UnmapWaiting { vaddr, .. }
                        | os::CoreState::UnmapOpExecuting { vaddr, result: None, .. } => {
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
                        os::CoreState::UnmapOpExecuting { vaddr, result: Some(result), .. }
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
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    //assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.contains_key(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    //if result is Ok {}
                },
                _ => {},
            };
        } 
    };
}

pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
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
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
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
            let ult_id = choose|id| #[trigger]
                c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(hardware::valid_core(c.hw, core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id2 == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
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
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapOpExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(ult_id2 == ult_id);
                    if s.interp_pt_mem().dom().contains(vaddr) {
                        let pte = s.interp_pt_mem()[vaddr];
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
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
                            &&& thread_state matches hlspec::ThreadState::Unmap {
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
                os::CoreState::UnmapOpExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    if result is Ok {
                        assert(ult_id2 == ult_id);
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
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
                            &&& thread_state matches hlspec::ThreadState::Unmap {
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
        }
    };

}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
    candidate: PTE,
)
    requires
        s.basic_inv(c),
        candidate.frame.size > 0,
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
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: None, .. } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                        },
                        os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: Some(result), .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
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
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& p_te === pte
                        &&& overlap(candidate.frame, pte.frame)
                    });
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_address,
                            pte: Some(pte),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === pte
                        &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                    });
                },
                os::CoreState::UnmapOpExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
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
        } 
    };
}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
    candidate: PTE,
)
    requires
        s.basic_inv(c),
        candidate.frame.size > 0,
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
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
                            &&& pte.is_some()
                            &&& overlap(candidate.frame, pte.unwrap().frame)
                        },
                        _ => { false },
                    }
                };
            let ult_id = choose|id| #[trigger]
                c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(hardware::valid_core(c.hw, core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, pte.frame));
                },
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapOpExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ult_id);
                    let pte = s.interp_pt_mem()[vaddr];
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame));
                },
                os::CoreState::UnmapOpExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
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
        }
    };
}

pub proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    assert forall|values| #![auto] map.values().insert(value).contains(values)
        implies map.insert(key, value).values().insert(map.index(key)).contains(values)
    by {
        if values == value {
            lemma_map_insert_value(map, key, value);
        } else {
            let k = choose|some_key| #[trigger]
                map.dom().contains(some_key) && (map[some_key] == values);
            assert(map.insert(key, value).dom().contains(k));
            if (k == key) {
                assert(map.index(key) == values);
            } else {
                assert(map[k] === map.insert(key, value)[k]);
            }
        }
    }
    assert(map.values().insert(value) =~= map.insert(key, value).values().insert(map.index(key)));
}

pub proof fn lemma_map_insert_value<A, B>(map: Map<A, B>, key: A, value: B)
    requires
    ensures
        map.insert(key, value).values().contains(value),
{
    assert(map.insert(key, value).dom().contains(key));
    assert(map.insert(key, value)[key] == value);
}

} // verus!
