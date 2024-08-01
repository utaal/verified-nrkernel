use vstd::prelude::*;

//use crate::impl_u::spec_pt;
//use crate::spec_t::hardware::Core;
use crate::definitions_t::{above_zero, overlap, MemRegion, PageTableEntry};
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
            os::CoreState::UnmapOpDone { vaddr, .. }
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
    next_step_preserves_overlapping_inv(c, s1, s2, step);

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
    /*
    assert(s.TLB_Shootdown.open_requests.is_empty());
    Set::lemma_len0_is_empty(s.TLB_Shootdown.open_requests);
    assert(s.TLB_Shootdown.open_requests === Set::empty());
    assert(forall|core| #[trigger]
        hardware::valid_core(c.hw, core)
            ==> s.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().is_empty());
    assert(s.shootdown_cores_valid(c));
    assert(s.successful_IPI(c));
    assert(s.successful_shootdown(c));
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));*/
    admit();
}

pub proof fn next_step_preserves_tlb_inv(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        s1.tlb_inv(c),
        s1.inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.tlb_inv(c),
{
    /*
    match step {
               os::OSStep::HW { ULT_id, step } => {
            match step {
                hardware::HWStep::TLBFill { vaddr, pte, core } => {
                    assert(s2.shootdown_cores_valid(c));
                    assume(s2.successful_IPI(c));
                    assume(s2.successful_shootdown(c));
                },
                hardware::HWStep::TLBEvict { vaddr, core } => {
                    assert(s2.shootdown_cores_valid(c));
                    assume(s2.successful_IPI(c));
                    assume(s2.successful_shootdown(c));
                },
                _ => {},
            }
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));
        },
        os::OSStep::MapEnd { core, result } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));

        },
        os::OSStep::UnmapOpEnd { core, result } => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));

        },
        _ => {
            assert(s2.shootdown_cores_valid(c));
            assume(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));
        },
    }*/
    admit();
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of overlapping Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_overlapping_inv(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s),
    ensures
        s.overlapping_inv(c),
{
}

pub proof fn next_step_preserves_overlapping_inv(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        s1.overlapping_inv(c),
        s1.basic_inv(c),
        s2.basic_inv(c),
        os::next_step(c, s1, s2, step),
    ensures
        s2.overlapping_inv(c),
{  //assert(forall |core1, core2|)
    if (s1.sound) {
        match step {
            os::OSStep::HW { ULT_id, step } => match step {
                _ => {
                    assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                    lemma_preserve_no_overlap_inflight_pmem_if_thread_state_consistent(c, s1, s2);
                },
            },
            //Map steps
            os::OSStep::MapStart { ULT_id, vaddr, pte: candidate } => {
                if (s2.sound) {
                    /*pub open spec fn step_Map_sound(
                pt: Map<nat, PageTableEntry>,
                inflightargs: Set<CoreState>,
                vaddr: nat,
                pte: PageTableEntry,
                ) -> bool {
                &&& !candidate_mapping_overlaps_existing_pmem(pt, pte)
                &&& !candidate_mapping_overlaps_inflight_pmem(pt, inflightargs, pte)
                &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte)
                } */
                    //TODO
                    assert(os::step_Map_sound(
                        s1.interp_pt_mem(),
                        s1.core_states.values(),
                        vaddr,
                        candidate,
                    ));
                    assert(!os::candidate_mapping_overlaps_inflight_pmem(
                        s1.interp_pt_mem(),
                        s1.core_states.values(),
                        candidate,
                    ));
                    assume(!exists|b|
                        #![auto]
                        {
                            &&& s1.core_states.values().contains(b)
                            &&& match b {
                                os::CoreState::MapWaiting { vaddr, pte, .. }
                                | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                                    overlap(candidate.frame, pte.frame)
                                },
                                os::CoreState::UnmapWaiting { ULT_id, vaddr }
                                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                                    &&& s1.interp_pt_mem().dom().contains(vaddr)
                                    &&& overlap(
                                        candidate.frame,
                                        s1.interp_pt_mem().index(vaddr).frame,
                                    )
                                },
                                os::CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                                | os::CoreState::UnmapShootdownWaiting {
                                    ULT_id,
                                    vaddr,
                                    pte,
                                    ..
                                } => {
                                    &&& pte is Some
                                    &&& overlap(candidate.frame, pte.unwrap().frame)
                                },
                                os::CoreState::Idle => false,
                            }
                        });
                    assume(s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c));

                } else {
                }
            },
            os::OSStep::MapOpStart { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_preserve_no_overlap_inflight_pmem_if_thread_state_consistent(c, s1, s2);
            },
            os::OSStep::MapEnd { core, result } => {
                //TODO
                if (s1.sound) {
                    assume(s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c));
                    assume(s2.sound_implies_inflight_map_no_overlap_existing_pmem(c));
                    assume(s2.sound_implies_existing_map_no_overlap_existing_pmem(c));
                } else {
                }
            },
            //Unmap steps
            os::OSStep::UnmapStart { ULT_id, vaddr } => {
                //TODO
                if (s2.sound) {
                    let pt = s1.interp_pt_mem();
                    assert(!pt.contains_key(vaddr) || !os::candidate_mapping_overlaps_inflight_vmem(
                        pt,
                        s1.core_states.values(),
                        vaddr,
                        pt.index(vaddr),
                    ));
                    if !pt.contains_key(vaddr) {
                        assume(s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c));
                    } else {
                        assume(s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c));
                    }
                    assert(s2.interp_pt_mem() =~= s1.interp_pt_mem());
                } else {
                }
            },
            os::OSStep::UnmapOpStart { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_preserve_no_overlap_inflight_pmem_if_thread_state_consistent(c, s1, s2);
            },
            os::OSStep::UnmapOpEnd { core, result } => {
                //TODO
                if (s1.sound) {
                    assume(s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c));
                    assert(s2.sound_implies_inflight_map_no_overlap_existing_pmem(c));
                    assert(s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));

                    assume(s2.sound_implies_existing_map_no_overlap_existing_pmem(c));
                } else {
                }
            },
            os::OSStep::UnmapInitiateShootdown { core } => {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_preserve_no_overlap_inflight_pmem_if_thread_state_consistent(c, s1, s2);
            },
            os::OSStep::UnmapEnd { core } => {
                assert forall|cr|
                    hardware::valid_core(c.hw, cr)
                        && #[trigger] s2.core_states[cr].is_map() implies !os::candidate_mapping_overlaps_inflight_pmem(

                    s2.interp_pt_mem(),
                    s2.set_core_idle(c, cr).core_states.values(),
                    s2.core_states[cr].map_pte(),
                ) by {
                    if (hardware::valid_core(c.hw, cr) && s1.core_states[cr].is_map()) {
                        let candidate = s1.core_states[cr].map_pte();
                        assert(cr != core);
                        assert(s1.core_states[cr] === s2.core_states[cr]);
                        map_values_contain_value_of_contained_key(s2.core_states, cr);
                        if (os::candidate_mapping_overlaps_inflight_pmem(
                            s2.interp_pt_mem(),
                            s2.set_core_idle(c, cr).core_states.values(),
                            s2.core_states[cr].map_pte(),
                        )) {
                            let overlap = choose|b: os::CoreState|
                                #![auto]
                                {
                                    &&& s2.set_core_idle(c, cr).core_states.values().contains(b)
                                    &&& match b {
                                        os::CoreState::MapWaiting { vaddr, pte, .. }
                                        | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                                            overlap(s2.core_states[cr].map_pte().frame, pte.frame)
                                        },
                                        os::CoreState::UnmapWaiting { ULT_id, vaddr }
                                        | os::CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                                            &&& s2.interp_pt_mem().dom().contains(vaddr)
                                            &&& overlap(
                                                s2.core_states[cr].map_pte().frame,
                                                s2.interp_pt_mem().index(vaddr).frame,
                                            )
                                        },
                                        os::CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                                        | os::CoreState::UnmapShootdownWaiting {
                                            ULT_id,
                                            vaddr,
                                            pte,
                                            ..
                                        } => {
                                            &&& pte is Some
                                            &&& overlap(
                                                s2.core_states[cr].map_pte().frame,
                                                pte.unwrap().frame,
                                            )
                                        },
                                        os::CoreState::Idle => false,
                                    }
                                };
                            let overlap_core = choose|some_core| #[trigger]
                                hardware::valid_core(c.hw, some_core) && (s2.set_core_idle(
                                    c,
                                    cr,
                                ).core_states[some_core] == overlap) && !(some_core === cr);
                            assert(overlap_core != core);
                            assert(s1.core_states[overlap_core] === s2.core_states[overlap_core]);
                            assert(s1.core_states[overlap_core] === overlap);
                            lemma_map_insert_values_equality(
                                s1.core_states,
                                core,
                                os::CoreState::Idle,
                            );
                            assert(s1.core_states.values().insert(os::CoreState::Idle)
                                =~= s2.core_states.values().insert(s1.core_states[core]));
                            lemma_map_insert_values_equality(
                                s2.core_states,
                                cr,
                                os::CoreState::Idle,
                            );
                            assert(s2.core_states.values().insert(os::CoreState::Idle)
                                =~= s2.set_core_idle(c, cr).core_states.values().insert(
                                s2.core_states[cr],
                            ));
                            lemma_map_insert_values_equality(
                                s1.core_states,
                                cr,
                                os::CoreState::Idle,
                            );
                            assert(s1.core_states.values().insert(os::CoreState::Idle)
                                =~= s1.set_core_idle(c, cr).core_states.values().insert(
                                s1.core_states[cr],
                            ));
                            map_values_contain_value_of_contained_key(
                                s1.set_core_idle(c, cr).core_states,
                                overlap_core,
                            );
                            match overlap {
                                os::CoreState::MapWaiting { vaddr, pte, .. } => {
                                    assert(s1.core_states.values().contains(overlap));
                                    assert(s1.set_core_idle(c, cr).core_states.values().contains(
                                        overlap,
                                    ));
                                },
                                os::CoreState::UnmapWaiting { ULT_id, vaddr } => {
                                    assert(s1.core_states.values().contains(overlap));
                                    assert(s1.set_core_idle(c, cr).core_states.values().contains(
                                        overlap,
                                    ));
                                },
                                os::CoreState::UnmapOpDone { .. }
                                | os::CoreState::UnmapShootdownWaiting { .. }
                                | os::CoreState::UnmapOpExecuting { .. }
                                | os::CoreState::MapExecuting { .. } => {
                                    assert(overlap.holds_lock());
                                },
                                os::CoreState::Idle => {},
                            }
                        } else {
                        }
                    } else {
                    }
                }
            },
            _ => {},
        }
    } else {
    }
}

proof fn lemma_thread_state_consistent_set_map_core_idle(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    core: hardware::Core,
)
    requires
        s1.interp(c).thread_state === s2.interp(c).thread_state,
        s1.interp_pt_mem() === s2.interp_pt_mem(),
        s1.basic_inv(c),
        s2.basic_inv(c),
        hardware::valid_core(c.hw, core),
        !s1.core_states[core].is_unmap(),
    ensures
        s1.set_core_idle(c, core).interp(c).thread_state === s2.set_core_idle(c, core).interp(
            c,
        ).thread_state,
{
    assert forall|cores| hardware::valid_core(c.hw, cores) implies (forall|ULT_id|
        (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores) ==> s1.set_core_idle(
            c,
            core,
        ).interp(c).thread_state[ULT_id] === s2.set_core_idle(c, core).interp(
            c,
        ).thread_state[ULT_id]) by {
        if (cores == core) {
            assert(s1.set_core_idle(c, core).core_states[core] is Idle);
            assert(s2.set_core_idle(c, core).core_states[core] is Idle);
            assert(forall|ULT_id|
                (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores)
                    ==> s1.set_core_idle(c, core).interp(c).thread_state[ULT_id] is Empty);
            assert(forall|ULT_id|
                (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores)
                    ==> s2.set_core_idle(c, core).interp(c).thread_state[ULT_id] is Empty);
        } else {
            assert(s1.set_core_idle(c, core).core_states[cores] === s1.core_states[cores]);
            assert(s2.set_core_idle(c, core).core_states[cores] === s2.core_states[cores]);
            match s1.core_states[cores] {
                os::CoreState::MapWaiting { ULT_id: ult, .. }
                | os::CoreState::MapExecuting { ULT_id: ult, .. } => {
                    assert(forall|ULT_id|
                        (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores && ULT_id
                            != ult) ==> s1.interp(c).thread_state[ULT_id] is Empty);
                },
                os::CoreState::UnmapWaiting { ULT_id: ult, .. }
                | os::CoreState::UnmapOpExecuting { ULT_id: ult, .. }
                | os::CoreState::UnmapOpDone { ULT_id: ult, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult, .. } => {
                    assert(forall|ULT_id|
                        (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores && ULT_id
                            != ult) ==> s1.interp(c).thread_state[ULT_id] is Empty);
                },
                os::CoreState::Idle => {
                    assert(s1.core_states[cores] is Idle);
                    assert(s1.set_core_idle(c, core).core_states[cores] is Idle);
                    assert(forall|ULT_id|
                        (#[trigger] c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == cores)
                            ==> s1.interp(c).thread_state[ULT_id] is Empty);
                },
            }
        }
    }
    assert(forall|ULT_id| #[trigger]
        c.valid_ULT(ULT_id) ==> hardware::valid_core(c.hw, c.ULT2core[ULT_id]));
    assert(s1.set_core_idle(c, core).interp(c).thread_state.dom() === s2.set_core_idle(
        c,
        core,
    ).interp(c).thread_state.dom());
    assert(s1.set_core_idle(c, core).interp(c).thread_state === s2.set_core_idle(c, core).interp(
        c,
    ).thread_state);
}

pub proof fn lemma_thread_state_preserves_core_state_type(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    core: hardware::Core,
)
    requires
        forall|ULT_id|
            (c.valid_ULT(ULT_id) && c.ULT2core[ULT_id] == core) ==> #[trigger] s1.interp(
                c,
            ).thread_state[ULT_id] === s2.interp(c).thread_state[ULT_id],
        //s1.interp_pt_mem() === s2.interp_pt_mem(),
        hardware::valid_core(c.hw, core),
        s1.basic_inv(c),
        s2.basic_inv(c),
    ensures
        s1.core_states[core].is_map() ==> s2.core_states[core].is_map(),
        s1.core_states[core].is_map() ==> (s1.core_states[core].map_pte()
            === s2.core_states[core].map_pte()),
{
    match s1.core_states[core] {
        os::CoreState::MapWaiting { ULT_id, pte, .. }
        | os::CoreState::MapExecuting { ULT_id, pte, .. } => {
            assert(s1.interp(c).thread_state[ULT_id] is Map);
            assert(s1.core_states[core].is_map());
            match s1.interp(c).thread_state[ULT_id] {
                hlspec::AbstractArguments::Map { vaddr: Vaddr, pte: Pte, .. } => {
                    assert(pte == Pte);
                    assert(s2.core_states[core].is_map());
                },
                _ => { assert(false) },
            }
        },
        _ => {},
    }
}

proof fn lemma_preserve_no_overlap_inflight_pmem_if_thread_state_consistent(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
)
    requires
        s1.basic_inv(c),
        s2.basic_inv(c),
        s1.sound_implies_inflight_map_no_overlap_inflight_pmem(c),
        s1.interp_thread_state(c) == s2.interp_thread_state(c),
        s1.interp_pt_mem() == s2.interp_pt_mem(),
        s1.sound,
        s2.sound,
    ensures
        s2.sound_implies_inflight_map_no_overlap_inflight_pmem(c),
{
    assert forall|core: hardware::Core| hardware::valid_core(c.hw, core) implies {
        match s2.core_states[core] {
            os::CoreState::MapWaiting { vaddr, pte, .. }
            | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                !os::candidate_mapping_overlaps_inflight_pmem(
                    s2.interp_pt_mem(),
                    s2.set_core_idle(c, core).core_states.values(),
                    pte,
                )
            },
            _ => { true },
        }
    } by {
        if (hardware::valid_core(c.hw, core)) {
            assert(hardware::valid_core(c.hw, core));
            assert(s1.core_states.dom() === s2.core_states.dom());
            lemma_thread_state_preserves_core_state_type(c, s1, s2, core);
            lemma_thread_state_preserves_core_state_type(c, s2, s1, core);
            match s1.core_states[core] {
                os::CoreState::MapWaiting { vaddr, pte, .. }
                | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                    assert(!os::candidate_mapping_overlaps_inflight_pmem(
                        s1.interp_pt_mem(),
                        s1.set_core_idle(c, core).core_states.values(),
                        pte,
                    ));
                    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(
                        c,
                        s1.set_core_idle(c, core),
                        pte,
                    );
                    assert(!hlspec::candidate_mapping_overlaps_inflight_pmem(
                        s1.set_core_idle(c, core).interp(c).thread_state.values(),
                        pte,
                    ));
                    lemma_thread_state_consistent_set_map_core_idle(c, s1, s2, core);
                    assert(s1.set_core_idle(c, core).interp(c).thread_state.values()
                        =~= s2.set_core_idle(c, core).interp(c).thread_state.values());
                    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(
                        c,
                        s2.set_core_idle(c, core),
                        pte,
                    );
                    assert(s2.core_states[core].is_map());
                    assert(!os::candidate_mapping_overlaps_inflight_pmem(
                        s2.interp_pt_mem(),
                        s2.set_core_idle(c, core).core_states.values(),
                        pte,
                    ));
                },
                _ => {},
            }
        } else {
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// candidate_mapping_overlaps_inflight_pmem set lemma
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*
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
                CoreState::MapWaiting { vaddr, pte, .. }
                | CoreState::MapExecuting { vaddr, pte, .. } => {
                    overlap(candidate.frame, pte.frame)
                },
                CoreState::UnmapWaiting { ULT_id, vaddr }
                | CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                    &&& pt.dom().contains(vaddr)
                    &&& overlap(candidate.frame, pt.index(vaddr).frame)
                },
                CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                | CoreState::UnmapShootdownWaiting { ULT_id, vaddr, pte, .. } => {
                    &&& pte is Some
                    &&& overlap(candidate.frame, pte.unwrap().frame)
                },
                CoreState::Idle => false,
            }
        }
}
*/

proof fn lemma_idle_insert_no_overlap(
    pt: Map<nat, PageTableEntry>,
    core_states: Set<os::CoreState>,
    candidate: PageTableEntry,
)
    requires
        os::candidate_mapping_overlaps_inflight_pmem(pt, core_states, candidate),
    ensures
        os::candidate_mapping_overlaps_inflight_pmem(
            pt,
            core_states.insert(os::CoreState::Idle),
            candidate,
        ),
{
    admit();
}

proof fn lemma_subset_no_overlap(
    pt: Map<nat, PageTableEntry>,
    super_core_states: Set<os::CoreState>,
    core_states: Set<os::CoreState>,
    candidate: PageTableEntry,
)
    requires
        os::candidate_mapping_overlaps_inflight_pmem(pt, super_core_states, candidate),
        core_states.subset_of(super_core_states),
    ensures
        os::candidate_mapping_overlaps_inflight_pmem(pt, core_states, candidate),
{
    admit();
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unique definition and equivalence
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn if_map_then_unique(c: os::OSConstants, s: os::OSVariables) -> bool {
    forall|core|
        hardware::valid_core(c.hw, core) && #[trigger] s.core_states[core].is_map()
            ==> !s.core_states.remove(core).values().contains(s.core_states[core])
}

pub open spec fn core_state_inflight_map_no_overlap_inflight_pmem(
    c: os::OSConstants,
    pt: Map<nat, PageTableEntry>,
    corestates: Set<os::CoreState>,
) -> bool {
    forall|cs|
        #![auto]
        {
            corestates.contains(cs) && cs.is_map()
                ==> !os::candidate_mapping_overlaps_inflight_pmem(
                pt,
                corestates.remove(cs),
                cs.map_pte(),
            )
        }
}

proof fn lemma_unique_no_overlap_core_states_implies_no_inflight_overlap_pmem(
    c: os::OSConstants,
    s: os::OSVariables,
)
    requires
        if_map_then_unique(c, s),
        core_state_inflight_map_no_overlap_inflight_pmem(
            c,
            s.interp_pt_mem(),
            s.core_states.values(),
        ),
        s.sound,
        s.basic_inv(c),
    ensures
        s.sound_implies_inflight_map_no_overlap_inflight_pmem(c),
{
    assert forall|core|
        hardware::valid_core(c.hw, core)
            && #[trigger] s.core_states[core].is_map() implies !os::candidate_mapping_overlaps_inflight_pmem(

        s.interp_pt_mem(),
        s.set_core_idle(c, core).core_states.values(),
        s.core_states[core].map_pte(),
    ) by {
        if (hardware::valid_core(c.hw, core) && #[trigger] s.core_states[core].is_map()) {
            admit();
        } else {
            assert(false);
        }
    }
}

proof fn lemma_no_inflight_overlap_pmem_implies_unique_no_overlap_core_states_(
    c: os::OSConstants,
    s: os::OSVariables,
)
    requires
        s.sound_implies_inflight_map_no_overlap_inflight_pmem(c),
        s.sound,
    ensures
        if_map_then_unique(c, s),
        core_state_inflight_map_no_overlap_inflight_pmem(
            c,
            s.interp_pt_mem(),
            s.core_states.values(),
        ),
{
    admit();
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(
    c: os::OSConstants,
    s: os::OSVariables,
    base: nat,
    candidate: PageTableEntry,
)
    requires
        s.basic_inv(c),
        above_zero(candidate.frame.size),
    ensures
        os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate,
    )) by {
        if (os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate,
        )) {
            let corestate = choose|b: os::CoreState|
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate.frame.size },
                            )
                        },
                        os::CoreState::UnmapWaiting { vaddr, .. }
                        | os::CoreState::UnmapOpExecuting { vaddr, .. } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(
                                MemRegion {
                                    base: vaddr,
                                    size: s.interp_pt_mem().index(vaddr).frame.size,
                                },
                                MemRegion { base: base, size: candidate.frame.size },
                            )
                        },
                        os::CoreState::UnmapOpDone { vaddr, pte, .. }
                        | os::CoreState::UnmapShootdownWaiting { vaddr, pte, .. } => {
                            &&& pte is Some
                            &&& overlap(
                                MemRegion { base: vaddr, size: pte.unwrap().frame.size },
                                MemRegion { base: base, size: candidate.frame.size },
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
                            MemRegion { base: base, size: candidate.frame.size },
                        )
                    });
                },
                os::CoreState::UnmapWaiting { ULT_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(p_te),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === p_te
                        &&& overlap(
                            MemRegion { base: v_address, size: p_te.frame.size },
                            MemRegion { base: base, size: candidate.frame.size },
                        )
                    });
                },
                os::CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, pte, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(p_te),
                        }
                        &&& v_address === vaddr
                        &&& pte === Some(p_te)
                        &&& overlap(
                            MemRegion { base: v_address, size: p_te.frame.size },
                            MemRegion { base: base, size: candidate.frame.size },
                        )
                    });
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
    candidate: PageTableEntry,
)
    requires
        s.basic_inv(c),
        above_zero(candidate.frame.size),
    ensures
        hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate,
        ) ==> os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate,
    ) ==> os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate,
    )) by {
        if (hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate,
        )) {
            let thread_state = choose|b|
                {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::AbstractArguments::Map { vaddr, pte } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate.frame.size },
                            )
                        },
                        hlspec::AbstractArguments::Unmap { vaddr, pte } => {
                            &&& pte.is_some()
                            &&& overlap(
                                MemRegion { base: vaddr, size: pte.unwrap().frame.size },
                                MemRegion { base: base, size: candidate.frame.size },
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
                    assert(above_zero(pte.frame.size));
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
                        MemRegion { base: base, size: candidate.frame.size },
                    ));
                },
                os::CoreState::UnmapWaiting { ULT_id: ult_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ULT_id);
                    let pte = s.interp_pt_mem()[vaddr];
                    assert(above_zero(pte.frame.size));
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
                        MemRegion { base: base, size: candidate.frame.size },
                    ));
                },
                os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, pte, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, pte, .. } => {
                    assert(ult_id == ULT_id);
                    assert(above_zero(pte.unwrap().frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& Some(entry) === pte
                    });
                    assert(overlap(
                        MemRegion { base: vaddr, size: pte.unwrap().frame.size },
                        MemRegion { base: base, size: candidate.frame.size },
                    ));
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
        if (os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        )) {
            let corestate = choose|b: os::CoreState|
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        os::CoreState::UnmapWaiting { ULT_id, vaddr }
                        | os::CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                        },
                        os::CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                        | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, pte, .. } => {
                            &&& pte is Some
                            &&& overlap(candidate.frame, pte.unwrap().frame)
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
                os::CoreState::UnmapWaiting { ULT_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(p_te),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === p_te
                        &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                    });
                },
                os::CoreState::UnmapOpDone { ULT_id, vaddr, pte, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, pte, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.dom().contains(ULT_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& pte === p_te
                        &&& overlap(candidate.frame, pte.unwrap().frame)
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
                    assert(above_zero(pte.frame.size));
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
                os::CoreState::UnmapWaiting { ULT_id: ult_id, vaddr }
                | os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ULT_id);
                    let pte = s.interp_pt_mem()[vaddr];
                    assert(above_zero(pte.frame.size));
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
                os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, pte, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, pte, .. } => {
                    assert(ult_id == ULT_id);
                    assert(above_zero(pte.unwrap().frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_addr,
                            pte: p_te,
                        }
                        &&& vaddr === v_addr
                        &&& p_te === pte
                    });
                    assert(overlap(candidate.frame, pte.unwrap().frame));
                },
                _ => {},
            };
        } else {
        }
    };
}

} // verus!
