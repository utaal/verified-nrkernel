use vstd::prelude::*;

//use crate::impl_u::spec_pt;
//use crate::spec_t::hardware::Core;
use crate::definitions_t::{
    above_zero, aligned, between, candidate_mapping_overlaps_existing_pmem, overlap, HWLoadResult,
    HWRWOp, HWStoreResult, LoadResult, MemRegion, PageTableEntry, RWOp, StoreResult,
};
use crate::spec_t::{hardware, hlspec, mem, os};

verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of Invariant
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn init_implies_inv(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s),
    ensures
        s.inv(c),
{
    init_implies_tlb_inv(c, s);
}

proof fn next_preserves_inv(c: os::OSConstants, s1: os::OSVariables, s2: os::OSVariables)
    requires
        s1.inv(c),
        os::next(c, s1, s2),
    ensures
        s2.inv(c),
{
    let step = choose|step| os::next_step(c, s1, s2, step);
    next_step_preserves_inv(c, s1, s2, step);
}

proof fn next_step_preserves_inv(
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
    next_step_preserves_tlb_inv(c, s1, s2, step);
    admit();

}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of TLB Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*    pub open spec fn tlb_inv(self, c: OSConstants) -> bool {
    assert( s2.shootdown_cores_valid(c));
    assert( s2.successful_IPI(c));
    assert( s2.successful_shootdown(c));
    assert( s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));
}
*/

proof fn init_implies_tlb_inv(c: os::OSConstants, s: os::OSVariables)
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
    assert(s.successful_shootdown(c));
    assert(s.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));
}

proof fn next_step_preserves_tlb_inv(
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
    match step {
        os::OSStep::HW { ULT_id, step } => {
            match step {
                hardware::HWStep::TLBFill { vaddr, pte, core } => {
                    assert(s2.shootdown_cores_valid(c));
                    assume(s2.successful_IPI(c));
                    assume(s2.successful_shootdown(c));
                    assume(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));
                },
                hardware::HWStep::TLBEvict { vaddr, core } => {
                    assert(s2.shootdown_cores_valid(c));
                    assume(s2.successful_IPI(c));
                    assume(s2.successful_shootdown(c));
                    assume(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));
                },
                _ => {},
            }
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));
            assert(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::MapEnd { core, result } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));
            assume(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));

        },
        os::OSStep::UnmapOpEnd { core, result } => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assume(s2.successful_shootdown(c));
            assume(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c));

        },
        _ => {
            assert(s2.shootdown_cores_valid(c));
            assert(s2.successful_IPI(c));
            assert(s2.successful_shootdown(c));
            assert(s2.TLB_dom_supset_of_pt_and_inflight_unmap_vaddr(c))
        },
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_inflight_vaddr_equals_hl_unmap(c: os::OSConstants, s: os::OSVariables)
    requires
        s.inv(c),
    ensures
        forall|v_addr|
            s.inflight_unmap_vaddr().contains(v_addr) <==> exists|thread_state|
                {
                    &&& s.interp_thread_state(c).values().contains(thread_state)
                    &&& s.interp_pt_mem().dom().contains(v_addr)
                    &&& thread_state matches hlspec::AbstractArguments::Unmap { vaddr, .. }
                    &&& vaddr === v_addr
                },
{
    // proof ==> direction
    assert forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr) implies exists|thread_state|
        {
            &&& s.interp_thread_state(c).values().contains(thread_state)
            &&& s.interp_pt_mem().dom().contains(v_addr)
            &&& thread_state matches hlspec::AbstractArguments::Unmap { vaddr, .. }
            &&& vaddr === v_addr
        } by {
        let core = choose|core|
            {
                &&& s.core_states.dom().contains(core)
                &&& ({
                    &&& s.core_states[core] matches os::CoreState::UnmapWaiting { vaddr, .. }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapOpExecuting { vaddr, .. }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapOpDone { vaddr, .. }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapShootdownWaiting {
                        vaddr,
                        ..
                    }
                    &&& vaddr == v_addr
                })
            };
        //assert(hardware::valid_core(c.hw, core));
        match s.core_states[core] {
            os::CoreState::UnmapWaiting { ULT_id, vaddr }
            | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
            | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                assert(s.interp_thread_state(c).dom().contains(ULT_id));
                let thread_state = s.interp_thread_state(c)[ULT_id];
                assert(s.interp_thread_state(c).values().contains(thread_state));
            },
            _ => {
                assert(false);
            },
        }
    };
    // proof  <== diretion
    assert forall|v_addr|
        exists|thread_state|
            {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().dom().contains(v_addr)
                &&& thread_state matches hlspec::AbstractArguments::Unmap { vaddr, .. }
                &&& vaddr === v_addr
            } implies s.inflight_unmap_vaddr().contains(v_addr) by {
        let thread_state = choose|thread_state|
            {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& thread_state matches hlspec::AbstractArguments::Unmap { vaddr, pte }
                &&& vaddr == v_addr
            };
        let ULT_id = choose|id| #[trigger]
            s.interp_thread_state(c).dom().contains(id) && s.interp_thread_state(c)[id]
                === thread_state;
        assert(s.core_states.dom().contains(c.ULT2core[ULT_id]));
    };

}

proof fn lemma_effective_mappings_unaffected_if_thread_state_constant(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.interp_thread_state(c) === s2.interp_thread_state(c),
        s1.interp_pt_mem() === s2.interp_pt_mem(),
    ensures
        s1.effective_mappings() === s2.effective_mappings(),
{
    lemma_inflight_vaddr_equals_hl_unmap(c, s1);
    lemma_inflight_vaddr_equals_hl_unmap(c, s2);
    assert(s2.inflight_unmap_vaddr() =~= s1.inflight_unmap_vaddr());
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    admit();
}

proof fn lemma_map_equality<A, B>(map1: Map<A, B>, map2: Map<A, B>)
    requires
        map1.dom() === map2.dom(),
        forall|key, value| map1.contains_pair(key, value) ==> map2.contains_pair(key, value),
        forall|key, value| map2.contains_pair(key, value) ==> map1.contains_pair(key, value),
    ensures
        map1 === map2,
{
    admit();
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(
    c: os::OSConstants,
    s: os::OSVariables,
    base: nat,
    candidate: PageTableEntry,
)
    requires
        s.inv(c),
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

proof fn lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(
    c: os::OSConstants,
    s: os::OSVariables,
    base: nat,
    candidate: PageTableEntry,
)
    requires
        s.inv(c),
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

proof fn lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(
    c: os::OSConstants,
    s: os::OSVariables,
    candidate: PageTableEntry,
)
    requires
        s.inv(c),
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

proof fn lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(
    c: os::OSConstants,
    s: os::OSVariables,
    candidate: PageTableEntry,
)
    requires
        s.inv(c),
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

proof fn lemma_map_soundness_equality(
    c: os::OSConstants,
    s: os::OSVariables,
    vaddr: nat,
    pte: PageTableEntry,
)
    requires
        s.inv(c),
        above_zero(pte.frame.size),
    ensures
        hlspec::step_Map_sound(s.interp(c).mappings, s.interp(c).thread_state.values(), vaddr, pte)
            <==> os::step_Map_sound(s.interp_pt_mem(), s.core_states.values(), vaddr, pte),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte);
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(c, s, pte);
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(c, s, pte);
    assert(candidate_mapping_overlaps_existing_pmem(s.interp(c).mappings, pte)
        ==> candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte));

    assert(candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte) ==> (
    candidate_mapping_overlaps_existing_pmem(s.interp(c).mappings, pte)
        || hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        pte,
    ))) by {
        if candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte) {
            if (!os::candidate_mapping_overlaps_inflight_pmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                pte,
            )) {
                let base = choose|b: nat|
                    #![auto]
                    {
                        &&& s.interp_pt_mem().dom().contains(b)
                        &&& overlap(pte.frame, s.interp_pt_mem().index(b).frame)
                    };
                if (!s.inflight_unmap_vaddr().contains(base)) {
                    assert(s.effective_mappings().dom().contains(base));

                } else {
                    let core = choose|core|
                        s.core_states.dom().contains(core) && match s.core_states[core] {
                            os::CoreState::UnmapWaiting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                                vaddr === base
                            },
                            _ => false,
                        };
                    assert(s.core_states.values().contains(s.core_states.index(core)));
                    assert(os::candidate_mapping_overlaps_inflight_pmem(
                        s.interp_pt_mem(),
                        s.core_states.values(),
                        pte,
                    ));
                }
            } else {
            }
        } else {
        }
    }
}

proof fn lemma_unmap_soundness_equality(
    c: os::OSConstants,
    s: os::OSVariables,
    vaddr: nat,
    pte: PageTableEntry,
)
    requires
        s.inv(c),
        above_zero(pte.frame.size),
    ensures
        hlspec::step_Unmap_sound(s.interp(c).thread_state.values(), vaddr, pte)
            <==> os::step_Unmap_sound(s.interp_pt_mem(), s.core_states.values(), vaddr, pte),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn os_init_refines_hl_init(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s),
    ensures
        hlspec::init(c.interp(), s.interp(c)),
{
    let abs_c = c.interp();
    let abs_s = s.interp(c);
    //lemma_effective_mappings_equal_interp_pt_mem(s);
    assert forall|id: nat| id < abs_c.thread_no implies (abs_s.thread_state[id]
        === hlspec::AbstractArguments::Empty) by {
        assert(c.ULT2core.contains_key(id));
        let core = c.ULT2core[id];
        assert(hardware::valid_core(c.hw, core));
        assert(s.core_states[core] === os::CoreState::Idle);  //nn
    };
    assert(abs_s.mem === Map::empty());
    assert(abs_s.mappings === Map::empty());
}

proof fn os_next_refines_hl_next(c: os::OSConstants, s1: os::OSVariables, s2: os::OSVariables)
    requires
        os::next(c, s1, s2),
        s1.inv(c),
    ensures
        hlspec::next(c.interp(), s1.interp(c), s2.interp(c)),
{
    let step = choose|step: os::OSStep| os::next_step(c, s1, s2, step);
    next_step_refines_hl_next_step(c, s1, s2, step);
}

proof fn next_step_refines_hl_next_step(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    step: os::OSStep,
)
    requires
        os::next_step(c, s1, s2, step),
        s1.inv(c),
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(c, s1)),
{
    next_step_preserves_inv(c, s1, s2, step);
    match step {
        os::OSStep::HW { ULT_id, step } => match step {
            hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, core } => {
                step_ReadWrite_refines(c, s1, s2, ULT_id, vaddr, paddr, op, pte, core)
            },
            _ => {},
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => {
            step_Map_Start_refines(c, s1, s2, ULT_id, vaddr, pte);
        },
        os::OSStep::MapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::OSStep::MapEnd { core, result } => {
            step_Map_End_refines(c, s1, s2, core, result);
            let ULT_id = s1.core_states[core]->MapExecuting_ULT_id;
            //let result_2 = s1.core_states[core]->MapExecuting;
            //assert(interp( os::OSStep::MapEnd { core, result }, c, s1) matches hlspec::AbstractStep::UnmapEnd { thread_id, result });
            // assert (step.interp(c, s1) is UnmapEnd);
            //assert ({&&& step.interp(c, s1) matches hlspec::AbstractStep::UnmapEnd { thread_id, result: r }
            //        &&& thread_id == ULT_id
            //        &&& result == r});
            //assert(hlspec::step_Map_end(c.interp(), s1.interp(c), s2.interp(c), ULT_id, result));
            assert({
                &&& step.interp(c, s1) matches hlspec::AbstractStep::UnmapEnd {
                    thread_id,
                    result: r,
                }
                &&& hlspec::step_Map_end(c.interp(), s1.interp(c), s2.interp(c), thread_id, r)
            });
            assume(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(c, s1)));
        },
        //Unmap steps
        os::OSStep::UnmapStart { ULT_id, vaddr } => {
            step_Unmap_Start_refines(c, s1, s2, ULT_id, vaddr);
        },
        os::OSStep::UnmapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::OSStep::UnmapOpEnd { core, result } => {
            step_Unmap_Op_End_refines(c, s1, s2, core, result);
        },
        os::OSStep::UnmapInitiateShootdown { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::OSStep::UnmapEnd { core } => {
            step_Unmap_End_refines(c, s1, s2, core);
        },
        _ => {},
    }
}

/*

    &&& match pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(
                vaddr,
                base,
                base + pte.frame.size,
            )
            // .. and the result depends on the flags.

            &&& match op {
                RWOp::Store { new_value, result } => {
                    if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor
                        && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === s1.mem.insert(vmem_idx, new_value)
                    } else {
                        &&& result is Undefined
                        &&& s2.mem === s1.mem
                    }
                },
                RWOp::Load { is_exec, result } => {
                    &&& s2.mem === s1.mem
                    &&& if pmem_idx < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec
                        ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.index(vmem_idx)
                    } else {
                        &&& result is Undefined
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !mem_domain_from_mappings(c.phys_mem_size, s1.mappings).contains(
                vmem_idx,
            )
            // .. and the result is always a Undefined and an unchanged memory.

            &&& s2.mem === s1.mem
            &&& match op {
                RWOp::Store { new_value, result } => result is Undefined,
                RWOp::Load { is_exec, result } => result is Undefined,
            }
        },
    }
}

*/

proof fn step_ReadWrite_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    ULT_id: nat,
    vaddr: nat,
    paddr: nat,
    op: HWRWOp,
    pte: Option<(nat, PageTableEntry)>,
    core: hardware::Core,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_HW(c, s1, s2, ULT_id, hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, core }),
    ensures
        ({
            let hl_pte = if (pte is None || (pte matches Some((base, _))
                && s1.inflight_unmap_vaddr().contains(base))) {
                None
            } else {
                pte
            };
            let rwop = match (op, hl_pte) {
                (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, Some(_)) => RWOp::Store {
                    new_value,
                    result: StoreResult::Ok,
                },
                (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, None) => RWOp::Store {
                    new_value,
                    result: StoreResult::Undefined,
                },
                (HWRWOp::Store { new_value, result: HWStoreResult::Pagefault }, _) => RWOp::Store {
                    new_value,
                    result: StoreResult::Undefined,
                },
                (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, Some(_)) => RWOp::Load {
                    is_exec,
                    result: LoadResult::Value(v),
                },
                (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, None) => RWOp::Load {
                    is_exec,
                    result: LoadResult::Undefined,
                },
                (HWRWOp::Load { is_exec, result: HWLoadResult::Pagefault }, _) => RWOp::Load {
                    is_exec,
                    result: LoadResult::Undefined,
                },
            };
            hlspec::step_ReadWrite(
                c.interp(),
                s1.interp(c),
                s2.interp(c),
                ULT_id,
                vaddr,
                rwop,
                hl_pte,
            )
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let hl_pte = if (pte is None || (pte matches Some((base, _))
        && s1.inflight_unmap_vaddr().contains(base))) {
        None
    } else {
        pte
    };
    let rwop = match (op, hl_pte) {
        (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, Some(_)) => RWOp::Store {
            new_value,
            result: StoreResult::Ok,
        },
        (HWRWOp::Store { new_value, result: HWStoreResult::Ok }, None) => RWOp::Store {
            new_value,
            result: StoreResult::Undefined,
        },
        (HWRWOp::Store { new_value, result: HWStoreResult::Pagefault }, _) => RWOp::Store {
            new_value,
            result: StoreResult::Undefined,
        },
        (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, Some(_)) => RWOp::Load {
            is_exec,
            result: LoadResult::Value(v),
        },
        (HWRWOp::Load { is_exec, result: HWLoadResult::Value(v) }, None) => RWOp::Load {
            is_exec,
            result: LoadResult::Undefined,
        },
        (HWRWOp::Load { is_exec, result: HWLoadResult::Pagefault }, _) => RWOp::Load {
            is_exec,
            result: LoadResult::Undefined,
        },
    };

    let vmem_idx = mem::word_index_spec(vaddr);
    //let pmem_idx = mem::word_index_spec(paddr);

    assert(hl_s2.sound == hl_s1.sound);
    assert(aligned(vaddr, 8));
    assert(hl_s2.mappings === hl_s1.mappings);
    assert(hlspec::valid_thread(hl_c, ULT_id));
    assert(hl_s1.thread_state[ULT_id] === hlspec::AbstractArguments::Empty);
    assert(hl_s2.thread_state === hl_s1.thread_state);
    match hl_pte {
        Some((base, pte)) => {
            let paddr = (pte.frame.base + (vaddr - base)) as nat;
            let pmem_idx = mem::word_index_spec(paddr);
            assume(s1.interp_pt_mem().contains_pair(base, pte));
            assume(hl_s1.mappings.contains_pair(base, pte));
            assert(between(vaddr, base, base + pte.frame.size));

            assume(false);

        },
        None => {
            if (pte is None) {
                assert(!exists|base: nat, pte: PageTableEntry|
                    {
                        &&& #[trigger] s1.interp_pt_mem().contains_pair(base, pte)
                        &&& hlspec::mem_domain_from_entry_contains(
                            c.hw.phys_mem_size,
                            vaddr,
                            base,
                            pte,
                        )
                    });
                assert(hl_s1.mappings.submap_of(s1.interp_pt_mem()));
                assert(forall|key, value|
                    !s1.interp_pt_mem().contains_pair(key, value) ==> !hl_s1.mappings.contains_pair(
                        key,
                        value,
                    ));
                assert(!exists|base: nat, pte: PageTableEntry|
                    {
                        &&& #[trigger] hl_s1.mappings.contains_pair(base, pte)
                        &&& hlspec::mem_domain_from_entry_contains(
                            c.hw.phys_mem_size,
                            vaddr,
                            base,
                            pte,
                        )
                    });
                assert(!hlspec::mem_domain_from_mappings(
                    hl_c.phys_mem_size,
                    hl_s1.mappings,
                ).contains(vmem_idx));
            } else {
                //assert(!s1.effective_mappings().dom().contains(vaddr));
                assume(!hlspec::mem_domain_from_mappings(
                    hl_c.phys_mem_size,
                    hl_s1.mappings,
                ).contains(vmem_idx));
                assume(false);
            }
        },
    }
}

proof fn step_Map_Start_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    ULT_id: nat,
    vaddr: nat,
    pte: PageTableEntry,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Map_Start(c, s1, s2, ULT_id, vaddr, pte),
    ensures
        hlspec::step_Map_start(c.interp(), s1.interp(c), s2.interp(c), ULT_id, vaddr, pte),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    assert(hlspec::step_Map_enabled(
        s1.interp(c).thread_state.values(),
        s1.interp(c).mappings,
        vaddr,
        pte,
    ));
    assert(hlspec::valid_thread(hl_c, ULT_id));
    assert(s1.interp(c).thread_state[ULT_id] === hlspec::AbstractArguments::Empty);
    let hl_map_sound = hlspec::step_Map_sound(
        s1.interp(c).mappings,
        s1.interp(c).thread_state.values(),
        vaddr,
        pte,
    );
    lemma_map_soundness_equality(c, s1, vaddr, pte);
    if (hl_map_sound) {
        assert(hl_s1.sound == hl_s2.sound);
        //assert (hl_s2.thread_state === hl_s1.thread_state.insert(ULT_id, ));
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Map { vaddr, pte },
        ));
        lemma_map_insert_values_equality(
            hl_s1.thread_state,
            ULT_id,
            hlspec::AbstractArguments::Map { vaddr, pte },
        );
        assert(hl_s2.thread_state.values().insert(hlspec::AbstractArguments::Empty)
            =~= hl_s1.thread_state.values().insert(hlspec::AbstractArguments::Map { vaddr, pte }));
        assert(s1.interp_pt_mem() == s2.interp_pt_mem());
        lemma_inflight_vaddr_equals_hl_unmap(c, s1);
        lemma_inflight_vaddr_equals_hl_unmap(c, s2);
        assert forall|base|
            s1.inflight_unmap_vaddr().contains(base) implies s2.inflight_unmap_vaddr().contains(
            base,
        ) by {
            let threadstate = choose|thread_state|
                {
                    &&& s1.interp_thread_state(c).values().contains(thread_state)
                    &&& s1.interp_pt_mem().dom().contains(base)
                    &&& thread_state matches hlspec::AbstractArguments::Unmap { vaddr, .. }
                    &&& vaddr === base
                };
            assert(s2.interp_thread_state(c).values().contains(threadstate));
        }
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
        assert(hl_s2.mappings === hl_s1.mappings);
        assert(hl_s2.mem === hl_s1.mem);
        assert(hlspec::state_unchanged_besides_thread_state(
            hl_s1,
            hl_s2,
            ULT_id,
            hlspec::AbstractArguments::Map { vaddr, pte },
        ));
    } else {
        assert(!s2.sound);
        assert(hlspec::unsound_state(hl_s1, hl_s2));
    };
}

//TODO review ensures as its not enough...
proof fn step_Map_End_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    core: hardware::Core,
    result: Result<(), ()>,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Map_End(c, s1, s2, core, result),
    ensures
        ({
            &&& s1.core_states[core] matches os::CoreState::MapExecuting { ULT_id, .. }
            &&& hlspec::step_Map_end(c.interp(), s1.interp(c), s2.interp(c), ULT_id, result)
        }),
{
    assume(false);
}

proof fn step_Unmap_Start_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    ULT_id: nat,
    vaddr: nat,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Unmap_Start(c, s1, s2, ULT_id, vaddr),
    ensures
        hlspec::step_Unmap_start(c.interp(), s1.interp(c), s2.interp(c), ULT_id, vaddr),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    let pte = if (hl_s1.mappings.dom().contains(vaddr)) {
        Some(hl_s1.mappings.index(vaddr))
    } else {
        Option::None
    };
    assert(hlspec::step_Unmap_enabled(vaddr));
    assert(hlspec::valid_thread(hl_c, ULT_id));
    assert(hl_s1.thread_state[ULT_id] === hlspec::AbstractArguments::Empty);
    let hl_unmap_sound = pte is None || hlspec::step_Unmap_sound(
        hl_s1.thread_state.values(),
        vaddr,
        pte.unwrap(),
    );
    if (pte is None) {
    } else {
        lemma_unmap_soundness_equality(c, s1, vaddr, pte.unwrap());
    }
    if (hl_unmap_sound) {
        assert(hl_s1.sound == hl_s2.sound);
        assume(hl_s2.thread_state === hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Unmap { vaddr, pte },
        ));
        if (pte is None) {
            assume(false);
        } else {
            assume(false);
        }
    } else {
    }
}

proof fn step_Unmap_Op_End_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    core: hardware::Core,
    result: Result<(), ()>,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Unmap_Op_End(c, s1, s2, core, result),
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c)),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    assert(hl_s1.thread_state.dom() === hl_s2.thread_state.dom());
    assert forall|key| #[trigger]
        hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state[key]
        == hl_s2.thread_state[key] by {
        assert(c.valid_ULT(key));
        assert(hl_s2.thread_state.dom().contains(key));
        let core_of_key = c.ULT2core[key];
        assert(hardware::valid_core(c.hw, core));
        assert(s1.core_states[core].holds_lock());
        assert(hardware::valid_core(c.hw, core_of_key));
        if (s1.core_states[core_of_key].holds_lock()) {
            assert(core_of_key === core);
        } else {
            assert(!(core_of_key === core));
            assert(!s1.core_states[core_of_key].holds_lock());
            assert(s1.core_states.index(core_of_key) == s2.core_states.index(core_of_key));
            assert(s1.core_states[c.ULT2core[key]] === s2.core_states[c.ULT2core[key]]);
            assume(false);
        }
    }
    assume(hl_s1.thread_state =~= hl_s2.thread_state);
    assume(s1.effective_mappings() == s2.effective_mappings())
}

proof fn step_Unmap_End_refines(
    c: os::OSConstants,
    s1: os::OSVariables,
    s2: os::OSVariables,
    core: hardware::Core,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Unmap_End(c, s1, s2, core),
    ensures
        ({
            &&& s1.core_states[core] matches os::CoreState::UnmapOpDone { result, ULT_id, .. }
            &&& hlspec::step_Unmap_end(c.interp(), s1.interp(c), s2.interp(c), ULT_id, result)
        } || {
            &&& s1.core_states[core] matches os::CoreState::UnmapShootdownWaiting {
                ULT_id,
                result,
                ..
            }
            &&& hlspec::step_Unmap_end(c.interp(), s1.interp(c), s2.interp(c), ULT_id, result)
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    match s1.core_states[core] {
        os::CoreState::UnmapShootdownWaiting { ULT_id, result, vaddr, pte, .. }
        | os::CoreState::UnmapOpDone { result, ULT_id, vaddr, pte, .. } => {
            assert(hlspec::valid_thread(hl_c, ULT_id));
            assert(hl_s2.sound == hl_s1.sound);
            assert(hl_s2.thread_state === hl_s1.thread_state.insert(
                ULT_id,
                hlspec::AbstractArguments::Empty,
            ));
            assert(!s1.interp_pt_mem().dom().contains(vaddr));
            assert(!s2.interp_pt_mem().dom().contains(vaddr));
            lemma_inflight_vaddr_equals_hl_unmap(c, s2);
            lemma_inflight_vaddr_equals_hl_unmap(c, s1);
            assert forall|key|
                s2.effective_mappings().dom().contains(
                    key,
                ) implies s1.effective_mappings().dom().contains(key) by {
                assert(s2.interp_pt_mem().dom().contains(key));
                assert(s1.interp_pt_mem().dom().contains(key));
                if (key == vaddr) {
                    assert(false);
                } else {
                    if (s1.inflight_unmap_vaddr().contains(key)) {
                        let threadstate = choose|thread_state|
                            {
                                &&& s1.interp_thread_state(c).values().contains(thread_state)
                                &&& s1.interp_pt_mem().dom().contains(key)
                                &&& thread_state matches hlspec::AbstractArguments::Unmap {
                                    vaddr,
                                    ..
                                }
                                &&& vaddr === key
                            };
                        let ult_id = choose|id|
                            #![auto]
                            s1.interp_thread_state(c).dom().contains(id) && s1.interp_thread_state(
                                c,
                            ).index(id) == threadstate;
                        assert(!(ult_id == ULT_id));
                        assert(s2.interp_thread_state(c).values().contains(threadstate));
                    } else {
                    }
                }
            }
            assert(s1.effective_mappings().dom() =~= s2.effective_mappings().dom());
            assert(s1.effective_mappings() =~= s2.effective_mappings());
            assert(hl_s2.mappings === hl_s1.mappings);
            assert(hl_s2.mem === hl_s1.mem);
        },
        _ => {
            assert(false);
        },
    };

}

} // verus!
