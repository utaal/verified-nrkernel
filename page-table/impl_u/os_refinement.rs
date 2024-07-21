use vstd::prelude::*;

//use crate::impl_u::spec_pt;
//use crate::spec_t::hardware::Core;
use crate::definitions_t::{
    above_zero, candidate_mapping_overlaps_existing_pmem, overlap, MemRegion, PageTableEntry,
};
use crate::spec_t::{hardware, hlspec, os};

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

proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    admit();
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemma
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
                assume(false);
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
            assume(false);
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
            assume(s1.interp_pt_mem() === s2.interp_pt_mem());
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::OSStep::UnmapInitiateShootdown { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        //TODO
        os::OSStep::UnmapEnd { core } => {
            step_Unmap_End_refines(c, s1, s2, core);
            assume(false);  //TODO adjust interp function
        },
        _ => {},
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
    //lemma_map_soundness_equality(c, s1, vaddr);
    assume(false);
}

/*

    &&& s2.thread_state === s1.thread_state.insert(
        thread_id,
        AbstractArguments::Unmap { vaddr, pte },
    )
    &&& if (pte is None) {
        &&& s2.mappings === s1.mappings
        &&& s2.mem === s1.mem
    } else {
        &&& s2.mappings === s1.mappings.remove(vaddr)
        &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s2.mappings)
        &&& (forall|idx: nat|
            #![auto]
            s2.mem.dom().contains(idx) ==> s2.mem[idx] === s1.mem[idx])
    }
    &&& s2.mem.dom() === mem_domain_from_mappings(c.phys_mem_size, s1.mappings.remove(vaddr))
    &&& s2.sound == s1.sound

    */

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
    let hl_unmap_unsound = pte is None || hlspec::step_Unmap_sound(
        hl_s1.thread_state.values(),
        vaddr,
        pte.unwrap(),
    );
    if (pte is None) {
    } else {
        lemma_unmap_soundness_equality(c, s1, vaddr, pte.unwrap());
    }
    if (hl_unmap_unsound) {
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
    //lemma_map_soundness_equality(c, s1, vaddr);

}

/*

        AbstractArguments::Unmap { vaddr, pte } => {
            &&& if pte is Some {
                result is Ok
            } else {
                result is Err
            }
        },
        _ => { false },
    }
}

*/

/*
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
    &&& spec_pt::step_Stutter(
        s1.pt_variables(),
        s2.pt_variables(),
    )
    //new state

    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s2.TLB_Shootdown == s1.TLB_Shootdown
    &&& s1.sound == s2.sound
}
*/

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
            assume(s1.effective_mappings() =~= s2.effective_mappings());
            assert(hl_s2.mappings === hl_s1.mappings);
            assert(hl_s2.mem === hl_s1.mem);
            if (pte is None) {
                assume(result is Ok);
            } else {
                assume(result is Err);
            }
            assume(false);

        },
        _ => {
            assert(false);
        },
    };

    //lemma_map_soundness_equality(c, s1, vaddr);

}

} // verus!
