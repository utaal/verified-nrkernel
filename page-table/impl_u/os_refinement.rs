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
proof fn lemma_infllight_vaddr_equals_hl_unmap(c: os::OSConstants, s: os::OSVariables)
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
    lemma_infllight_vaddr_equals_hl_unmap(c, s1);
    lemma_infllight_vaddr_equals_hl_unmap(c, s2);
    assert(s2.inflight_unmap_vaddr() =~= s1.inflight_unmap_vaddr());
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemma
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn interp_inflight_pte_size_above_zero(
    inflightargs: Set<hlspec::AbstractArguments>,
) -> bool {
    forall|b: hlspec::AbstractArguments|
        {
            #[trigger] inflightargs.contains(b) ==> match b {
                hlspec::AbstractArguments::Map { pte, .. } => { above_zero(pte.frame.size) },
                hlspec::AbstractArguments::Unmap { pte, .. } => {
                    pte.is_some() ==> above_zero(pte.unwrap().frame.size)
                },
                _ => { true },
            }
        }
}

proof fn lemma_interp_inflight_pte_size_above_zero(c: os::OSConstants, s: os::OSVariables)
    requires
        s.inv(c),
    ensures
        interp_inflight_pte_size_above_zero(s.interp(c).thread_state.values()),
{
    assume(false);
}

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
            s.effective_mappings(),
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
        s.effective_mappings(),
        s.core_states.values(),
        base,
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate,
    )) by {
        if (os::candidate_mapping_overlaps_inflight_vmem(
            s.effective_mappings(),
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
                        | os::CoreState::UnmapOpExecuting { vaddr, .. }
                        | os::CoreState::UnmapOpDone { vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { vaddr, .. } => {
                            &&& s.effective_mappings().dom().contains(vaddr)
                            &&& overlap(
                                MemRegion {
                                    base: vaddr,
                                    size: s.effective_mappings().index(vaddr).frame.size,
                                },
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
                    assume(s.interp(c).thread_state.values().contains(thread_state));
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
                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(p_te),
                        }
                        &&& v_address === vaddr
                        &&& s.effective_mappings()[vaddr] === p_te
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
            s.effective_mappings(),
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
        s.effective_mappings(),
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
            assume(false);
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
                | os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr }
                | os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, .. } => {
                    assert(s.effective_mappings().dom().contains(vaddr));
                    assert(ult_id == ULT_id);
                    let pte = s.effective_mappings()[vaddr];
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
            s.effective_mappings(),
            s.core_states.values(),
            candidate,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_pmem(
        s.effective_mappings(),
        s.core_states.values(),
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    )) by {
        if (os::candidate_mapping_overlaps_inflight_pmem(
            s.effective_mappings(),
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
                        | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                        | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                            &&& s.effective_mappings().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.effective_mappings().index(vaddr).frame)
                        },
                        os::CoreState::Idle => false,
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
                    assume(s.interp(c).thread_state.values().contains(thread_state));
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
                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
                    assert(c.valid_ULT(ULT_id));
                    let thread_state = s.interp_thread_state(c)[ULT_id];
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_address,
                            pte: Some(p_te),
                        }
                        &&& v_address === vaddr
                        &&& s.effective_mappings()[vaddr] === p_te
                        &&& overlap(candidate.frame, s.effective_mappings().index(vaddr).frame)
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
            s.effective_mappings(),
            s.core_states.values(),
            candidate,
        ),
{
    lemma_interp_inflight_pte_size_above_zero(c, s);
    assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    ) ==> os::candidate_mapping_overlaps_inflight_pmem(
        s.effective_mappings(),
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
                | os::CoreState::UnmapOpExecuting { ULT_id: ult_id, vaddr }
                | os::CoreState::UnmapOpDone { ULT_id: ult_id, vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { ULT_id: ult_id, vaddr, .. } => {
                    assume(s.effective_mappings().dom().contains(vaddr));
                    assert(ult_id == ULT_id);
                    let pte = s.effective_mappings()[vaddr];
                    assert(above_zero(pte.frame.size));
                    assert({
                        &&& thread_state matches hlspec::AbstractArguments::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, s.effective_mappings().index(vaddr).frame));
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
            <==> os::step_Map_sound(s.effective_mappings(), s.core_states.values(), vaddr, pte),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte);
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(c, s, pte);
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(c, s, pte);
    assert(candidate_mapping_overlaps_existing_pmem(s.interp(c).mappings, pte)
        <==> candidate_mapping_overlaps_existing_pmem(s.effective_mappings(), pte));
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

// probably need invariant that TLB entries are consistent
// to prove lemma that if we choose one TLB entry its the same as choosing another
// also needs invariant that tlbs are submap of pt to pt + inflight memory
proof fn HL_Stutter_step(
    c: hlspec::AbstractConstants,
    s1: hlspec::AbstractVariables,
    s2: hlspec::AbstractVariables,
)
    requires
        s1.mem === s2.mem,
        s1.thread_state === s2.thread_state,
        s1.mappings === s2.mappings,
        s1.sound === s2.sound,
    ensures
        hlspec::step_Stutter(c, s1, s2),
{
    assume(false);
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

            //assert(s1.interp(c).mappings =~= s2.interp(c).mappings);
            //assert(s1.interp(c).mem === s2.interp(c).mem);

        },
        os::OSStep::MapEnd { core, result } => {
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
        os::OSStep::UnmapEnd { core } => {
            assume(false);
        },
        _ => {},
    }
}

/*
c: AbstractConstants,
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    vaddr: nat,
    pte: PageTableEntry,
    */

/*  &&& step_Map_enabled(s1.thread_state.values(), s1.mappings, vaddr, pte)
    &&& valid_thread(c, thread_id)
    &&& s1.thread_state[thread_id] === AbstractArguments::Empty
    &&& if (!candidate_mapping_overlaps_inflight_vmem(s1.thread_state.values(), vaddr, pte)
        && !candidate_mapping_overlaps_existing_pmem(s1.mappings, pte)
        && !candidate_mapping_overlaps_inflight_pmem(s1.thread_state.values(), pte)) {
        &&& state_unchanged_besides_thread_state(
            s1,
            s2,
            thread_id,
            AbstractArguments::Map { vaddr, pte },
        )
    } else {
        unsound_state(s1, s2)
    }
*/

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
    let hl_map_unsound = hlspec::step_Map_sound(
        s1.interp(c).mappings,
        s1.interp(c).thread_state.values(),
        vaddr,
        pte,
    );
    lemma_map_soundness_equality(c, s1, vaddr, pte);
    if (hl_map_unsound) {
        assert(hl_s1.sound == hl_s2.sound);
        //assert (hl_s2.thread_state === hl_s1.thread_state.insert(ULT_id, ));
        lemma_infllight_vaddr_equals_hl_unmap(c, s1);
        lemma_infllight_vaddr_equals_hl_unmap(c, s2);
        assume(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
        assert(hl_s2.mappings === hl_s1.mappings);
        assert(hl_s2.mem === hl_s1.mem);
        assume(hlspec::state_unchanged_besides_thread_state(
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
    assume(false);
}

} // verus!
