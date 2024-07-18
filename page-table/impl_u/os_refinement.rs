use vstd::prelude::*;

//use crate::impl_u::spec_pt;
use crate::spec_t::hardware::Core;
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
// Lemma
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
                    &&& s.core_states[core] matches os::CoreState::UnmapWaiting { ULT_id, vaddr }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapOpExecuting {
                        ULT_id,
                        vaddr,
                    }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                    &&& vaddr == v_addr
                } || {
                    &&& s.core_states[core] matches os::CoreState::UnmapShootdownWaiting {
                        ULT_id,
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
    match step {
        os::OSStep::HW { ULT_id, step } => match step {
            hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, core } => {
                assume(false);
            },
            _ => {},
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => {
            assume(false);
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
            assume(false);
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

} // verus!
