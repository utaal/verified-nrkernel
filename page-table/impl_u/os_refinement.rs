use vstd::prelude::*;

use crate::spec_t::{ hardware, hlspec, os };
use crate::impl_u::spec_pt;
use crate::spec_t::hardware::Core;
use crate::definitions_t::{ between, MemRegion, overlap, PageTableEntry, RWOp,
aligned, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem,
L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, WORD_SIZE };
use crate::spec_t::mem::{ word_index_spec };
use crate::extra;

verus! {

proof fn os_init_refines_hl_init(c: os::OSConstants, s: os::OSVariables)
    requires
        os::init(c, s)
    ensures
        hlspec::init(c.interp(), s.interp(c))
{
    let abs_c = c.interp();
    let abs_s = s.interp(c);
    //lemma_effective_mappings_equal_interp_pt_mem(s);
    assert forall|id: nat| id < abs_c.thread_no implies (abs_s.thread_state[id] === hlspec::AbstractArguments::Empty) by {
        assert (c.ULT2core.contains_key(id));
        let core = c.ULT2core[id];
        assert (hardware::valid_core(c.hw ,core));
        assert (s.core_states[core] === os::CoreState::Idle); //nn
    };
    assert( abs_s.mem === Map::empty());
    assert( abs_s.mappings === Map::empty());
}

proof fn os_next_refines_hl_next(c: os::OSConstants, s1: os::OSVariables, s2: os::OSVariables)
    requires
        os::next(c, s1, s2,)
    ensures
        hlspec::next(c.interp(), s1.interp(c), s2.interp(c))
{   let step = choose |step : os::OSStep| os::next_step(c, s1, s2, step);
    next_step_refines_hl_next_step(c, s1, s2, step);
}

// probably need invariant that TLB entries are consistent 
// to prove lemma that if we choose one TLB entry its the same as choosing another
// also needs invariant that tlbs are submap of pt to pt + inflight memory

proof fn HL_Stutter_step(c: hlspec::AbstractConstants, s1 : hlspec::AbstractVariables, s2 : hlspec::AbstractVariables )
    requires
        s1.mem          === s2.mem,
        s1.thread_state === s2.thread_state,
        s1.mappings     === s2.mappings,
        s1.sound        === s2.sound,
    ensures 
        hlspec::step_Stutter(c, s1, s2)
{
    assume(false);
}


proof fn next_step_refines_hl_next_step(c: os::OSConstants, s1: os::OSVariables, s2: os::OSVariables, step: os::OSStep)
    requires
        os::next_step(c, s1, s2, step)
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(c, s1))
{
    match step {
        os::OSStep::HW { ULT_id, step } => match step {
            hardware::HWStep::ReadWrite {
                vaddr,
                paddr,
                op,
                pte,
                core,
            } => {assume(false);},
            _ => {},
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => { assume(false); },
        os::OSStep::MapOpStart { ULT_id } => {
            let core = c.ULT2core.index(ULT_id);
            assert(s1.interp(c).thread_state.dom() =~= s2.interp(c).thread_state.dom());
            let vaddr = s1.core_states[core]->MapWaiting_vaddr;
            let pte = s1.core_states[core]->MapWaiting_pte;
            assert(s2.core_states == s1.core_states.insert(core, os::CoreState::MapExecuting { ULT_id, vaddr, pte }));
            assert forall|k| #![auto] s1.interp(c).thread_state.contains_key(k)
                implies s1.interp(c).thread_state[k] == s2.interp(c).thread_state[k] by
            {
                if k == ULT_id {
                } else {
                    if c.ULT2core[k] == core {
                        assert(s1.interp(c).thread_state[k] == s2.interp(c).thread_state[k]);
                    } else {
                        assume(s1.core_states.dom().contains(c.ULT2core[k]));
                        assert(s1.interp(c).thread_state[k] == s2.interp(c).thread_state[k]);
                    }
                }
            };
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);

            assume(s2.inflight_unmap_vaddr() == s1.inflight_unmap_vaddr());
            assert(s1.interp(c).mappings =~= s2.interp(c).mappings);
            assert(s1.interp(c).mem === s2.interp(c).mem);
            //HL_Stutter_step(c.interp(), s1.interp(c), s2.interp(c));
        },
        os::OSStep::MapEnd { ULT_id, result } => {assume(false);},
        //Unmap steps
        os::OSStep::UnmapStart { ULT_id, vaddr } => {assume(false); },
        os::OSStep::UnmapOpStart { ULT_id } => {assume(false);},
        os::OSStep::UnmapOpEnd { ULT_id, result } => {assume(false);},
        os::OSStep::UnmapInitiateShootdown { ULT_id } => {assume(s1.interp(c).thread_state === s2.interp(c).thread_state);
                                                          assume(s1.interp(c).mem === s2.interp(c).mem);
                                                          assume(s1.interp(c).mappings === s2.interp(c).mappings);
                                                          //HL_Stutter_step(c.interp(), s1.interp(c), s2.interp(c));
},
        os::OSStep::UnmapEnd { ULT_id, result } => {assume(false);
        },
        _ => {},
    }
}


}
