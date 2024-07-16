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

proof fn init_refines_hl_init(c: os::OSConstants, s: os::OSVariables)
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
    //created by 
    assert forall |core: Core| #[trigger] hardware::valid_core(c.hw, core) implies s.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb === Map::empty() by {
        assert (core.NUMA_id < c.hw.NUMA_no);
        assert (hardware::valid_NUMA_id(c.hw, core.NUMA_id));
        assert (s.hw.NUMAs.contains_key(core.NUMA_id));
        assert (hardware::NUMA_init(c.hw, s.hw.NUMAs[core.NUMA_id]));
        assert (core.core_id < c.hw.core_no);
        assert (hardware::valid_core_id(c.hw, core.core_id));
        assert (s.hw.NUMAs[core.NUMA_id].cores.contains_key(core.core_id));
        assert (s.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb === Map::empty());
    }
   
    assume( abs_s.mem === Map::empty());
    //created by 
    assume( abs_s.mappings === Map::empty());
    
    //assert(s.interp().mem =~= Map::empty());
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
            hardware::HWStep::PTMemOp => {},
            hardware::HWStep::TLBFill { vaddr, pte, core } => {assume(false);},
            hardware::HWStep::TLBEvict { vaddr, core } => {assume(false);},
            hardware::HWStep::Stutter => {},
        },
        //Map steps
        os::OSStep::MapStart { ULT_id, vaddr, pte } => { assume(false); },
        os::OSStep::MapOpStart { ULT_id } => {assume(false);},
        os::OSStep::MapEnd { ULT_id, result } => {assume(false);},
        //Unmap steps
        os::OSStep::UnmapStart { ULT_id, vaddr } => {assume(false); },
        os::OSStep::UnmapOpStart { ULT_id } => {assume(false);},
        os::OSStep::UnmapOpEnd { ULT_id, result } => {assume(false);},
        os::OSStep::UnmapInitiateShootdown { ULT_id } => {assume(false);},
        os::OSStep::AckShootdownIPI { core } => {assume(false);},
        os::OSStep::UnmapEnd { ULT_id, result } => {assume(false);
        },
        _ => {},
    }
}


}
