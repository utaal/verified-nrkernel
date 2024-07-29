use vstd::prelude::*;

use crate::definitions_t::{
    candidate_mapping_in_bounds, x86_arch_spec_upper_bound,
    Flags, MemRegion, PageTableEntry, HWRWOp, HWStoreResult
};
use crate::spec_t::os::*;
use crate::spec_t::hardware as hw;
use crate::spec_t::mem;

use crate::hlspec_user::lemma_max_phyaddr_at_least;

verus! {

//use util::*;

proof fn program_1() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = OSConstants {
        hw: hw::HWConstants {
            NUMA_no: 1,
            core_no: 4,
            phys_mem_size: 4096 * 4096,
        },
        ULT_no: 4,
        ULT2core: Map::new(|i:nat| i < 4, |i| hw::Core { NUMA_id: 0, core_id: i }),
    };

    let global_pt: mem::PageTableMemory;
    let mem = Seq::new(c.hw.phys_mem_size, |i| 0);
    // Init
    assume(global_pt.inv());
    assume(global_pt.regions() === set![global_pt.cr3_spec()@]);
    assume(global_pt.region_view(global_pt.cr3_spec()@).len() == 512);
    assume((forall|i: nat| i < 512 ==> global_pt.region_view(global_pt.cr3_spec()@)[i as int] == 0));
    // Have to assume because this isn't really modeled in sufficient detail.
    assume(global_pt.alloc_available_pages() == 50);
    let core_state = hw::CoreVariables { tlb: Map::empty() };
    let numa_state = hw::NUMAVariables { cores: Map::new(|i:nat| i < c.hw.core_no, |i| core_state) };
    let s1 = OSVariables {
        hw: hw::HWVariables {
            mem: mem,
            NUMAs: Map::new(|i:nat| i < c.hw.NUMA_no, |i| numa_state),
            global_pt: global_pt,
        },
        core_states: Map::new(|core:hw::Core| core.NUMA_id < c.hw.NUMA_no && core.core_id < c.hw.core_no, |c| CoreState::Idle),
        TLB_Shootdown: ShootdownVector {
            vaddr: 0,
            open_requests: set![],
        },
        sound: true,
    };

    assert(s1.wf(c));
    assume(hw::interp_pt_mem(s1.hw.global_pt) =~= Map::empty());
    assert(init(c, s1));

    let pte1 = PageTableEntry {
        frame: MemRegion { base: 4096, size: 4096 },
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(s1.hw.global_pt, 4096 * 3, pte1));
    assert(step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), 4096 * 3, pte1));

    let core1 = hw::Core { NUMA_id: 0, core_id: 1 };
    let s2 = OSVariables {
        core_states: s1.core_states.insert(core1, CoreState::MapWaiting { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 }),
        ..s1
    };

    assert(next_step(
        c,
        s1,
        s2,
        OSStep::MapStart { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 },
    ));
    assert(next(c, s1, s2));

    //let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let s3 = OSVariables {
        core_states: s2.core_states.insert(core1, CoreState::MapExecuting { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 }),
        ..s2
    };
    assert(next_step(c, s2, s3, OSStep::MapOpStart { core: core1 }));

    assert(!crate::definitions_t::candidate_mapping_overlaps_existing_vmem(s3.pt_variables().interp(), 4096 * 3, pte1));
    let global_pt2: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt2) == hw::interp_pt_mem(global_pt).insert(4096 * 3, pte1));
    let s4 = OSVariables {
        core_states: s3.core_states.insert(core1, CoreState::Idle),
        hw: hw::HWVariables {
            global_pt: global_pt2,
            ..s3.hw
        },
        ..s3
    };

    assert(next_step(c, s3, s4, OSStep::MapEnd { core: core1, result: Ok(()) }));

    let core2 = hw::Core { NUMA_id: 0, core_id: 2 };
    let s5 = OSVariables {
        hw: hw::HWVariables {
            NUMAs:
                s4.hw.NUMAs.insert(0,
                    hw::NUMAVariables {
                        cores:
                            s4.hw.NUMAs[0].cores.insert(2,
                                hw::CoreVariables {
                                    tlb: s4.hw.NUMAs[0].cores[2].tlb.insert(4096 * 3, pte1)
                                })
                    }),
            ..s4.hw
        },
        ..s4
    };

    assert(s5.hw.NUMAs.remove(0) =~= s4.hw.NUMAs.remove(0));
    assert(s5.hw.NUMAs[0].cores.remove(2) =~= s4.hw.NUMAs[0].cores.remove(2));
    assert(next_step(
        c,
        s4,
        s5,
        OSStep::HW {
            ULT_id: 2,
            step: hw::HWStep::TLBFill {
                vaddr: 4096 * 3,
                pte: pte1,
                core: core2,
            },
        }));

    let s6 = OSVariables {
        hw: hw::HWVariables {
            mem: s5.hw.mem.update(512, 42),
            ..s5.hw
        },
        ..s5
    };

    assert(hw::step_ReadWrite(c.hw, s5.hw, s6.hw, 4096 * 3, 4096, HWRWOp::Store { new_value: 42, result: HWStoreResult::Ok }, Some((4096 * 3, pte1)), core2));
    assert(next_step(
        c,
        s5,
        s6,
        OSStep::HW {
            ULT_id: 2,
            step: hw::HWStep::ReadWrite {
                vaddr: 4096 * 3,
                paddr: 4096,
                op: HWRWOp::Store { new_value: 42, result: HWStoreResult::Ok },
                pte: Some((4096 * 3, pte1)),
                core: core2,
            },
        }));

    //assert(next_step(
    //    c,
    //    s5,
    //    s5,
    //    OSStep::HW {
    //        ULT_id: 2,
    //        step: hw::HWStep::ReadWrite {
    //            vaddr: 4096 * 3,
    //            paddr: 4096,
    //            op: HWRWOp::Load { is_exec: false, result: HWLoadResult::Value(42) },
    //            pte: Some((4096 * 3, pte1)),
    //            core: core2,
    //        },
    //    }));




    //let mem6 = lemma_contract_mem_domain(s5.mem, 4096 * 3, 4096);
    //let s6 = AbstractVariables {
    //    thread_state: s5.thread_state.insert(
    //        2,
    //        AbstractArguments::Unmap { vaddr: 4096 * 3, pte: Some(pte1) },
    //    ),
    //    mappings: s5.mappings.remove(4096 * 3),
    //    mem: mem6,
    //    ..s5
    //};
    //// assume(false);  //TODO
    //
    //assert(s6.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s6.mappings));
    //assert(next_step(c, s5, s6, AbstractStep::UnmapStart { thread_id: 2, vaddr: 4096 * 3 }));

}

} // verus!
