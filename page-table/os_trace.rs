use vstd::prelude::*;

use crate::definitions_t::{
    candidate_mapping_in_bounds, x86_arch_spec_upper_bound, Flags, HWRWOp, HWStoreResult,
    MemRegion, PageTableEntry,
};
use crate::spec_t::hardware as hw;
use crate::spec_t::mem;
use crate::spec_t::os::*;

use crate::hlspec_user::lemma_max_phyaddr_at_least;

verus! {

//use util::*;
proof fn program_1() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = OSConstants {
        hw: hw::HWConstants { NUMA_no: 1, core_no: 4, phys_mem_size: 4096 * 4096 },
        ULT_no: 4,
        ULT2core: Map::new(|i: nat| i < 4, |i| hw::Core { NUMA_id: 0, core_id: i }),
    };

    let global_pt: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt) =~= Map::empty());
    // Have to assume because this isn't really modeled in sufficient detail.
    assume(global_pt.alloc_available_pages() >= 3);
    let mem = Seq::new(c.hw.phys_mem_size, |i| 0);
    let core_state = hw::CoreVariables { tlb: Map::empty() };
    let numa_state = hw::NUMAVariables {
        cores: Map::new(|i: nat| i < c.hw.core_no, |i| core_state),
    };
    let s1 = OSVariables {
        hw: hw::HWVariables {
            mem: mem,
            NUMAs: Map::new(|i: nat| i < c.hw.NUMA_no, |i| numa_state),
            global_pt: global_pt,
        },
        core_states: Map::new(
            |core: hw::Core| core.NUMA_id < c.hw.NUMA_no && core.core_id < c.hw.core_no,
            |c| CoreState::Idle,
        ),
        TLB_Shootdown: ShootdownVector { vaddr: 0, open_requests: set![] },
        sound: true,
    };

    let pte1 = PageTableEntry {
        frame: MemRegion { base: 4096, size: 4096 },
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(s1.hw.global_pt, 4096 * 3, pte1));
    assert(step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), 4096 * 3, pte1));

    let core0 = hw::Core { NUMA_id: 0, core_id: 0 };
    let core1 = hw::Core { NUMA_id: 0, core_id: 1 };
    let core2 = hw::Core { NUMA_id: 0, core_id: 2 };
    let core3 = hw::Core { NUMA_id: 0, core_id: 3 };
    let s2 = OSVariables {
        core_states: s1.core_states.insert(
            core1,
            CoreState::MapWaiting { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s1
    };

    assert(next_step(c, s1, s2, OSStep::MapStart { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 }));
    assert(next(c, s1, s2));

    //let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let s3 = OSVariables {
        core_states: s2.core_states.insert(
            core1,
            CoreState::MapExecuting { ULT_id: 1, vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s2
    };
    assert(next_step(c, s2, s3, OSStep::MapOpStart { core: core1 }));

    assert(!crate::definitions_t::candidate_mapping_overlaps_existing_vmem(
        s3.pt_variables(core1).interp(),
        4096 * 3,
        pte1,
    ));
    let global_pt2: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt2) == hw::interp_pt_mem(global_pt).insert(4096 * 3, pte1));
    let s4 = OSVariables {
        core_states: s3.core_states.insert(core1, CoreState::Idle),
        hw: hw::HWVariables { global_pt: global_pt2, ..s3.hw },
        ..s3
    };

    assert(next_step(c, s3, s4, OSStep::MapEnd { core: core1, result: Ok(()) }));

    let s5 = OSVariables {
        hw: hw::HWVariables {
            NUMAs: s4.hw.NUMAs.insert(
                0,
                hw::NUMAVariables {
                    cores: s4.hw.NUMAs[0].cores.insert(
                        2,
                        hw::CoreVariables {
                            tlb: s4.hw.NUMAs[0].cores[2].tlb.insert(4096 * 3, pte1),
                        },
                    ),
                },
            ),
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
            step: hw::HWStep::TLBFill { vaddr: 4096 * 3, pte: pte1, core: core2 },
        },
    ));

    let s6 = OSVariables { hw: hw::HWVariables { mem: s5.hw.mem.update(512, 42), ..s5.hw }, ..s5 };

    assert(hw::step_ReadWrite(
        c.hw,
        s5.hw,
        s6.hw,
        4096 * 3,
        4096,
        HWRWOp::Store { new_value: 42, result: HWStoreResult::Ok },
        Some((4096 * 3, pte1)),
        core2,
    ));
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
        },
    ));

    let s7 = OSVariables {
        core_states: s6.core_states.insert(
            core1,
            CoreState::UnmapWaiting { ULT_id: 1, vaddr: 4096 * 3 },
        ),
        ..s6
    };

    assert(next_step(c, s6, s7, OSStep::UnmapStart { ULT_id: 1, vaddr: 4096 * 3 }));

    let s8 = OSVariables {
        core_states: s7.core_states.insert(
            core1,
            CoreState::UnmapOpExecuting { ULT_id: 1, vaddr: 4096 * 3, result: None },
        ),
        ..s7
    };

    assert(next_step(c, s7, s8, OSStep::UnmapOpStart { core: core1 }));

    let global_pt3: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt3) == hw::interp_pt_mem(global_pt2).remove(4096 * 3));
    let s9a = OSVariables {
        core_states: s8.core_states.insert(
            core1,
            CoreState::UnmapOpExecuting { ULT_id: 1, vaddr: 4096 * 3, result: Some(Ok(pte1)) },
        ),
        hw: hw::HWVariables { global_pt: global_pt3, ..s8.hw },
        ..s8
    };

    assert(next_step(c, s8, s9a, OSStep::UnmapOpChange { core: core1, result: Ok(pte1) }));

    let s9b = OSVariables {
        core_states: s9a.core_states.insert(
            core1,
            CoreState::UnmapOpDone { ULT_id: 1, vaddr: 4096 * 3, result: Ok(pte1) },
        ),
        ..s9a
    };

    assert(next_step(c, s9a, s9b, OSStep::UnmapOpEnd { core: core1 }));

    let s10 = OSVariables {
        core_states: s9b.core_states.insert(
            core1,
            CoreState::UnmapShootdownWaiting {
                ULT_id: 1,
                vaddr: 4096 * 3,
                result: Ok(pte1),
            },
        ),
        TLB_Shootdown: ShootdownVector {
            vaddr: 4096 * 3,
            open_requests:
                set![
                core0,
                core1,
                core2,
                core3,
            ],
        },
        ..s9b
    };

    assert(Set::new(|core: hw::Core| hw::valid_core(c.hw, core))
        =~= s10.TLB_Shootdown.open_requests);
    assert(next_step(c, s9b, s10, OSStep::UnmapInitiateShootdown { core: core1 }));

    let s11 = OSVariables {
        TLB_Shootdown: ShootdownVector {
            vaddr: 4096 * 3,
            open_requests:
                set![
                core0,
                core2,
                core3,
            ],
        },
        ..s10
    };

    assert(s11.TLB_Shootdown.open_requests =~= s10.TLB_Shootdown.open_requests.remove(core1));
    assert(next_step(c, s10, s11, OSStep::AckShootdownIPI { core: core1 }));

    let s12 = OSVariables {
        TLB_Shootdown: ShootdownVector {
            vaddr: 4096 * 3,
            open_requests: set![
                core2,
                core3,
            ],
        },
        ..s11
    };

    assert(s12.TLB_Shootdown.open_requests =~= s11.TLB_Shootdown.open_requests.remove(core0));
    assert(next_step(c, s11, s12, OSStep::AckShootdownIPI { core: core0 }));

    let s13 = OSVariables {
        TLB_Shootdown: ShootdownVector {
            vaddr: 4096 * 3,
            open_requests: set![
                core2,
            ],
        },
        ..s12
    };

    assert(s13.TLB_Shootdown.open_requests =~= s12.TLB_Shootdown.open_requests.remove(core3));
    assert(next_step(c, s12, s13, OSStep::AckShootdownIPI { core: core3 }));

    let s14 = OSVariables {
        hw: hw::HWVariables {
            NUMAs: s13.hw.NUMAs.insert(
                0,
                hw::NUMAVariables {
                    cores: s13.hw.NUMAs[0].cores.insert(
                        2,
                        hw::CoreVariables { tlb: s13.hw.NUMAs[0].cores[2].tlb.remove(4096 * 3) },
                    ),
                },
            ),
            ..s13.hw
        },
        ..s13
    };

    assert(s14.hw.NUMAs.remove(0) =~= s13.hw.NUMAs.remove(0));
    assert(s14.hw.NUMAs[0].cores.remove(2) =~= s13.hw.NUMAs[0].cores.remove(2));
    assert(next_step(
        c,
        s13,
        s14,
        OSStep::HW { ULT_id: 2, step: hw::HWStep::TLBEvict { core: core2, vaddr: 4096 * 3 } },
    ));

    let s15 = OSVariables {
        TLB_Shootdown: ShootdownVector { vaddr: 4096 * 3, open_requests: set![] },
        ..s14
    };

    assert(s15.TLB_Shootdown.open_requests =~= s14.TLB_Shootdown.open_requests.remove(core2));
    assert(next_step(c, s14, s15, OSStep::AckShootdownIPI { core: core2 }));

    let s16 = OSVariables { core_states: s15.core_states.insert(core1, CoreState::Idle), ..s15 };

    assert(next_step(c, s15, s16, OSStep::UnmapEnd { core: core1 }));
}

} // verus!
