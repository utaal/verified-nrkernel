use vstd::prelude::*;

use crate::definitions_t::{
    candidate_mapping_in_bounds, x86_arch_spec_upper_bound, Flags, HWRWOp, HWStoreResult,
    MemRegion, PTE, Core,
};
use crate::spec_t::hardware as hw;
use crate::spec_t::mem;
use crate::spec_t::mmu::DummyAtomicMMU;
use crate::spec_t::os::*;

use crate::hlspec_user::lemma_max_phyaddr_at_least;

verus! {

//use util::*;
proof fn program_1() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants {
        hw: hw::Constants { node_count: 1, core_count: 4, phys_mem_size: 4096 * 4096 },
        ult_no: 4,
        ult2core: Map::new(|i: nat| i < 4, |i| Core { node_id: 0, core_id: i }),
    };

    let global_pt: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt) =~= Map::empty());
    // Have to assume because this isn't really modeled in sufficient detail.
    assume(global_pt.alloc_available_pages() >= 3);
    let mem = Seq::new(c.hw.phys_mem_size, |i| 0);
    let core_state = hw::PerCoreState { tlb: Map::empty() };
    let numa_state = hw::PerNodeState {
        cores: Map::new(|i: nat| i < c.hw.core_count, |i| core_state),
    };
    let s1 = State {
        hw: hw::State {
            mem: mem,
            nodes: Map::new(|i: nat| i < c.hw.node_count, |i| numa_state),
            global_pt: global_pt,
            mmu: DummyAtomicMMU {}
        },
        core_states: Map::new(
            |core: Core| core.node_id < c.hw.node_count && core.core_id < c.hw.core_count,
            |c| CoreState::Idle,
        ),
        TLB_Shootdown: ShootdownVector { vaddr: 0, open_requests: set![] },
        sound: true,
    };

    let pte1 = PTE {
        frame: MemRegion { base: 4096, size: 4096 },
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(s1.hw.global_pt, 4096 * 3, pte1));
    assert(step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), 4096 * 3, pte1));

    let core0 = Core { node_id: 0, core_id: 0 };
    let core1 = Core { node_id: 0, core_id: 1 };
    let core2 = Core { node_id: 0, core_id: 2 };
    let core3 = Core { node_id: 0, core_id: 3 };
    let s2 = State {
        core_states: s1.core_states.insert(
            core1,
            CoreState::MapWaiting { ult_id: 1, vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s1
    };

    assert(next_step(c, s1, s2, Step::MapStart { ult_id: 1, vaddr: 4096 * 3, pte: pte1 }));
    assert(next(c, s1, s2));

    //let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let s3 = State {
        core_states: s2.core_states.insert(
            core1,
            CoreState::MapExecuting { ult_id: 1, vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s2
    };
    assert(next_step(c, s2, s3, Step::MapOpStart { core: core1 }));

    assert(!crate::definitions_t::candidate_mapping_overlaps_existing_vmem(
        s3.pt_variables(core1).interp(),
        4096 * 3,
        pte1,
    ));
    let global_pt2: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt2) == hw::interp_pt_mem(global_pt).insert(4096 * 3, pte1));
    let s4 = State {
        core_states: s3.core_states.insert(core1, CoreState::Idle),
        hw: hw::State { global_pt: global_pt2, ..s3.hw },
        ..s3
    };

    assert(next_step(c, s3, s4, Step::MapEnd { core: core1, result: Ok(()) }));

    let s5 = State {
        hw: hw::State {
            nodes: s4.hw.nodes.insert(
                0,
                hw::PerNodeState {
                    cores: s4.hw.nodes[0].cores.insert(
                        2,
                        hw::PerCoreState {
                            tlb: s4.hw.nodes[0].cores[2].tlb.insert(4096 * 3, pte1),
                        },
                    ),
                },
            ),
            ..s4.hw
        },
        ..s4
    };

    assert(s5.hw.nodes.remove(0) =~= s4.hw.nodes.remove(0));
    assert(s5.hw.nodes[0].cores.remove(2) =~= s4.hw.nodes[0].cores.remove(2));
    assert(next_step(
        c,
        s4,
        s5,
        Step::HW {
            ult_id: 2,
            step: hw::Step::TLBFill { vaddr: 4096 * 3, pte: pte1, core: core2 },
        },
    ));

    let s6 = State { hw: hw::State { mem: s5.hw.mem.update(512, 42), ..s5.hw }, ..s5 };

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
        Step::HW {
            ult_id: 2,
            step: hw::Step::ReadWrite {
                vaddr: 4096 * 3,
                paddr: 4096,
                op: HWRWOp::Store { new_value: 42, result: HWStoreResult::Ok },
                pte: Some((4096 * 3, pte1)),
                core: core2,
            },
        },
    ));

    let s7 = State {
        core_states: s6.core_states.insert(
            core1,
            CoreState::UnmapWaiting { ult_id: 1, vaddr: 4096 * 3 },
        ),
        ..s6
    };

    assert(next_step(c, s6, s7, Step::UnmapStart { ult_id: 1, vaddr: 4096 * 3 }));

    let s8 = State {
        core_states: s7.core_states.insert(
            core1,
            CoreState::UnmapOpExecuting { ult_id: 1, vaddr: 4096 * 3, result: None },
        ),
        ..s7
    };

    assert(next_step(c, s7, s8, Step::UnmapOpStart { core: core1 }));

    let global_pt3: mem::PageTableMemory;
    assume(hw::interp_pt_mem(global_pt3) == hw::interp_pt_mem(global_pt2).remove(4096 * 3));
    let s9a = State {
        core_states: s8.core_states.insert(
            core1,
            CoreState::UnmapOpExecuting { ult_id: 1, vaddr: 4096 * 3, result: Some(Ok(pte1)) },
        ),
        hw: hw::State { global_pt: global_pt3, ..s8.hw },
        ..s8
    };

    assert(next_step(c, s8, s9a, Step::UnmapOpChange { core: core1, result: Ok(pte1) }));

    let s9b = State {
        core_states: s9a.core_states.insert(
            core1,
            CoreState::UnmapOpDone { ult_id: 1, vaddr: 4096 * 3, result: Ok(pte1) },
        ),
        ..s9a
    };

    assert(next_step(c, s9a, s9b, Step::UnmapOpEnd { core: core1 }));

    let s10 = State {
        core_states: s9b.core_states.insert(
            core1,
            CoreState::UnmapShootdownWaiting {
                ult_id: 1,
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

    assert(Set::new(|core: Core| hw::valid_core(c.hw, core))
        =~= s10.TLB_Shootdown.open_requests);
    assert(next_step(c, s9b, s10, Step::UnmapInitiateShootdown { core: core1 }));

    let s11 = State {
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
    assert(next_step(c, s10, s11, Step::AckShootdownIPI { core: core1 }));

    let s12 = State {
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
    assert(next_step(c, s11, s12, Step::AckShootdownIPI { core: core0 }));

    let s13 = State {
        TLB_Shootdown: ShootdownVector {
            vaddr: 4096 * 3,
            open_requests: set![
                core2,
            ],
        },
        ..s12
    };

    assert(s13.TLB_Shootdown.open_requests =~= s12.TLB_Shootdown.open_requests.remove(core3));
    assert(next_step(c, s12, s13, Step::AckShootdownIPI { core: core3 }));

    let s14 = State {
        hw: hw::State {
            nodes: s13.hw.nodes.insert(
                0,
                hw::PerNodeState {
                    cores: s13.hw.nodes[0].cores.insert(
                        2,
                        hw::PerCoreState { tlb: s13.hw.nodes[0].cores[2].tlb.remove(4096 * 3) },
                    ),
                },
            ),
            ..s13.hw
        },
        ..s13
    };

    assert(s14.hw.nodes.remove(0) =~= s13.hw.nodes.remove(0));
    assert(s14.hw.nodes[0].cores.remove(2) =~= s13.hw.nodes[0].cores.remove(2));
    assert(next_step(
        c,
        s13,
        s14,
        Step::HW { ult_id: 2, step: hw::Step::TLBEvict { core: core2, vaddr: 4096 * 3 } },
    ));

    let s15 = State {
        TLB_Shootdown: ShootdownVector { vaddr: 4096 * 3, open_requests: set![] },
        ..s14
    };

    assert(s15.TLB_Shootdown.open_requests =~= s14.TLB_Shootdown.open_requests.remove(core2));
    assert(next_step(c, s14, s15, Step::AckShootdownIPI { core: core2 }));

    let s16 = State { core_states: s15.core_states.insert(core1, CoreState::Idle), ..s15 };

    assert(next_step(c, s15, s16, Step::UnmapEnd { core: core1 }));
}

} // verus!
