use vstd::prelude::*;

use crate::definitions_t::{
    aligned, between, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap, HWLoadResult, HWRWOp, HWStoreResult,
    LoadResult, MemRegion, PTE, RWOp, StoreResult, WORD_SIZE, Core
};
use crate::spec_t::hlproof::lemma_mem_domain_from_mappings;
use crate::spec_t::os_invariant::{
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl,
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl, next_step_preserves_inv,
    lemma_map_insert_values_equality, lemma_map_insert_value,
};
use crate::spec_t::{hardware, hlspec, mem, os, mmu};
use crate::spec_t::mmu::WalkResult;
use crate::extra::result_map_ok;

verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_inflight_vaddr_equals_hl_unmap<M: mmu::MMU>(c: os::Constants, s: os::State<M>)
    requires
        s.basic_inv(c),
    ensures
        forall|v_addr|
            s.inflight_unmap_vaddr().contains(v_addr) <==> exists|thread_state|
                {
                    &&& s.interp_thread_state(c).values().contains(thread_state)
                    &&& s.interp_pt_mem().dom().contains(v_addr)
                    &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                    &&& vaddr === v_addr
                },
{
    // proof ==> direction
    assert forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr) implies exists|thread_state|
        {
            &&& s.interp_thread_state(c).values().contains(thread_state)
            &&& s.interp_pt_mem().dom().contains(v_addr)
            &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
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
            os::CoreState::UnmapWaiting { ult_id, vaddr }
            | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                assert(s.interp_thread_state(c).dom().contains(ult_id));
                let thread_state = s.interp_thread_state(c)[ult_id];
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
                &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                &&& vaddr === v_addr
            } implies s.inflight_unmap_vaddr().contains(v_addr) by {
        let thread_state = choose|thread_state|
            {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, pte }
                &&& vaddr == v_addr
            };
        let ult_id = choose|id| #[trigger]
            s.interp_thread_state(c).dom().contains(id) && s.interp_thread_state(c)[id]
                === thread_state;
        assert(s.core_states.dom().contains(c.ult2core[ult_id]));
    };

}

proof fn lemma_effective_mappings_unaffected_if_thread_state_constant<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
)
    requires
        s1.basic_inv(c),
        s2.basic_inv(c),
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
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_map_soundness_equality<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
    vaddr: nat,
    pte: PTE,
)
    requires
        s.basic_inv(c),
        pte.frame.size > 0,
    ensures
        hlspec::step_Map_sound(s.interp(c).mappings, s.interp(c).thread_state.values(), vaddr, pte)
            <==> os::step_Map_sound(s.interp_pt_mem(), s.core_states.values(), vaddr, pte),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte.frame.size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte.frame.size);
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
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
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

proof fn lemma_unmap_soundness_equality<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
    vaddr: nat,
    pte_size: nat,
)
    requires
        s.basic_inv(c),
    ensures
        hlspec::step_Unmap_sound(s.interp(c).thread_state.values(), vaddr, pte_size)
            <==> os::step_Unmap_sound(s.interp_pt_mem(), s.core_states.values(), vaddr, pte_size),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte_size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte_size);
}

proof fn lemma_os_overlap_vmem_implies_hl_or_inflight_overlap_vmem<M: mmu::MMU>(
    c: os::Constants,
    s: os::State<M>,
    vaddr: nat,
    pte: PTE,
)
    requires
        s.basic_inv(c),
    ensures
        candidate_mapping_overlaps_existing_vmem(s.interp_pt_mem(), vaddr, pte)
            ==> candidate_mapping_overlaps_existing_vmem(s.interp(c).mappings, vaddr, pte)
            || hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            vaddr,
            pte.frame.size,
        ),
{
    let pte_size = pte.frame.size;
    assert(candidate_mapping_overlaps_existing_vmem(s.interp_pt_mem(), vaddr, pte) ==> (
    candidate_mapping_overlaps_existing_vmem(s.interp(c).mappings, vaddr, pte)
        || hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        vaddr,
        pte_size,
    ))) by {
        if candidate_mapping_overlaps_existing_vmem(s.interp_pt_mem(), vaddr, pte) {
            if (!os::candidate_mapping_overlaps_inflight_vmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                vaddr,
                pte_size,
            )) {
                let base = choose|b: nat| #![auto] {
                        &&& s.interp_pt_mem().dom().contains(b)
                        &&& overlap(
                            MemRegion { base: vaddr, size: pte_size },
                            MemRegion { base: b, size: s.interp_pt_mem()[b].frame.size },
                        )
                    };
                if (!s.inflight_unmap_vaddr().contains(base)) {
                    assert(s.effective_mappings().dom().contains(base));
                } else {
                    let core = choose|core|
                        s.core_states.dom().contains(core) && match s.core_states[core] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === base
                            },
                            _ => false,
                        };
                    assert(s.core_states.values().contains(s.core_states.index(core)));
                    assert(os::candidate_mapping_overlaps_inflight_vmem(
                        s.interp_pt_mem(),
                        s.core_states.values(),
                        vaddr,
                        pte_size,
                    ));
                }
            } else {
                lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte_size);
            }
        } else {
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn os_init_refines_hl_init<M: mmu::MMU>(c: os::Constants, s: os::State<M>)
    requires
        os::init(c, s),
    ensures
        hlspec::init(c.interp(), s.interp(c)),
{
    let abs_c = c.interp();
    let abs_s = s.interp(c);
    //lemma_effective_mappings_equal_interp_pt_mem(s);
    assert forall|id: nat| id < abs_c.thread_no implies (abs_s.thread_state[id]
        === hlspec::ThreadState::Idle) by {
        assert(c.ult2core.contains_key(id));
        let core = c.ult2core[id];
        assert(hardware::valid_core(c.hw, core));
        assert(s.core_states[core] === os::CoreState::Idle);  //nn
    };
    assert(abs_s.mem === Map::empty());
    assert(abs_s.mappings === Map::empty());
}

proof fn os_next_refines_hl_next<M: mmu::MMU>(c: os::Constants, s1: os::State<M>, s2: os::State<M>)
    requires
        os::next(c, s1, s2),
        s1.inv(c),
    ensures
        hlspec::next(c.interp(), s1.interp(c), s2.interp(c)),
{
    let step = choose|step: os::Step| os::next_step(c, s1, s2, step);
    next_step_refines_hl_next_step(c, s1, s2, step);
}

proof fn next_step_refines_hl_next_step<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    step: os::Step,
)
    requires
        os::next_step(c, s1, s2, step),
        s1.inv(c),
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(c, s1)),
{
    next_step_preserves_inv(c, s1, s2, step);
    match step {
        os::Step::HW { ult_id, step } => match step {
            hardware::Step::ReadWrite { vaddr, paddr, op, walk_result, core } => {
                step_ReadWrite_refines(c, s1, s2, ult_id, vaddr, paddr, op, walk_result, core)
            },
            _ => {},
        },
        //Map steps
        os::Step::MapStart { ult_id, vaddr, pte } => {
            step_Map_Start_refines(c, s1, s2, ult_id, vaddr, pte);
        },
        os::Step::MapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::Step::MapEnd { core, paddr, value, result } => {
            if (s1.sound) {
                step_Map_End_refines(c, s1, s2, core, paddr, value, result);
            }
        },
        //Unmap steps
        os::Step::UnmapStart { ult_id, vaddr } => {
            if (s1.sound) {
                step_Unmap_Start_refines(c, s1, s2, ult_id, vaddr);
            }
        },
        os::Step::UnmapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::Step::UnmapOpChange { core, paddr, value, result } => {
            if s1.sound {
                step_Unmap_Op_Change_refines(c, s1, s2, core, paddr, value, result);
            }
        }
        os::Step::UnmapOpEnd { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::Step::UnmapEnd { core } => {
            step_Unmap_End_refines(c, s1, s2, core);
        },
        _ => {},
    }
}

/*
    &&& match pte {

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

//TODO
proof fn step_ReadWrite_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    ult_id: nat,
    vaddr: nat,
    paddr: nat,
    op: HWRWOp,
    walk_result: WalkResult,
    core: Core,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_HW(c, s1, s2, ult_id, hardware::Step::ReadWrite { vaddr, paddr, op, walk_result, core }),
    ensures
        ({
            let hl_pte = match walk_result {
                WalkResult::Valid { vbase, pte } => {
                    if s1.effective_mappings().contains_key(vbase as nat) {
                        Some((vbase as nat, pte))
                    } else {
                        None
                    }
                },
                WalkResult::Invalid { .. } => None,
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
                ult_id,
                vaddr,
                rwop,
                hl_pte,
            )
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let hl_pte = match walk_result {
        WalkResult::Valid { vbase, pte } => {
            if s1.effective_mappings().contains_key(vbase as nat) {
                Some((vbase as nat, pte))
            } else {
                None
            }
        },
        WalkResult::Invalid { .. } => None,
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
    assert(hlspec::valid_thread(hl_c, ult_id));
    assert(hl_s1.thread_state[ult_id] === hlspec::ThreadState::Idle);
    assert(hl_s2.thread_state === hl_s1.thread_state);
    match hl_pte {
        Some((base, pte)) => {
            assert(s1.effective_mappings().dom().contains(base));
            if (!s1.Unmap_vaddr().contains(base)) {
                assert(s1.interp_pt_mem().dom().contains(base));
                assume(s1.interp_pt_mem().contains_pair(base, pte));
                assert(hl_s1.mappings.dom().contains(base));
                assert(hl_s1.mappings.contains_pair(base, pte));
                assert(between(vaddr, base, base + pte.frame.size));
                assume(hl_c.phys_mem_size == s1.hw.mem.len());
                match rwop {
                    RWOp::Store { new_value, result } => {
                        if (result is Ok) {
                            //assert( s2.hw.mem === s1.mem.hw.update(pmem_idx as int, new_value));
                            assume(hl_s2.mem === hl_s1.mem.insert(vmem_idx, new_value));
                        }
                    },
                    RWOp::Load { is_exec, result } => {
                        assert(hl_s2.mem === hl_s1.mem);
                        if (result is Value) {
                            assume(result->0 == hl_s1.mem.index(vmem_idx));
                        }
                    },
                }
            } else {
                assert(!s1.interp_pt_mem().dom().contains(base));
                assert(false);
            }
        },
        None => {
            if walk_result is Invalid {
                assume(!exists|base: nat, pte: PTE| {
                        &&& #[trigger] s1.interp_pt_mem().contains_pair(base, pte)
                        &&& hlspec::mem_domain_from_entry_contains(
                            c.hw.phys_mem_size,
                            vaddr,
                            base,
                            pte,
                        )
                    });
                assert(hl_s1.mappings.submap_of(s1.interp_pt_mem()));
                assert(forall|key, value| #![auto]
                    !s1.interp_pt_mem().contains_pair(key, value) ==> !hl_s1.mappings.contains_pair(
                        key,
                        value,
                    ));
                assert(!exists|base: nat, pte: PTE|
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
                let vbase = walk_result->Valid_vbase as nat;
                let pte = walk_result->pte;
                //assert(!s1.effective_mappings().dom().contains(vaddr));
                assert(!s1.effective_mappings().dom().contains(vbase));
                assert(!hl_s1.mappings.dom().contains(vbase));
                assume(!hlspec::mem_domain_from_mappings(
                    hl_c.phys_mem_size,
                    hl_s1.mappings,
                ).contains(vmem_idx));
                assume(hl_s2.mem === hl_s1.mem);
                assert(match rwop {
                    RWOp::Store { new_value, result } => result is Undefined,
                    RWOp::Load { is_exec, result } => result is Undefined,
                });
            }
        },
    }
}

proof fn step_Map_Start_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    ult_id: nat,
    vaddr: nat,
    pte: PTE,
)
    requires
        s1.basic_inv(c),
        s2.basic_inv(c),
        os::step_Map_Start(c, s1, s2, ult_id, vaddr, pte),
    ensures
        hlspec::step_Map_start(c.interp(), s1.interp(c), s2.interp(c), ult_id, vaddr, pte),
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
    assert(hlspec::valid_thread(hl_c, ult_id));
    assert(s1.interp(c).thread_state[ult_id] === hlspec::ThreadState::Idle);
    let hl_map_sound = hlspec::step_Map_sound(
        s1.interp(c).mappings,
        s1.interp(c).thread_state.values(),
        vaddr,
        pte,
    );
    lemma_map_soundness_equality(c, s1, vaddr, pte);
    if (hl_map_sound) {
        assert(hl_s1.sound == hl_s2.sound);
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        ));
        lemma_map_insert_values_equality(
            hl_s1.thread_state,
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        );
        assert(hl_s2.thread_state.values().insert(hlspec::ThreadState::Idle)
            =~= hl_s1.thread_state.values().insert(hlspec::ThreadState::Map { vaddr, pte }));
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
                    &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
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
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        ));
    } else {
        assert(!s2.sound);
        assert(hlspec::unsound_state(hl_s1, hl_s2));
    };
}

proof fn step_Map_End_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    core: Core,
    paddr: usize,
    value: usize,
    result: Result<(), ()>,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Map_End(c, s1, s2, core, paddr, value, result),
        s1.sound,
    ensures
        ({
            &&& s1.core_states[core] matches os::CoreState::MapExecuting { ult_id, .. }
            &&& hlspec::step_Map_end(c.interp(), s1.interp(c), s2.interp(c), ult_id, result)
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let ult_id = s1.core_states[core]->MapExecuting_ult_id;
    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
    let pte = s1.core_states[core]->MapExecuting_pte;

    assert(s2.sound);
    assert(hlspec::valid_thread(hl_c, ult_id));
    assert(s1.interp(c).thread_state[ult_id] is Map);

    if (candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte)) {
        assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
        assert(result is Err);
        assert(s1.interp_pt_mem() == s2.interp_pt_mem());

        lemma_map_insert_values_equality(s1.core_states, core, os::CoreState::Idle);
        assert(s1.core_states.values().insert(os::CoreState::Idle)
            =~= s2.core_states.values().insert(s1.core_states[core]));

        assert forall|key| #[trigger]
            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Idle,
        )[key] == hl_s2.thread_state[key] by {
            let core_of_key = c.ult2core[key];
            if (core_of_key === core) {
            } else {
                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            }
        }
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Idle,
        ));
        assert(s1.core_states[core] is MapExecuting);

        lemma_map_insert_values_equality(
            hl_s1.thread_state,
            ult_id,
            hlspec::ThreadState::Idle,
        );
        assert(hl_s1.thread_state.values().insert(hlspec::ThreadState::Idle)
            =~= hl_s2.thread_state.values().insert(hl_s1.thread_state[ult_id]));
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
                    &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                    &&& vaddr === base
                };
            assert(!(hl_s1.thread_state[ult_id] is Unmap));
            assert(hl_s1.thread_state.values().insert(hlspec::ThreadState::Idle).contains(
                threadstate,
            ));
            assert(hl_s2.thread_state.values().contains(threadstate));
        }
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());

    } else {
        lemma_os_overlap_vmem_implies_hl_or_inflight_overlap_vmem(c, s1, vaddr, pte);
        if (!hlspec::candidate_mapping_overlaps_inflight_vmem(
            s1.interp(c).thread_state.values(),
            vaddr,
            pte.frame.size,
        )) {
            assert(hl_s1.thread_state[ult_id] is Map);
            let map_vaddr = hl_s1.thread_state[ult_id]->Map_vaddr;
            let map_pte = hl_s1.thread_state[ult_id]->Map_pte;
            //assert(hl_s1.thread_state[matches])
            assert(hl_s1.thread_state.dom().contains(ult_id));
            assert(hl_s1.thread_state.values().contains(hl_s1.thread_state[ult_id]));
            assert(overlap(
                MemRegion { base: map_vaddr, size: map_pte.frame.size },
                MemRegion { base: vaddr, size: pte.frame.size },
            ));

        } else {
            assert(!candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(
                s1.interp(c).thread_state.values(),
                vaddr,
                pte.frame.size,
            ));
            lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(
                c,
                s1,
                vaddr,
                pte.frame.size,
            );
            assert(os::candidate_mapping_overlaps_inflight_vmem(
                s1.interp_pt_mem(),
                s1.core_states.values(),
                vaddr,
                pte.frame.size,
            ));
            if (!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)) {
                assert forall|key| #[trigger]
                    hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
                    ult_id,
                    hlspec::ThreadState::Idle,
                )[key] == hl_s2.thread_state[key] by {
                    let core_of_key = c.ult2core[key];
                    if (core_of_key === core) {
                    } else {
                        assert(!s1.core_states[core_of_key].holds_lock());
                        if (s1.core_states[core_of_key] is UnmapWaiting) {
                            assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                            assert(s1.core_states[c.ult2core[key]]
                                === s2.core_states[c.ult2core[key]]);
                            let Unmap_vaddr = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                            if (vaddr == Unmap_vaddr) {
                                assert(!s1.core_states[core].is_idle()
                                    && !s1.core_states[core_of_key].is_idle() && overlap(
                                    MemRegion {
                                        base: s1.core_states[core].vaddr(),
                                        size: s1.core_states[core].vmem_pte_size(
                                            s1.interp_pt_mem(),
                                        ),
                                    },
                                    MemRegion {
                                        base: s1.core_states[core_of_key].vaddr(),
                                        size: s1.core_states[core_of_key].vmem_pte_size(
                                            s1.interp_pt_mem(),
                                        ),
                                    },
                                ));
                                assert(core_of_key == core);
                                assert(false);
                            }
                        } else {
                            assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                            assert(s1.core_states[c.ult2core[key]]
                                === s2.core_states[c.ult2core[key]]);
                        }
                    }
                }
                assert(hl_s2.thread_state === hl_s1.thread_state.insert(
                    ult_id,
                    hlspec::ThreadState::Idle,
                ));
                //assert(!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
                assert(result is Ok);
                assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                assert(!s1.inflight_unmap_vaddr().contains(vaddr));
                assert forall|idx|
                    s1.inflight_unmap_vaddr().contains(
                        idx,
                    ) implies s2.inflight_unmap_vaddr().contains(idx) by {
                    if (s1.inflight_unmap_vaddr().contains(idx)) {
                        assert(s1.interp_pt_mem().dom().contains(idx));
                        let unmap_core = choose|unmap_core|
                            s1.core_states.dom().contains(unmap_core)
                                && match s1.core_states[unmap_core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === idx
                                },
                                _ => false,
                            };
                        if (unmap_core != core) {
                            assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                            assert(s2.interp_pt_mem().dom().contains(idx));
                            assert(s2.core_states.dom().contains(unmap_core));
                            assert(s1.core_states[unmap_core] === s2.core_states[unmap_core]);
                        }
                    }
                };
                assert forall|idx|
                    s2.inflight_unmap_vaddr().contains(
                        idx,
                    ) implies s1.inflight_unmap_vaddr().contains(idx) by {
                    if (s2.inflight_unmap_vaddr().contains(idx)) {
                        assert(s2.interp_pt_mem().dom().contains(idx));

                        let unmap_core = choose|unmap_core|
                            s2.core_states.dom().contains(unmap_core)
                                && match s1.core_states[unmap_core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === idx
                                },
                                _ => false,
                            };
                        if (idx != vaddr) {
                            if (unmap_core != core) {
                                assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                                assert(s2.interp_pt_mem().dom().contains(idx));
                                assert(s2.core_states.dom().contains(unmap_core));
                                assert(s1.core_states[unmap_core] === s2.core_states[unmap_core]);
                            }
                        } else {
                            assert(!s1.core_states[core].is_idle()
                                && !s1.core_states[unmap_core].is_idle() && overlap(
                                MemRegion {
                                    base: s1.core_states[core].vaddr(),
                                    size: s1.core_states[core].vmem_pte_size(s1.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s1.core_states[unmap_core].vaddr(),
                                    size: s1.core_states[unmap_core].vmem_pte_size(
                                        s1.interp_pt_mem(),
                                    ),
                                },
                            ));
                        }
                    }
                };
                assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
                assert(hl_s2.mappings.contains_pair(vaddr, pte));
                assert(forall|idx|
                    hl_s1.mappings.contains_key(idx) ==> hl_s2.mappings.contains_key(idx));
                assert(forall|idx|
                    #![auto]
                    hl_s2.mappings.contains_key(idx) ==> hl_s1.mappings.insert(
                        vaddr,
                        pte,
                    ).contains_key(idx));
                assert(hl_s2.mappings =~= hl_s1.mappings.insert(vaddr, pte));
                lemma_mem_domain_from_mappings(
                    c.interp().phys_mem_size,
                    hl_s1.mappings,
                    vaddr,
                    pte,
                );
                assert forall|idx: nat|
                    #![auto]
                    hl_s1.mem.dom().contains(idx) implies hl_s2.mem[idx] === hl_s1.mem[idx] by {
                    // TODO overlapping mapped vmem
                    if (hl_s1.mem.dom().contains(idx)) {
                        assert(hlspec::mem_domain_from_mappings_contains(
                            hl_c.phys_mem_size,
                            idx,
                            hl_s1.mappings,
                        ));
                        assert(hl_s2.mem.dom().contains(idx));
                        let vidx = (idx * WORD_SIZE as nat);
                        let (mem_base, mem_pte): (nat, PTE) = choose|
                            base: nat,
                            pte: PTE,
                        |
                            {
                                &&& #[trigger] hl_s1.mappings.contains_pair(base, pte)
                                &&& hlspec::mem_domain_from_entry_contains(
                                    hl_c.phys_mem_size,
                                    vidx,
                                    base,
                                    pte,
                                )
                            };
                        let paddr = (mem_pte.frame.base + (vidx - mem_base)) as nat;

                        assert(hl_s1.mappings.contains_pair(mem_base, mem_pte));
                        assert(between(vidx, mem_base, mem_base + mem_pte.frame.size));

                        assert forall|page, entry|
                            hl_s2.mappings.contains_pair(page, entry) && between(
                                vidx,
                                page,
                                page + entry.frame.size,
                            ) implies (page == mem_base) && (entry == mem_pte) by {
                            if (hl_s2.mappings.contains_pair(page, entry) && between(
                                vidx,
                                page,
                                page + entry.frame.size,
                            )) {
                                assert(overlap(
                                    MemRegion { base: page, size: entry.frame.size },
                                    MemRegion { base: mem_base, size: mem_pte.frame.size },
                                ));
                                assert(s2.interp_pt_mem().dom().contains(page));
                                assert(s2.interp_pt_mem().dom().contains(mem_base));
                                if (s2.interp_pt_mem().remove(page).dom().contains(mem_base)) {
                                    assert(false);
                                } else {
                                    assert(page == mem_base);
                                    assert(entry == mem_pte);
                                }
                            }
                        }
                        assert forall|page, entry|
                            hl_s1.mappings.contains_pair(page, entry) && between(
                                vidx,
                                page,
                                page + entry.frame.size,
                            ) implies (page == mem_base) && (entry == mem_pte) by {
                            assert(s1.effective_mappings().dom().subset_of(
                                s2.effective_mappings().dom(),
                            ));
                            assert(hl_s1.mappings.submap_of(hl_s2.mappings));
                            assert(hl_s2.mappings.contains_pair(page, entry) && between(
                                vidx,
                                page,
                                page + entry.frame.size,
                            ));
                        }
                    }
                }
                assert(hl_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                    hl_c.phys_mem_size,
                    hl_s2.mappings,
                ));
            } else {
                assert(!candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte));
                assert(result is Err);
                let os_overlap_vaddr = choose|b: nat|
                    #![auto]
                    {
                        &&& s1.interp_pt_mem().dom().contains(b)
                        &&& overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: b, size: s1.interp_pt_mem()[b].frame.size },
                        )
                    };

                assert(s1.interp_pt_mem().dom().contains(os_overlap_vaddr));
                assert(!hl_s1.mappings.dom().contains(os_overlap_vaddr));
                assert(s1.inflight_unmap_vaddr().contains(os_overlap_vaddr));
                let unmap_core = choose|core|
                    s1.core_states.dom().contains(core) && match s1.core_states[core] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === os_overlap_vaddr
                        },
                        _ => false,
                    };
                assert(!s1.core_states[unmap_core].holds_lock());
                assert(s1.core_states[unmap_core] is UnmapWaiting);
                assert(overlap(
                    MemRegion { base: vaddr, size: pte.frame.size },
                    MemRegion {
                        base: s1.core_states[unmap_core]->UnmapWaiting_vaddr,
                        size:
                            s1.interp_pt_mem()[s1.core_states[unmap_core]->UnmapWaiting_vaddr].frame.size,
                    },
                ));
                assert(hardware::valid_core(c.hw, core) && hardware::valid_core(c.hw, unmap_core)
                    && !s1.core_states[core].is_idle() && !s1.core_states[unmap_core].is_idle()
                    && overlap(
                    MemRegion {
                        base: s1.core_states[core].vaddr(),
                        size: s1.core_states[core].vmem_pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[unmap_core].vaddr(),
                        size: s1.core_states[unmap_core].vmem_pte_size(s1.interp_pt_mem()),
                    },
                ) && (core != unmap_core));
            }
        }
    }
}

proof fn step_Unmap_Start_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    ult_id: nat,
    vaddr: nat,
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_Unmap_Start(c, s1, s2, ult_id, vaddr),
    ensures
        hlspec::step_Unmap_start(c.interp(), s1.interp(c), s2.interp(c), ult_id, vaddr),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    let core = c.ult2core[ult_id];
    let pte = if (hl_s1.mappings.dom().contains(vaddr)) {
        Some(hl_s1.mappings.index(vaddr))
    } else {
        Option::None
    };
    let pte_size = if (pte is Some) {
        pte.unwrap().frame.size
    } else {
        0
    };
    assert(hlspec::step_Unmap_enabled(vaddr));
    assert(hlspec::valid_thread(hl_c, ult_id));
    assert(hl_s1.thread_state[ult_id] === hlspec::ThreadState::Idle);

    lemma_unmap_soundness_equality(c, s1, vaddr, pte_size);
    if hlspec::step_Unmap_sound(hl_s1.thread_state.values(), vaddr, pte_size) {
        assert(hl_s1.sound == hl_s2.sound);
        assert forall|key| #[trigger]
            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Unmap { vaddr, pte },
        )[key] == hl_s2.thread_state[key] by {
            let core_of_key = c.ult2core[key];
            if (core_of_key === core) {
                if (key == ult_id) {
                    assert(s2.core_states == s1.core_states.insert(
                        core,
                        os::CoreState::UnmapWaiting { ult_id, vaddr },
                    ));
                    assert(s2.core_states[core] is UnmapWaiting);
                    let thread_pte = hl_s2.thread_state[ult_id]->Unmap_pte;
                    if (s1.interp_pt_mem().dom().contains(vaddr)
                        && s1.inflight_unmap_vaddr().contains(vaddr)) {
                        let overlap_core = choose|core|
                            s1.core_states.dom().contains(core) && match s1.core_states[core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr: v }
                                | os::CoreState::UnmapOpExecuting { ult_id, vaddr: v, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr: v, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr: v, .. } => {
                                    vaddr === v
                                },
                                _ => false,
                            };
                        //overlap{};
                        assert(!s2.core_states[core].is_idle()
                            && !s2.core_states[overlap_core].is_idle() && overlap(
                            MemRegion {
                                base: s2.core_states[core].vaddr(),
                                size: s2.core_states[core].vmem_pte_size(s2.interp_pt_mem()),
                            },
                            MemRegion {
                                base: s2.core_states[overlap_core].vaddr(),
                                size: s2.core_states[overlap_core].vmem_pte_size(
                                    s2.interp_pt_mem(),
                                ),
                            },
                        ));
                    }
                }
            } else {
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            }
        }
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Unmap { vaddr, pte },
        ));
        if (pte is None) {
            assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
            assert forall|ids|
                s1.inflight_unmap_vaddr().contains(ids) implies s2.inflight_unmap_vaddr().contains(
                ids,
            ) by {
                if s1.inflight_unmap_vaddr().contains(ids) {
                    let unmap_core = choose|cr|
                        s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === ids
                            },
                            _ => false,
                        };
                    assert(!(unmap_core == core));
                    assert(s2.core_states.dom().contains(unmap_core));
                }
            }
            assert(hl_s2.mappings === hl_s1.mappings);
            assert(hl_s2.mem =~= hl_s1.mem);
            assert(hl_s1.mem.dom() === hlspec::mem_domain_from_mappings(
                hl_c.phys_mem_size,
                hl_s1.mappings,
            ));
            assert(hl_s1.mappings =~= hl_s1.mappings.remove(vaddr));
            assert(hl_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                hl_c.phys_mem_size,
                hl_s1.mappings.remove(vaddr),
            ));
        } else {
            assert(s2.core_states == s1.core_states.insert(
                core,
                os::CoreState::UnmapWaiting { ult_id, vaddr },
            ));
            lemma_map_insert_value(
                s1.core_states,
                core,
                os::CoreState::UnmapWaiting { ult_id, vaddr },
            );
            // assert(s2.inflight_unmap_vaddr().contains(vaddr));
            //assert(!s2.effective_mappings().dom().contains(vaddr));
            assert forall|ids|
                s1.inflight_unmap_vaddr().insert(vaddr).contains(
                    ids,
                ) implies #[trigger] s2.inflight_unmap_vaddr().contains(ids) by {
                if s1.inflight_unmap_vaddr().contains(ids) {
                    if (ids === vaddr) {
                    } else {
                        let unmap_core = choose|cr|
                            s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === ids
                                },
                                _ => false,
                            };
                        assert(!(unmap_core == core));
                        assert(s2.core_states.dom().contains(unmap_core));
                    }
                } else {
                }
            }
            //  assert(s2.inflight_unmap_vaddr() =~= s1.inflight_unmap_vaddr().insert(vaddr));

            assert(hl_s2.mappings =~= hl_s1.mappings.remove(vaddr));
            assert(hl_s1.mappings =~= hl_s2.mappings.insert(vaddr, hl_s1.mappings.index(vaddr)));
            //   assert(hl_s2.mem.dom() === hlspec::mem_domain_from_mappings(hl_c.phys_mem_size, hl_s1.mappings.remove(vaddr)));
            //   assert(hl_s1.mem.dom() === hlspec::mem_domain_from_mappings(hl_c.phys_mem_size, hl_s1.mappings));
            lemma_mem_domain_from_mappings(
                hl_c.phys_mem_size,
                hl_s2.mappings,
                vaddr,
                hl_s1.mappings.index(vaddr),
            );
            // assert( hl_s1.mem.dom() =~= hl_s2.mem.dom());
            assert forall|idx: nat| #![auto] hl_s2.mem.dom().contains(idx) implies hl_s2.mem[idx]
                === hl_s1.mem[idx] by {
                if (hl_s2.mem.dom().contains(idx)) {
                    assert(hlspec::mem_domain_from_mappings_contains(
                        hl_c.phys_mem_size,
                        idx,
                        hl_s2.mappings,
                    ));
                    assert(hl_s1.mem.dom().contains(idx));
                    let vidx = (idx * WORD_SIZE as nat);
                    let (mem_base, mem_pte): (nat, PTE) = choose|
                        base: nat,
                        pte: PTE,
                    |
                        {
                            &&& #[trigger] hl_s2.mappings.contains_pair(base, pte)
                            &&& hlspec::mem_domain_from_entry_contains(
                                hl_c.phys_mem_size,
                                vidx,
                                base,
                                pte,
                            )
                        };
                    let paddr = (mem_pte.frame.base + (vidx - mem_base)) as nat;

                    assert(hl_s2.mappings.contains_pair(mem_base, mem_pte));
                    assert(between(vidx, mem_base, mem_base + mem_pte.frame.size));

                    assert forall|page, entry|
                        hl_s1.mappings.contains_pair(page, entry) && between(
                            vidx,
                            page,
                            page + entry.frame.size,
                        ) implies (page == mem_base) && (entry == mem_pte) by {
                        assert(overlap(
                            MemRegion { base: page, size: entry.frame.size },
                            MemRegion { base: mem_base, size: mem_pte.frame.size },
                        ));
                        assert(s1.interp_pt_mem().dom().contains(page));
                        assert(s1.interp_pt_mem().dom().contains(mem_base));
                        if (s1.interp_pt_mem().remove(page).dom().contains(mem_base)) {
                            assert(false);
                        } else {
                            assert(page == mem_base);
                            assert(entry == mem_pte);
                        }
                    }
                    assert forall|page, entry|
                        hl_s2.mappings.contains_pair(page, entry) && between(
                            vidx,
                            page,
                            page + entry.frame.size,
                        ) implies (page == mem_base) && (entry == mem_pte) by {
                        assert(s2.effective_mappings().dom().subset_of(
                            s1.effective_mappings().dom(),
                        ));
                        assert(hl_s2.mappings.submap_of(hl_s1.mappings));
                        assert(hl_s1.mappings.contains_pair(page, entry) && between(
                            vidx,
                            page,
                            page + entry.frame.size,
                        ));
                    }
                }
            }
        }
    } else {
    }
}

proof fn step_Unmap_Op_Change_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    core: Core,
    paddr: usize,
    value: usize,
    result: Result<PTE, ()>
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_Unmap_Op_Change(c, s1, s2, core, paddr, value, result),
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c)),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    assert(s1.core_states[core] is UnmapOpExecuting);
    let vaddr = s1.core_states[core]->UnmapOpExecuting_vaddr;

    assert(hl_s1.thread_state.dom() === hl_s2.thread_state.dom());
    assert forall|key| #[trigger]
        hl_s1.thread_state.contains_key(key) implies hl_s1.thread_state[key] == hl_s2.thread_state[key] by {
        assert(c.valid_ult(key));
        assert(hl_s2.thread_state.dom().contains(key));
        let core_of_key = c.ult2core[key];
        assert(hardware::valid_core(c.hw, core));
        assert(s1.core_states[core].holds_lock());
        assert(hardware::valid_core(c.hw, core_of_key));
        if s1.core_states[core_of_key].holds_lock() {
            assert(core_of_key === core);
        } else {
            assert(!(core_of_key === core));
            assert(!s1.core_states[core_of_key].holds_lock());
            assert(s1.core_states.index(core_of_key) == s2.core_states.index(core_of_key));
            assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            if (s1.core_states.index(core_of_key) is UnmapWaiting) {
                let vaddr_of_key = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                if (vaddr_of_key == vaddr) {
                    assert(overlap(
                        MemRegion {
                            base: s2.core_states[core_of_key].vaddr(),
                            size: s2.core_states[core_of_key].vmem_pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].vmem_pte_size(s2.interp_pt_mem()),
                        },
                    ));

                } else {
                }
            } else {
            }
        }
    }
    assert(hl_s1.thread_state =~= hl_s2.thread_state);
    assert(s1.interp_pt_mem().remove(vaddr) =~= s2.interp_pt_mem());
    if (s1.interp_pt_mem().dom().contains(vaddr)) {
        assert(s1.core_states.dom().contains(core));
        assert(s1.inflight_unmap_vaddr().contains(vaddr));
        assert forall|ids|
            s1.inflight_unmap_vaddr().contains(
                ids,
            ) implies #[trigger] s2.inflight_unmap_vaddr().insert(vaddr).contains(ids) by {
            if s1.inflight_unmap_vaddr().contains(ids) {
                if (ids === vaddr) {
                } else {
                    assert(s1.interp_pt_mem().dom().contains(ids));
                    assert(s2.interp_pt_mem().dom().contains(ids));
                    let unmap_core = choose|cr|
                        s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === ids
                            },
                            _ => false,
                        };
                    assert(!(unmap_core == core));
                    assert(s2.core_states.dom().contains(unmap_core));
                }
            } else {
            }
        }
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr().insert(vaddr));

    } else {
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert forall|ids|
            s1.inflight_unmap_vaddr().contains(ids) implies s2.inflight_unmap_vaddr().contains(
            ids,
        ) by {
            if s1.inflight_unmap_vaddr().contains(ids) {
                assert(!(ids === vaddr));
                assert(s1.interp_pt_mem().dom().contains(ids));
                assert(s2.interp_pt_mem().dom().contains(ids));
                let unmap_core = choose|cr|
                    s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapOpExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === ids
                        },
                        _ => false,
                    };
                assert(!(unmap_core == core));
                assert(s2.core_states.dom().contains(unmap_core));
            } else {
            }
        }
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
    }
    assert(s1.effective_mappings() =~= s2.effective_mappings())
}

proof fn step_Unmap_End_refines<M: mmu::MMU>(
    c: os::Constants,
    s1: os::State<M>,
    s2: os::State<M>,
    core: Core,
)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_Unmap_End(c, s1, s2, core),
    ensures
        ({
            &&& s1.core_states[core] matches os::CoreState::UnmapOpDone { result, ult_id, .. }
            &&& hlspec::step_Unmap_end(c.interp(), s1.interp(c), s2.interp(c), ult_id, result_map_ok(result, |r| ()))
        } || {
            &&& s1.core_states[core] matches os::CoreState::UnmapShootdownWaiting {
                ult_id,
                result,
                ..
            }
            &&& hlspec::step_Unmap_end(c.interp(), s1.interp(c), s2.interp(c), ult_id, result_map_ok(result, |r| ()))
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    match s1.core_states[core] {
        os::CoreState::UnmapShootdownWaiting { ult_id, result, vaddr, .. }
        | os::CoreState::UnmapOpDone { result, ult_id, vaddr, .. } => {
            assert(hlspec::valid_thread(hl_c, ult_id));
            assert(hl_s2.sound == hl_s1.sound);
            assert(hl_s2.thread_state === hl_s1.thread_state.insert(
                ult_id,
                hlspec::ThreadState::Idle,
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
                if key == vaddr {
                    assert(false);
                } else {
                    if s1.inflight_unmap_vaddr().contains(key) {
                        let threadstate = choose|thread_state| {
                                &&& s1.interp_thread_state(c).values().contains(thread_state)
                                &&& s1.interp_pt_mem().dom().contains(key)
                                &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                                &&& vaddr === key
                            };
                        let ult_id2 = choose|id|
                            #![auto] s1.interp_thread_state(c).dom().contains(id)
                            && s1.interp_thread_state(c)[id] == threadstate;
                        assert(ult_id2 != ult_id);
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
