use vstd::prelude::*;

//use crate::impl_u::spec_pt;
//use crate::spec_t::hardware::Core;
use crate::definitions_t::{
    above_zero, aligned, between, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap, HWLoadResult, HWRWOp, HWStoreResult,
    LoadResult, MemRegion, PageTableEntry, RWOp, StoreResult, WORD_SIZE,
};
use crate::spec_t::hlproof::lemma_mem_domain_from_mappings;
use crate::spec_t::os_invariant::{
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl,
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl, next_step_preserves_inv,
};
use crate::spec_t::{hardware, hlspec, mem, os};

verus! {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_inflight_vaddr_equals_hl_unmap(c: os::OSConstants, s: os::OSVariables)
    requires
        s.basic_inv(c),
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
// Map lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn map_values_contain_value_of_contained_key<A, B>(map: Map<A, B>, key: A)
    requires
        map.dom().contains(key),
    ensures
        map.values().contains(map[key]),
{
}

proof fn lemma_map_insert_value<A, B>(map: Map<A, B>, key: A, value: B)
    requires
    ensures
        map.insert(key, value).values().contains(value),
{
    assert(map.insert(key, value).dom().contains(key));
    assert(map.insert(key, value)[key] == value);
}

pub proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    //
    assert forall|values| #![auto] map.values().insert(value).contains(values) implies map.insert(
        key,
        value,
    ).values().insert(map.index(key)).contains(values) by {
        if (values == value) {
            lemma_map_insert_value(map, key, value);
        } else {
            let k = choose|some_key| #[trigger]
                map.dom().contains(some_key) && (map[some_key] == values);
            assert(map.insert(key, value).dom().contains(k));
            if (k == key) {
                assert(map.index(key) == values);
            } else {
                assert(map[k] === map.insert(key, value)[k]);
            }
        }
    }
    assert(map.values().insert(value) =~= map.insert(key, value).values().insert(map.index(key)));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_map_soundness_equality(
    c: os::OSConstants,
    s: os::OSVariables,
    vaddr: nat,
    pte: PageTableEntry,
)
    requires
        s.basic_inv(c),
        above_zero(pte.frame.size),
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

proof fn lemma_os_overlap_vmem_implies_hl_or_inflight_overlap_vmem(
    c: os::OSConstants,
    s: os::OSVariables,
    vaddr: nat,
    pte: PageTableEntry,
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
                let base = choose|b: nat|
                    #![auto]
                    {
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
                            os::CoreState::UnmapWaiting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
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
            if (s1.sound) {
                step_Map_End_refines(c, s1, s2, core, result);
            }
        },
        //Unmap steps
        os::OSStep::UnmapStart { ULT_id, vaddr } => {
            if (s1.sound) {
                step_Unmap_Start_refines(c, s1, s2, ULT_id, vaddr);
            }
        },
        os::OSStep::UnmapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
        },
        os::OSStep::UnmapOpEnd { core, result } => {
            if (s1.sound) {
                step_Unmap_Op_End_refines(c, s1, s2, core, result);
            }
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

//TODO
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
        s1.basic_inv(c),
        s2.basic_inv(c),
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

//TODO
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
        s1.sound,
    ensures
        ({
            &&& s1.core_states[core] matches os::CoreState::MapExecuting { ULT_id, .. }
            &&& hlspec::step_Map_end(c.interp(), s1.interp(c), s2.interp(c), ULT_id, result)
        }),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    let ULT_id = s1.core_states[core]->MapExecuting_ULT_id;
    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
    let pte = s1.core_states[core]->MapExecuting_pte;

    assert(s2.sound);
    assert(hlspec::valid_thread(hl_c, ULT_id));
    assert(s1.interp(c).thread_state[ULT_id] is Map);
    if (candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte)) {
        assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
        assert(result is Err);
        assert(s1.interp_pt_mem() == s2.interp_pt_mem());

        lemma_map_insert_values_equality(s1.core_states, core, os::CoreState::Idle);
        assert(s1.core_states.values().insert(os::CoreState::Idle)
            =~= s2.core_states.values().insert(s1.core_states[core]));

        assert forall|key| #[trigger]
            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Empty,
        )[key] == hl_s2.thread_state[key] by {
            let core_of_key = c.ULT2core[key];
            if (core_of_key === core) {
            } else {
                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                assert(s1.core_states[c.ULT2core[key]] === s2.core_states[c.ULT2core[key]]);
            }
        }
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Empty,
        ));
        assert(s1.core_states[core] is MapExecuting);

        lemma_map_insert_values_equality(
            hl_s1.thread_state,
            ULT_id,
            hlspec::AbstractArguments::Empty,
        );
        assert(hl_s1.thread_state.values().insert(hlspec::AbstractArguments::Empty)
            =~= hl_s2.thread_state.values().insert(hl_s1.thread_state[ULT_id]));
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
            assert(!(hl_s1.thread_state[ULT_id] is Unmap));
            assert(hl_s1.thread_state.values().insert(hlspec::AbstractArguments::Empty).contains(
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
            assert forall|key| #[trigger]
                hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
                ULT_id,
                hlspec::AbstractArguments::Empty,
            )[key] == hl_s2.thread_state[key] by {
                let core_of_key = c.ULT2core[key];
                if (core_of_key === core) {
                } else {
                    assert(!s1.core_states[core_of_key].holds_lock());
                    if (s1.core_states[core_of_key] is UnmapWaiting) {
                        assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                        assert(s1.core_states[c.ULT2core[key]] === s2.core_states[c.ULT2core[key]]);
                        let Unmap_vaddr = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                        if (vaddr == Unmap_vaddr) {
                            assume(false); //TODO overlapping inflight vmem, make an assert(false); here
                        } 
                    } else {
                        assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                        assert(s1.core_states[c.ULT2core[key]] === s2.core_states[c.ULT2core[key]]);
                    }
                }
            }
            assert(hl_s2.thread_state === hl_s1.thread_state.insert(
                ULT_id,
                hlspec::AbstractArguments::Empty,
            ));
            assert(!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
            assert(result is Ok);
            assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
            assert(!s1.inflight_unmap_vaddr().contains(vaddr));
            //TODO think about this since an invalid unmap would be made valid by a map
            assume(hl_s2.mappings === hl_s1.mappings.insert(vaddr, pte));
            lemma_mem_domain_from_mappings(c.interp().phys_mem_size, hl_s1.mappings, vaddr, pte);
            assert forall|idx: nat|
                #![auto]
                hl_s1.mem.dom().contains(idx) implies hl_s2.mem[idx] === hl_s1.mem[idx] by {

                    assume(false); // TODO overlapping mapped vmem 

                }            
                assert(hl_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                hl_c.phys_mem_size,
                hl_s2.mappings,
            ));
        } else {
            lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s1, vaddr, pte.frame.size);
            assume(false);  //TODO vmem invariant assert false
        }
    }
}

//TODO
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
        s1.sound,
        os::step_Unmap_Start(c, s1, s2, ULT_id, vaddr),
    ensures
        hlspec::step_Unmap_start(c.interp(), s1.interp(c), s2.interp(c), ULT_id, vaddr),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    let core = c.ULT2core[ULT_id];
    let pte = if (hl_s1.mappings.dom().contains(vaddr)) {
        Some(hl_s1.mappings.index(vaddr))
    } else {
        Option::None
    };
    let pte_size = if (pte is Some) {pte.unwrap().frame.size} else {0};
    assert(hlspec::step_Unmap_enabled(vaddr));
    assert(hlspec::valid_thread(hl_c, ULT_id));
    assert(hl_s1.thread_state[ULT_id] === hlspec::AbstractArguments::Empty);
    
    lemma_unmap_soundness_equality(c, s1, vaddr, pte_size);
    if hlspec::step_Unmap_sound(
        hl_s1.thread_state.values(),
        vaddr,
        pte_size,
    ) {
        assert(hl_s1.sound == hl_s2.sound);
        assert forall|key| #[trigger]
            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Unmap { vaddr, pte },
        )[key] == hl_s2.thread_state[key] by {
            let core_of_key = c.ULT2core[key];
            if (core_of_key === core) {
                if (key == ULT_id) {
                    assert(s2.core_states == s1.core_states.insert(
                        core,
                        os::CoreState::UnmapWaiting { ULT_id, vaddr },
                    ));
                    assert(s2.core_states[core] is UnmapWaiting);
                    let thread_pte = hl_s2.thread_state[ULT_id]->Unmap_pte;
                    if (s1.interp_pt_mem().dom().contains(vaddr)
                        && s1.inflight_unmap_vaddr().contains(vaddr)) {
                        let overlap_core = choose|core|
                            s1.core_states.dom().contains(core) && match s1.core_states[core] {
                                os::CoreState::UnmapWaiting { ULT_id, vaddr: v }
                                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr: v }
                                | os::CoreState::UnmapOpDone { ULT_id, vaddr: v, .. }
                                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr: v, .. } => {
                                    vaddr === v
                                },
                                _ => false,
                            };
                        assume(false);  //TODO assert false here with overlapping invariant
                    }
                }
            } else {
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                assert(s1.core_states[c.ULT2core[key]] === s2.core_states[c.ULT2core[key]]);
            }
        }
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ULT_id,
            hlspec::AbstractArguments::Unmap { vaddr, pte },
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
                            os::CoreState::UnmapWaiting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
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
                os::CoreState::UnmapWaiting { ULT_id, vaddr },
            ));
            lemma_map_insert_value(
                s1.core_states,
                core,
                os::CoreState::UnmapWaiting { ULT_id, vaddr },
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
                                os::CoreState::UnmapWaiting { ULT_id, vaddr }
                                | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                                | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
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
            //    assert(hl_s1.mem.dom() === hlspec::mem_domain_from_mappings(hl_c.phys_mem_size, hl_s1.mappings));
            lemma_mem_domain_from_mappings(
                hl_c.phys_mem_size,
                hl_s2.mappings,
                vaddr,
                hl_s1.mappings.index(vaddr),
            );
            assert forall|idx: nat| #![auto] hl_s2.mem.dom().contains(idx) implies hl_s2.mem[idx]
                === hl_s1.mem[idx] by {
                assert(hl_s1.mem.dom().contains(idx));
                let vddr = idx * WORD_SIZE as nat;
                let (mem_base, mem_pte): (nat, PageTableEntry) = choose|b: nat, p: PageTableEntry|
                    #![auto]
                    s1.interp_pt_mem().contains_pair(b, p) && between(vddr, b, b + p.frame.size);
                let paddr = (mem_pte.frame.base + (vddr - mem_base)) as nat;
                let pmem_idx = mem::word_index_spec(paddr);
                assert(s1.hw.mem[pmem_idx as int] === s2.hw.mem[pmem_idx as int]);
                assume(false);  //TODO smth smth overlap

            }
        }
    } else {
    }
}

//TODO
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
        s1.sound,
        os::step_Unmap_Op_End(c, s1, s2, core, result),
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
            if (s1.core_states.index(core_of_key) is UnmapWaiting) {
                let vaddr_of_key = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                if (vaddr_of_key == vaddr) {
                    assume(false);  //TODO show overlap, we have 2 different cores that both unmap the same vaddr
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
                            os::CoreState::UnmapWaiting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                            | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
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
                        os::CoreState::UnmapWaiting { ULT_id, vaddr }
                        | os::CoreState::UnmapOpExecuting { ULT_id, vaddr }
                        | os::CoreState::UnmapOpDone { ULT_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ULT_id, vaddr, .. } => {
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
