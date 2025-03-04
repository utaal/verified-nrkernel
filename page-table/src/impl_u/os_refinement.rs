use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    between, candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap,
    MemRegion, PTE, WORD_SIZE, Core
};
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::mmu::{ self, rl1 };
#[cfg(verus_keep_ghost)]
use crate::spec_t::hlproof::lemma_mem_domain_from_mappings;
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_invariant::{
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl,
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl, next_step_preserves_inv,
    lemma_map_insert_values_equality, lemma_map_insert_value,
};
use crate::spec_t::{hlspec, os};
use crate::theorem::RLbl;

verus! {


///////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_inflight_vaddr_equals_hl_unmap(c: os::Constants, s: os::State)
    requires s.inv_basic(c),
    ensures
        forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr)
            <==> exists|thread_state| {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().dom().contains(v_addr)
                &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
                &&& vaddr === v_addr
            },
{
    // proof ==> direction
    assert forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr) implies exists|thread_state| {
        &&& s.interp_thread_state(c).values().contains(thread_state)
        &&& s.interp_pt_mem().dom().contains(v_addr)
        &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
        &&& vaddr === v_addr
    } by {
        let core = choose|core| {
            &&& s.core_states.dom().contains(core)
            &&& ({
                &&& s.core_states[core] matches os::CoreState::UnmapWaiting { vaddr, .. }
                &&& vaddr == v_addr
            } || {
                &&& s.core_states[core] matches os::CoreState::UnmapExecuting { vaddr, .. }
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
        match s.core_states[core] {
            os::CoreState::UnmapWaiting { ult_id, vaddr }
            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
    // proof of <== direction
    assert forall|v_addr| exists|thread_state| {
        &&& s.interp_thread_state(c).values().contains(thread_state)
        &&& s.interp_pt_mem().dom().contains(v_addr)
        &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
        &&& vaddr === v_addr
    } implies s.inflight_unmap_vaddr().contains(v_addr) by {
        let thread_state = choose|thread_state| {
            &&& s.interp_thread_state(c).values().contains(thread_state)
            &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, pte }
            &&& vaddr == v_addr
        };
        let ult_id = choose|id|
            #[trigger] s.interp_thread_state(c).dom().contains(id) && s.interp_thread_state(c)[id]
                === thread_state;
        assert(s.core_states.dom().contains(c.ult2core[ult_id]));
    };

}

proof fn lemma_effective_mappings_unaffected_if_thread_state_constant(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
)
    requires
        s1.inv_basic(c),
        s2.inv_basic(c),
        s1.interp_thread_state(c) === s2.interp_thread_state(c),
        s1.interp_pt_mem() === s2.interp_pt_mem(),
    ensures
        s1.effective_mappings() === s2.effective_mappings(),
{
    lemma_inflight_vaddr_equals_hl_unmap(c, s1);
    lemma_inflight_vaddr_equals_hl_unmap(c, s2);
    assert(s2.inflight_unmap_vaddr() =~= s1.inflight_unmap_vaddr());
}

///////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////
proof fn lemma_map_soundness_equality(
    c: os::Constants,
    s: os::State,
    vaddr: nat,
    pte: PTE,
)
    requires
        s.inv_basic(c),
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
            if !os::candidate_mapping_overlaps_inflight_pmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                pte,
            ) {
                let base = choose|b: nat|
                    #![auto]
                    {
                        &&& s.interp_pt_mem().dom().contains(b)
                        &&& overlap(pte.frame, s.interp_pt_mem().index(b).frame)
                    };
                if !s.inflight_unmap_vaddr().contains(base) {
                    assert(s.effective_mappings().dom().contains(base));
                } else {
                    let core = choose|core|
                        s.core_states.dom().contains(core) && match s.core_states[core] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
            }
        }
    }
}

proof fn lemma_unmap_soundness_equality(
    c: os::Constants,
    s: os::State,
    vaddr: nat,
    pte_size: nat,
)
    requires
        s.inv_basic(c),
    ensures
        hlspec::step_Unmap_sound(s.interp(c), vaddr, pte_size)
            <==> os::step_Unmap_sound(s, vaddr, pte_size),
{
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(c, s, vaddr, pte_size);
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(c, s, vaddr, pte_size);
}

proof fn lemma_os_overlap_vmem_implies_hl_or_inflight_overlap_vmem(
    c: os::Constants,
    s: os::State,
    vaddr: nat,
    pte: PTE,
)
    requires
        s.inv_basic(c),
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
            if !os::candidate_mapping_overlaps_inflight_vmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                vaddr,
                pte_size,
            ) {
                let base = choose|b: nat| #![auto] {
                        &&& s.interp_pt_mem().dom().contains(b)
                        &&& overlap(
                            MemRegion { base: vaddr, size: pte_size },
                            MemRegion { base: b, size: s.interp_pt_mem()[b].frame.size },
                        )
                    };
                if !s.inflight_unmap_vaddr().contains(base) {
                    assert(s.effective_mappings().dom().contains(base));
                } else {
                    let core = choose|core|
                        s.core_states.dom().contains(core) && match s.core_states[core] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Refinement proof
///////////////////////////////////////////////////////////////////////////////////////////////
proof fn os_init_refines_hl_init(c: os::Constants, s: os::State)
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
        assert(c.valid_core(core));
        assert(s.core_states[core] === os::CoreState::Idle);  //nn
    };
    assert(abs_s.mem === Map::empty());
    assert(abs_s.mappings === Map::empty());
}

proof fn os_next_refines_hl_next(c: os::Constants, s1: os::State, s2: os::State, lbl: RLbl)
    requires
        os::next(c, s1, s2, lbl),
        s1.inv(c),
    ensures
        hlspec::next(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let step = choose|step: os::Step| os::next_step(c, s1, s2, step, lbl);
    next_step_refines_hl_next_step(c, s1, s2, step, lbl);
}

proof fn next_step_refines_hl_next_step(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        os::next_step(c, s1, s2, step, lbl),
        s1.inv(c),
    ensures
        hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl),
{
    broadcast use to_rl1::next_refines;
    next_step_preserves_inv(c, s1, s2, step, lbl);
    match step {
        os::Step::MemOp { core, .. } => {
            step_MemOp_refines(c, s1, s2, core, lbl);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        // Map steps
        os::Step::MapStart { core } => {
            step_MapStart_refines(c, s1, s2, core, lbl);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapOpChange { core, paddr, value } => {
            if s1.sound {
                admit();
                //step_MapEnd_refines(c, s1, s2, core, paddr, value, result);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapNoOp { core } => {
            if s1.sound {
                admit();
                //step_MapEnd_refines(c, s1, s2, core, paddr, value, result);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapEnd { core } => {
            if s1.sound {
                step_MapEnd_refines(c, s1, s2, core, lbl);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        // Unmap steps
        os::Step::UnmapStart { core } => {
            if s1.sound {
                step_UnmapStart_refines(c, s1, s2, core, lbl);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapOpStart { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapOpChange { core, paddr, value, result } => {
            if s1.sound {
                step_UnmapOpChange_refines(c, s1, s2, core, paddr, value, result, lbl);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        }
        os::Step::UnmapOpEnd { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapEnd { core } => {
            step_UnmapEnd_refines(c, s1, s2, core, lbl);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        _ => assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl)),
    }
}

proof fn step_MemOp_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_MemOp(c, s1, s2, core, lbl),
    ensures
        ({
            let vaddr = lbl->MemOp_vaddr;
            let op = lbl->MemOp_op;
            let mlbl = mmu::Lbl::MemOp(core, vaddr as usize, op);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, step, mlbl);
            match mmu_step {
                rl1::Step::MemOpNoTr =>
                    hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), None, lbl),
                rl1::Step::MemOpNoTrNA { .. } =>
                    hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl),
                rl1::Step::MemOpTLB { tlb_va } =>
                    hlspec::step_MemOp(
                        c.interp(),
                        s1.interp(c),
                        s2.interp(c),
                        Some((tlb_va as nat, s1.effective_mappings()[tlb_va as nat])),
                        lbl
                    ),
                _ => arbitrary(),
            }
        }),
{
    broadcast use to_rl1::next_refines;
    let vaddr = lbl->MemOp_vaddr;
    let op = lbl->MemOp_op;
    let mlbl = mmu::Lbl::MemOp(core, vaddr as usize, op);
    let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, step, mlbl);
    match mmu_step {
        rl1::Step::MemOpNoTr { .. } => {
            admit();
            assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), None, lbl));
        },
        rl1::Step::MemOpNoTrNA { .. } => {
            // TODO: Needs an invariant about pending_maps
            admit();
            assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        rl1::Step::MemOpTLB { tlb_va } => {
            admit();
            let hl_pte = Some((tlb_va as nat, s1.effective_mappings()[tlb_va as nat]));
            assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), hl_pte, lbl));
        },
        _ => assert(false),
    };

}

proof fn step_MapStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv_basic(c),
        s2.inv_basic(c),
        os::step_MapStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_MapStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let ult_id = lbl->MapStart_thread_id;
    let vaddr = lbl->MapStart_vaddr;
    let pte = lbl->MapStart_pte;

    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    assert(hlspec::step_Map_enabled(s1.interp(c).thread_state.values(), s1.interp(c).mappings, vaddr, pte));
    assert(hl_c.valid_thread(ult_id));
    assert(s1.interp(c).thread_state[ult_id] === hlspec::ThreadState::Idle);
    let hl_map_sound = hlspec::step_Map_sound(
        s1.interp(c).mappings,
        s1.interp(c).thread_state.values(),
        vaddr,
        pte,
    );
    lemma_map_soundness_equality(c, s1, vaddr, pte);
    if hl_map_sound {
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

/*
proof fn step_MapOpEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, paddr: usize, value: usize, result: Result<(), ()>,  lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_MapOpEnd(c, s1, s2, core, paddr, value, result, lbl),
        s1.sound,
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c), lbl)
{
    broadcast use to_rl1::next_refines;
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    assert(hl_s2.sound);
    assume(hl_s2.mem === hl_s1.mem);
    assume(hl_s1.thread_state === hl_s2.thread_state);
    assume(hl_s2.mappings === hl_s1.mappings);
    admit();


    

    /*
    let ult_id = s1.core_states[core]->MapDone_ult_id;
    let vaddr = s1.core_states[core]->MapDone_vaddr;
    let pte = s1.core_states[core]->MapDone_pte;
    let result = s1.core_states[core]->MapDone_result;

    assert(hlspec::valid_thread(hl_c, ult_id));
    assert(s1.interp(c).thread_state[ult_id] is Map);

    if candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte) {
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
            if core_of_key === core {
            } else {
                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            }
        }
        assert(hl_s2.thread_state === hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Idle));
        assert(s1.core_states[core] is MapDone);

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
            let threadstate = choose|thread_state| {
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
        if !hlspec::candidate_mapping_overlaps_inflight_vmem(
            s1.interp(c).thread_state.values(),
            vaddr,
            pte.frame.size,
        ) {
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

        } else { // contradiction
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
            if !candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte) {
                assert forall|key| #[trigger]
                    hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
                    ult_id,
                    hlspec::ThreadState::Idle,
                )[key] == hl_s2.thread_state[key] by {
                    let core_of_key = c.ult2core[key];
                    if core_of_key === core {
                    } else {
                        assert(c.valid_core(core_of_key));
                        assert(!s1.core_states[core_of_key].is_in_crit_sect());
                        if s1.core_states[core_of_key] is UnmapWaiting {
                            assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
                            assert(s1.core_states[c.ult2core[key]]
                                === s2.core_states[c.ult2core[key]]);
                            let Unmap_vaddr = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                            if vaddr == Unmap_vaddr {
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
                assert(hl_s2.thread_state === hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Idle));
                //assert(!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
                assert(result is Ok);
                assert(s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte));
                assert(!s1.inflight_unmap_vaddr().contains(vaddr));
                assert forall|idx|
                    s1.inflight_unmap_vaddr().contains(
                        idx,
                    ) implies s2.inflight_unmap_vaddr().contains(idx) by {
                    if s1.inflight_unmap_vaddr().contains(idx) {
                        assert(s1.interp_pt_mem().dom().contains(idx));
                        let unmap_core = choose|unmap_core|
                            s1.core_states.dom().contains(unmap_core)
                                && match s1.core_states[unmap_core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === idx
                                },
                                _ => false,
                            };
                        if unmap_core != core {
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
                    if s2.inflight_unmap_vaddr().contains(idx) {
                        assert(s2.interp_pt_mem().dom().contains(idx));

                        let unmap_core = choose|unmap_core|
                            s2.core_states.dom().contains(unmap_core)
                                && match s1.core_states[unmap_core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === idx
                                },
                                _ => false,
                            };
                        if idx != vaddr {
                            if unmap_core != core {
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
                assert(forall|idx| #![auto]
                    hl_s2.mappings.contains_key(idx) ==> hl_s1.mappings.insert(vaddr, pte).contains_key(idx));
                assert(hl_s2.mappings =~= hl_s1.mappings.insert(vaddr, pte));
                lemma_mem_domain_from_mappings(c.interp().phys_mem_size, hl_s1.mappings, vaddr, pte);
                assert forall|idx: nat| #![auto]
                    hl_s1.mem.dom().contains(idx) implies hl_s2.mem[idx] === hl_s1.mem[idx] by {
                    // TODO overlapping mapped vmem
                    if hl_s1.mem.dom().contains(idx) {
                        assert(hlspec::mem_domain_from_mappings_contains(
                            hl_c.phys_mem_size,
                            idx,
                            hl_s1.mappings,
                        ));
                        assert(hl_s2.mem.dom().contains(idx));
                        let vidx = (idx * WORD_SIZE as nat);
                        let (mem_base, mem_pte): (nat, PTE) = choose|base: nat, pte: PTE| {
                            &&& #[trigger] hl_s1.mappings.contains_pair(base, pte)
                            &&& hlspec::mem_domain_from_entry_contains(hl_c.phys_mem_size, vidx, base, pte)
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
                            if hl_s2.mappings.contains_pair(page, entry) && between(
                                vidx,
                                page,
                                page + entry.frame.size,
                            ) {
                                assert(overlap(
                                    MemRegion { base: page, size: entry.frame.size },
                                    MemRegion { base: mem_base, size: mem_pte.frame.size },
                                ));
                                assert(s2.interp_pt_mem().dom().contains(page));
                                assert(s2.interp_pt_mem().dom().contains(mem_base));
                                if s2.interp_pt_mem().remove(page).dom().contains(mem_base) {
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
                let os_overlap_vaddr = choose|b: nat| #![auto] {
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
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === os_overlap_vaddr
                        },
                        _ => false,
                    };
                assert(!s1.core_states[unmap_core].is_in_crit_sect());
                assert(s1.core_states[unmap_core] is UnmapWaiting);
                assert(overlap(
                    MemRegion { base: vaddr, size: pte.frame.size },
                    MemRegion {
                        base: s1.core_states[unmap_core]->UnmapWaiting_vaddr,
                        size:
                            s1.interp_pt_mem()[s1.core_states[unmap_core]->UnmapWaiting_vaddr].frame.size,
                    },
                ));
                assert(c.valid_core(core) && c.valid_core(unmap_core)
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
            assert(false);
        }
    }
*/
}
*/


proof fn step_MapEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_MapEnd(c, s1, s2, core, lbl),
        s1.sound,
    ensures 
        hlspec::step_MapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl)
{
    //interpretation
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    //label
    let vaddr = lbl->UnmapEnd_vaddr;
    let thread_id = lbl->UnmapEnd_thread_id;
    let result = lbl->UnmapEnd_result;
    //core_state
    let ult_id = s1.core_states[core]->MapDone_ult_id;
    let vaddr = s1.core_states[core]->MapDone_vaddr;
    let pte = s1.core_states[core]->MapDone_pte;
    let result = s1.core_states[core]->MapDone_result;


    assert(hl_c.valid_thread(ult_id));
    assert(hl_s2.sound == hl_s1.sound);
    assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Idle,
    ));
    assert(s1.interp(c).thread_state[ult_id] is Map);
    
    
    if (candidate_mapping_overlaps_existing_vmem(hl_s1.mappings, vaddr, pte) ){


        assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
        assume(result is Err);
        assume(hl_s2.mappings === hl_s1.mappings);
        assert(hl_s2.mem === hl_s1.mem);
   
//        assert(s1.interp_pt_mem() == s2.interp_pt_mem());
//
//        lemma_map_insert_values_equality(s1.core_states, core, os::CoreState::Idle);
//        assert(s1.core_states.values().insert(os::CoreState::Idle)
//            =~= s2.core_states.values().insert(s1.core_states[core]));
//
//        assert forall|key| #[trigger]
//            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
//            ult_id,
//            hlspec::ThreadState::Idle,
//        )[key] == hl_s2.thread_state[key] by {
//            let core_of_key = c.ult2core[key];
//            if core_of_key === core {
//            } else {
//                assert(s1.core_states[core_of_key] == s2.core_states[core_of_key]);
//                assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
//            }
//        }
//        assert(hl_s2.thread_state === hl_s1.thread_state.insert(ult_id, hlspec::ThreadState::Idle));
//        assert(s1.core_states[core] is MapDone);
//
//        lemma_map_insert_values_equality(
//            hl_s1.thread_state,
//            ult_id,
//            hlspec::ThreadState::Idle,
//        );
//        assert(hl_s1.thread_state.values().insert(hlspec::ThreadState::Idle)
//            =~= hl_s2.thread_state.values().insert(hl_s1.thread_state[ult_id]));
//        lemma_inflight_vaddr_equals_hl_unmap(c, s1);
//        lemma_inflight_vaddr_equals_hl_unmap(c, s2);
//        assert forall|base|
//            s1.inflight_unmap_vaddr().contains(base) implies s2.inflight_unmap_vaddr().contains(
//            base,
//        ) by {
//            let threadstate = choose|thread_state| {
//                    &&& s1.interp_thread_state(c).values().contains(thread_state)
//                    &&& s1.interp_pt_mem().dom().contains(base)
//                    &&& thread_state matches hlspec::ThreadState::Unmap { vaddr, .. }
//                    &&& vaddr === base
//                };
//            assert(!(hl_s1.thread_state[ult_id] is Unmap));
//            assert(hl_s1.thread_state.values().insert(hlspec::ThreadState::Idle).contains(
//                threadstate,
//            ));
//            assert(hl_s2.thread_state.values().contains(threadstate));
//        }
//        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());      
    } else {
        assume(result is Ok);
        assume(hl_s2.mappings === hl_s1.mappings.insert(vaddr, pte));
        assume((forall|idx: nat| #![auto] hl_s1.mem.contains_key(idx) ==> hl_s2.mem[idx] === hl_s1.mem[idx]));
        assert(hl_s2.mem.dom() === crate::spec_t::hlspec::mem_domain_from_mappings(hl_c.phys_mem_size, hl_s2.mappings));
    }
}

proof fn step_UnmapStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let vaddr = lbl->UnmapStart_vaddr;
    let ult_id = lbl->UnmapStart_thread_id;
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    let pte = if hl_s1.mappings.dom().contains(vaddr) { Some(hl_s1.mappings[vaddr]) } else { Option::None };
    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };
    assert(hlspec::step_Unmap_enabled(vaddr));
    assert(hl_c.valid_thread(ult_id));
    assert(hl_s1.thread_state[ult_id] === hlspec::ThreadState::Idle);

    lemma_unmap_soundness_equality(c, s1, vaddr, pte_size);
    if hlspec::step_Unmap_sound(hl_s1, vaddr, pte_size) {
        // TODO(MB): This broke when I fixed a bug in step_UnmapStart.
        // It previously said: s2.sound == s1.sound && step_Unmap_sound(..)
        // I changed it to:    s2.sound == (s1.sound && step_Unmap_sound(..))
        assume(hl_s1.sound == hl_s2.sound);
        assert forall|key| #[trigger]
            hl_s1.thread_state.dom().contains(key) implies hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Unmap { vaddr, pte },
        )[key] == hl_s2.thread_state[key] by {
            let core_of_key = c.ult2core[key];
            if core_of_key === core {
                if key == ult_id {
                    assert(s2.core_states == s1.core_states.insert(
                        core,
                        os::CoreState::UnmapWaiting { ult_id, vaddr },
                    ));
                    assert(s2.core_states[core] is UnmapWaiting);
                    let thread_pte = hl_s2.thread_state[ult_id]->Unmap_pte;
                    if s1.interp_pt_mem().dom().contains(vaddr)
                        && s1.inflight_unmap_vaddr().contains(vaddr) {
                        let overlap_core = choose|core|
                            s1.core_states.dom().contains(core) && match s1.core_states[core] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr: v }
                                | os::CoreState::UnmapExecuting { ult_id, vaddr: v, .. }
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
        assert(c.valid_core(c.ult2core[ult_id]));
        // unstable
        // jp: unstable indeed
        assume(hl_s2.thread_state =~= hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Unmap { vaddr, pte },
        ));
        if pte is None {
            assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
            assert forall|ids|
                s1.inflight_unmap_vaddr().contains(ids) implies s2.inflight_unmap_vaddr().contains(
                ids,
            ) by {
                if s1.inflight_unmap_vaddr().contains(ids) {
                    let unmap_core = choose|cr|
                        s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
                    if ids === vaddr {
                    } else {
                        let unmap_core = choose|cr|
                            s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                                os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
                if hl_s2.mem.dom().contains(idx) {
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
                        if s1.interp_pt_mem().remove(page).dom().contains(mem_base) {
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
    }
}

proof fn step_UnmapOpChange_refines(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    core: Core,
    paddr: usize,
    value: usize,
    result: Result<PTE, ()>,
    lbl: RLbl,
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapOpChange(c, s1, s2, core, paddr, value, result, lbl),
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    broadcast use to_rl1::next_refines;
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    assert(s1.core_states[core] is UnmapExecuting);
    let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;

    assert(hl_s1.thread_state.dom() === hl_s2.thread_state.dom());
    assert forall|key| #[trigger]
        hl_s1.thread_state.contains_key(key) implies hl_s1.thread_state[key] == hl_s2.thread_state[key] by {
        assert(c.valid_ult(key));
        assert(hl_s2.thread_state.dom().contains(key));
        let core_of_key = c.ult2core[key];
        assert(c.valid_core(core));
        assert(s1.core_states[core].is_in_crit_sect());
        assert(c.valid_core(core_of_key));
        if s1.core_states[core_of_key].is_in_crit_sect() {
            assert(core_of_key === core);
        } else {
            assert(!(core_of_key === core));
            assert(!s1.core_states[core_of_key].is_in_crit_sect());
            assert(s1.core_states.index(core_of_key) == s2.core_states.index(core_of_key));
            assert(s1.core_states[c.ult2core[key]] === s2.core_states[c.ult2core[key]]);
            if s1.core_states.index(core_of_key) is UnmapWaiting {
                let vaddr_of_key = s1.core_states[core_of_key]->UnmapWaiting_vaddr;
                if vaddr_of_key == vaddr {
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
                }
            } 
        }
    }
    assert(hl_s1.thread_state =~= hl_s2.thread_state);
    assert(s1.interp_pt_mem().remove(vaddr) =~= s2.interp_pt_mem());
    if s1.interp_pt_mem().dom().contains(vaddr) {
        assert(s1.core_states.dom().contains(core));
        assert(s1.inflight_unmap_vaddr().contains(vaddr));
        assert forall|ids|
            s1.inflight_unmap_vaddr().contains(
                ids,
            ) implies #[trigger] s2.inflight_unmap_vaddr().insert(vaddr).contains(ids) by {
            if s1.inflight_unmap_vaddr().contains(ids) {
                if ids === vaddr {
                } else {
                    assert(s1.interp_pt_mem().dom().contains(ids));
                    assert(s2.interp_pt_mem().dom().contains(ids));
                    let unmap_core = choose|cr|
                        s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                            os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
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
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
    }
    assert(s1.effective_mappings() =~= s2.effective_mappings())
}

proof fn step_UnmapEnd_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        os::step_UnmapEnd(c, s1, s2, core, lbl),
    ensures
        s1.core_states[core] is UnmapOpDone || s1.core_states[core] is UnmapShootdownWaiting,
        hlspec::step_UnmapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);
    match s1.core_states[core] {
        os::CoreState::UnmapShootdownWaiting { ult_id, result, vaddr, .. }
        | os::CoreState::UnmapOpDone { result, ult_id, vaddr, .. } => {
            assert(hl_c.valid_thread(ult_id));
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
