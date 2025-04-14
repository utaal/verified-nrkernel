#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    x86_arch_spec_upper_bound,
    candidate_mapping_in_bounds,
    candidate_mapping_overlaps_existing_pmem,
    candidate_mapping_overlaps_existing_vmem, overlap,
    MAX_BASE, MemRegion, PTE, Core
};
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::mmu::{ self, rl1 };
#[cfg(verus_keep_ghost)]
use crate::spec_t::os_invariant::{
    lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl,
    lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os,
    lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl, next_step_preserves_inv,
    lemma_map_insert_values_equality, lemma_map_insert_value,
    lemma_init_implies_empty_map,
};
use crate::spec_t::{hlspec, os};
use crate::theorem::RLbl;
use crate::spec_t::mmu::defs::MemOp;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{between, update_range};
use crate::spec_t::mmu::pt_mem::PTMem;
use crate::spec_t::os::CoreState;

verus! {


///////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata
///////////////////////////////////////////////////////////////////////////////////////////////

proof fn lemma_inflight_unmap_vaddr_equals_hl_unmap(c: os::Constants, s: os::State)
    requires s.inv_basic(c),
    ensures
        forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr)
            <==> exists|thread_state| {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().dom().contains(v_addr)
                &&& (thread_state matches hlspec::ThreadState::Unmap { vaddr, .. } && vaddr === v_addr)
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


proof fn lemma_inflight_vaddr_implies_hl_unmap_or_map(c: os::Constants, s: os::State)
    requires s.inv_basic(c),
    ensures
        forall|v_addr| s.inflight_unmap_vaddr().contains(v_addr)
            ==> exists|thread_state| {
                &&& s.interp_thread_state(c).values().contains(thread_state)
                &&& s.interp_pt_mem().dom().contains(v_addr)
                &&& ((thread_state matches hlspec::ThreadState::Unmap { vaddr, .. } && vaddr === v_addr)
                    || (thread_state matches hlspec::ThreadState::Map { vaddr, .. } && vaddr === v_addr))
            },
{
    if (!(s.inflight_vaddr() =~= Set::empty()) && s.inflight_unmap_vaddr() =~= Set::empty()) {
        let v_address = s.inflight_vaddr().choose();
        assert(s.interp_pt_mem().contains_key(v_address));
        let map_core = choose|core| s.core_states.contains_key(core) && match s.core_states[core] {
            os::CoreState::UnmapWaiting { ult_id, vaddr }
            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
            | os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                vaddr === v_address
            },
            _ => false,
        };
        if (s.core_states[map_core] is MapDone) {
        let ult_id = s.core_states[map_core]->MapDone_ult_id;
        assert(s.interp_thread_state(c).dom().contains(ult_id));
        let thread_state = s.interp_thread_state(c)[ult_id];
        assert(thread_state is Map);
        assert(s.interp_thread_state(c).values().contains(thread_state));
        } else {
            assert(s.inflight_unmap_vaddr().contains(v_address));
            assert(false);
        }
    } else {
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s);
    }
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
        os::next(c, s1, s2, RLbl::Tau),
    ensures
        s1.effective_mappings() === s2.effective_mappings(),
{
    lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
    lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
    let step = choose|step| os::next_step(c, s1, s2, step, RLbl::Tau);
    if (s1.inflight_unmap_vaddr() =~= s1.inflight_vaddr()) {
        assert(s2.inflight_unmap_vaddr() =~= s2.inflight_vaddr()) by {
            if (!(s2.inflight_unmap_vaddr() =~= s2.inflight_vaddr())){
                let map_vaddr = choose|v| s2.inflight_vaddr().contains(v) && !s2.inflight_unmap_vaddr().contains(v);
                let map_core = choose |core| s2.core_states.dom().contains(core) && s2.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:map_vaddr, result: Ok(()), .. };
                assert(!s2.effective_mappings().contains_key(map_vaddr));
                assert(s2.interp_pt_mem().contains_key(map_vaddr));
            }
        }
        assert(s2.inflight_vaddr() =~= s1.inflight_vaddr());
    } else {
        let map_vaddr = choose|v| s1.inflight_vaddr().contains(v) && !s1.inflight_unmap_vaddr().contains(v);
        let map_core = choose |core| s1.core_states.dom().contains(core) && s1.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:map_vaddr, result: Ok(()), .. };
        assert(!s1.effective_mappings().contains_key(map_vaddr));
        assert(s1.core_states[map_core] == s2.core_states[map_core]);
        assert(s2.inflight_vaddr().contains(map_vaddr) && !s2.inflight_unmap_vaddr().contains(map_vaddr));
        assert(s2.inflight_vaddr() =~= s1.inflight_vaddr());
    }
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
        if  (candidate_mapping_overlaps_existing_pmem(s.interp_pt_mem(), pte)) {
            // canditate pte overlaps with base's pte
            let base = choose|b: nat|
                    #![auto]
                    {
                        &&& s.interp_pt_mem().dom().contains(b)
                        &&& overlap(pte.frame, s.interp_pt_mem().index(b).frame)
                    };
            let overlap_pte = s.interp_pt_mem()[base];
            if !os::candidate_mapping_overlaps_inflight_pmem(
                s.interp_pt_mem(),
                s.core_states.values(),
                pte,
            ) {
                if !s.inflight_vaddr().contains(base) {
                    assert(s.effective_mappings().dom().contains(base));
                } else {
                    let critical_core = choose|core|
                        s.core_states.dom().contains(core) && match s.core_states[core] {
                            os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. }
                            | os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === base
                            },
                            _ => false,
                        };
                    assert(s.core_states.values().contains(s.core_states.index(critical_core)));
                    if (s.core_states[critical_core] is MapDone) {
                        let critical_ult_id = s.core_states[critical_core]->MapDone_ult_id;
                        let b = hlspec::ThreadState::Map { vaddr: base, pte: overlap_pte };
                        assert ( s.interp(c).thread_state.values().contains(b) && match b {
                            hlspec::ThreadState::Map { vaddr: base, pte: overlap_pte } => overlap(pte.frame, overlap_pte.frame),
                            _ => { false },
                        });
                        assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
                            s.interp(c).thread_state.values(),
                            pte,
                        ));
                    } else {
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
    //assert(abs_s.mem === Map::empty());
    assert(abs_s.mappings =~= Map::empty()) by {
        lemma_init_implies_empty_map(s, c);
    };
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
            if s1.sound {
                step_MemOp_refines(c, s1, s2, core, lbl);
                assume(false); // step_MemOp_refines ensures doesn't match Step::interp
            }
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
            extra_mappings_preserved(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapOpChange { core, paddr, value } => {
            if s1.sound {
                step_MapOpChange_refines(c, s1, s2, core, paddr, value, lbl);
                //step_MapEnd_refines(c, s1, s2, core, paddr, value, result);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::MapNoOp { core } => {
            if s1.sound {
                assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
                lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
                extra_mappings_preserved_for_overlap_map(c, s1, s2, core);
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
            extra_mappings_preserved(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapOpChange { core, paddr, value } => {
            if s1.sound {
                step_UnmapOpChange_refines(c, s1, s2, core, paddr, value, lbl);
            }
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        }
        os::Step::UnmapOpFail { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            extra_mappings_preserved(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s1.interp(c).thread_state =~= s2.interp(c).thread_state);
            lemma_effective_mappings_unaffected_if_thread_state_constant(c, s1, s2);
            extra_mappings_preserved(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        os::Step::UnmapEnd { core } => {
            step_UnmapEnd_refines(c, s1, s2, core, lbl);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        },
        _ => {
            extra_mappings_preserved(c, s1, s2);
            assert(hlspec::next_step(c.interp(), s1.interp(c), s2.interp(c), step.interp(s1, s2, c, lbl), lbl));
        }
    }
}

use crate::spec_t::hlspec::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::aligned;
proof fn step_MemOp_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_MemOp(c, s1, s2, core, lbl),
        s1.sound,
    ensures
        ({
            let vaddr = lbl->MemOp_vaddr;
            let op = lbl->MemOp_op;
            let mlbl = mmu::Lbl::MemOp(core, vaddr as usize, op);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mlbl);
            match mmu_step {
                rl1::Step::MemOpNoTr =>
                    hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), None, lbl),
                rl1::Step::MemOpNoTrNA { .. } =>
                    hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl),
                rl1::Step::MemOpTLB { tlb_va } =>
                    if s1.effective_mappings().dom().contains(tlb_va as nat) {
                        hlspec::step_MemOp(
                            c.interp(),
                            s1.interp(c),
                            s2.interp(c),
                            Some((tlb_va as nat, s1.effective_mappings()[tlb_va as nat])),
                            lbl
                        )
                    } else {
                        hlspec::step_MemOpNA(
                            c.interp(),
                            s1.interp(c),
                            s2.interp(c),
                            lbl
                        )
                    }
                _ => arbitrary(),
            }
        }),
{
    broadcast use to_rl1::next_refines;
    let vaddr = lbl->MemOp_vaddr;
    let op = lbl->MemOp_op;
    let mlbl = mmu::Lbl::MemOp(core, vaddr as usize, op);
    let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.common, step, mlbl);
    assert(rl1::next_step(s1.mmu@, s2.mmu@, c.common, mmu_step, mlbl));

    extra_mappings_preserved(c, s1, s2);

    match mmu_step {
        rl1::Step::MemOpNoTr { .. } => {
            assert(rl1::step_MemOpNoTr(s1.mmu@, s2.mmu@, c.common, mlbl));
            let t1 = s1.interp(c);
            let t2 = s2.interp(c);
            let d = c.interp();
            assert(lbl is MemOp);
            let thread_id = lbl->MemOp_thread_id;
            assert(t2.mem === t1.mem);
            assert(t2.mappings === t1.mappings);
            assert(t2.thread_state === t1.thread_state);
            assert(t2.sound == t1.sound);
            assert(op.is_pagefault());
            assert(aligned(vaddr, 8));
            assert(d.valid_thread(thread_id));
            assert(t1.thread_state.dom().contains(thread_id));
            assert(t1.thread_state[thread_id] is Idle);
            assert(!is_in_mapped_region(c.common.phys_mem_size, t1.mappings, vaddr)) by {
                reveal(PTMem::view);
                assert forall|base: nat, pte: PTE|
                  #[trigger] t1.mappings.contains_pair(base, pte)
                   && between(vaddr, base, base + pte.frame.size)
                   && pte.frame.base + (vaddr - base) < c.common.phys_mem_size
                   implies false
                by {
                    assert(s1.interp_pt_mem().dom().contains(base));
                    reveal(PTMem::view);
                    assert(s1.mmu@.pt_mem.pt_walk(base as usize).result() is Valid);
                    assert(s1.mmu@.pt_mem.pt_walk(vaddr as usize).result() is Invalid);
                    s1.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(base as usize, vaddr as usize);
                    assert(false);
                }
            }
            assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), None, lbl));
        },
        rl1::Step::MemOpNoTrNA { vbase } => {
            let t1 = s1.interp(c);
            let t2 = s2.interp(c);
            let d = c.interp();
            let thread_id = lbl->MemOp_thread_id;
            let op = lbl->MemOp_op;

            let pte = t1.vaddr_mapping_is_being_modified_choose(d, vaddr);

            let core = choose |core| os::State::is_pending_for_core(c, vbase, core, s1.core_states, s1.mmu@.pending_maps);
            assert(os::State::is_pending_for_core(c, vbase, core, s1.core_states, s1.mmu@.pending_maps));

            let thread1 = s1.core_states[core]->MapDone_ult_id;
            assert(d.valid_thread(thread1));
            assert(match t1.thread_state[thread1] {
                ThreadState::Map { vaddr: vaddr1, pte } => between(vaddr, vaddr1, vaddr1 + pte.frame.size),
                _ => false,
            });

            let thread = t1.vaddr_mapping_is_being_modified_choose_thread(d, vaddr);

            assert(match t1.thread_state[thread] {
                ThreadState::Map { vaddr: vaddr1, pte } => between(vaddr, vaddr1, vaddr1 + pte.frame.size),
                ThreadState::Unmap { vaddr: vaddr1, pte: Some(pte) } => between(vaddr, vaddr1, vaddr1 + pte.frame.size),
                _ => false,
            });

            assert(thread == thread1) by {
                let core1 = c.ult2core[thread1];
                let core2 = c.ult2core[thread];
                assert(s1.inv_inflight_map_no_overlap_inflight_vmem(c));
                let mr1 = MemRegion {
                        base: s1.core_states[core1].vaddr(),
                        size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                    };
                let mr2 = MemRegion {
                        base: s1.core_states[core2].vaddr(),
                        size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                    };
                assert(between(vaddr, mr1.base, mr1.base + mr1.size));
                assert(between(vaddr, mr2.base, mr2.base + mr2.size));
                assert(overlap(mr1, mr2));
                assert(core1 == core2);
                assert(thread1 == thread);
            }

            assert(t1.vaddr_mapping_is_being_modified(d, vaddr));
            assert(t1.thread_state[thread] is Map);

            assert(pte.is_none());

            assert(aligned(vaddr, 8));
            assert(d.valid_thread(thread_id));
            assert(t1.thread_state[thread_id] is Idle);
            assert(t2.mappings === t1.mappings);
            assert(t2.thread_state === t1.thread_state);
            assert(t2.sound == t1.sound);
            assert(t2.mem == t1.mem);
            assert(op.is_pagefault());

            assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        rl1::Step::MemOpTLB { tlb_va } => {
            assume(s1.tlb_inv(c));
            assert(s1.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
            assert(c.valid_core(core));

            assert(s1.mmu@.tlbs[core].dom().contains(tlb_va));
            assert(s1.interp_pt_mem().dom().union(s1.unmap_vaddr_set()).contains(tlb_va as nat));
            unmap_vaddr_set_le_extra_mappings_dom(c, s1);
            assert(s1.applied_mappings().dom().contains(tlb_va as nat));
            assume(s1.applied_mappings()[tlb_va as nat] == s1.mmu@.tlbs[core][tlb_va]); // needs invariant

            let hl_pte = Some((tlb_va as nat, s1.applied_mappings()[tlb_va as nat]));

            let t1 = s1.interp(c);
            let t2 = s2.interp(c);
            let d = c.interp();
            let thread_id = lbl->MemOp_thread_id;

            assert(d.valid_thread(thread_id));
            assert(t1.thread_state[thread_id] is Idle);
            assert(aligned(vaddr, op.op_size()));
            assert(op.valid_op_size());

            assert(t2.mappings === t1.mappings);
            assert(t2.thread_state === t1.thread_state);
            assert(t2.sound == t1.sound);

            let base = tlb_va as nat;
            let pte = s1.applied_mappings()[tlb_va as nat];

            assert(pte == s1.mmu@.tlbs[core][tlb_va]);
            //assert(s1.mmu@.pt_mem.is_base_pt_walk(tlb_va));

            let paddr = pte.frame.base + (vaddr - base);
            assert(base <= vaddr);
            assert(vaddr < base + pte.frame.size);
            assert(between(vaddr, base, base + pte.frame.size));

            no_overlaps_applied_mappings(c, s1);

            assume(vaddr as int + op.op_size() as int <= base + pte.frame.size);
            assume(base + pte.frame.size <= s1.interp_vmem(c).len());
            assume(pte.frame.base + pte.frame.size <= s1.mmu@.phys_mem.len());

            match op {
                MemOp::Store { new_value, result } => {
                    if paddr < d.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        assert(result is Ok);
                        interp_vmem_update_range(c, s1, base, pte, vaddr as int, op.op_size() as int, new_value);
                        assert(t2.mem === update_range(t1.mem, vaddr as int, new_value));
                    } else {
                        assert(result is Pagefault);
                        assert(t2.mem === t1.mem);
                    }
                },
                MemOp::Load { is_exec, result, .. } => {
                    assert(t2.mem === t1.mem);
                    if paddr < d.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        assert(result is Value);
                        interp_vmem_subrange(c, s1, base, pte, vaddr as int, op.op_size() as int);
                        assert(result->0 == t1.mem.subrange(vaddr as int, vaddr + op.op_size() as int));
                    } else {
                        assert(result is Pagefault);
                    }
                }
            }

            if s1.effective_mappings().dom().contains(tlb_va as nat) {
                assert(t1.mappings.contains_pair(base, pte));
                assert(hlspec::step_MemOp(c.interp(), s1.interp(c), s2.interp(c), hl_pte, lbl));
            } else {
                assert(s1.extra_mappings().dom().contains(tlb_va as nat)
                    || s1.inflight_vaddr().contains(tlb_va as nat));
                assert(c.valid_core(core));
                assert(s1.mmu@.tlbs[core].dom().contains(tlb_va));
                assert(between(vaddr, tlb_va as nat, tlb_va as nat + s1.mmu@.tlbs[core][tlb_va].frame.size));
                vaddr_mapping_is_being_modified_from_vaddr_unmap(c, s1, core, tlb_va, vaddr);
                assert(t1.vaddr_mapping_is_being_modified(d, vaddr));
                assert(Some((base, pte)) == t1.vaddr_mapping_is_being_modified_choose(d, vaddr));
                assert(hlspec::step_MemOpNA(c.interp(), s1.interp(c), s2.interp(c), lbl));
            }
        },
        _ => assert(false),
    };
}

proof fn vaddr_distinct(c: os::Constants, s: os::State)
    requires s.inv(c), s.sound,
    ensures 
        forall |core1, core2| #![all_triggers]
            s.core_states.dom().contains(core1) && s.core_states.dom().contains(core2)
            && !s.core_states[core1].is_idle() && !s.core_states[core2].is_idle()
            && s.core_states[core1].vaddr() == s.core_states[core2].vaddr() ==> core1 == core2
{
    assert forall |core1, core2| #![all_triggers]
        s.core_states.dom().contains(core1) && s.core_states.dom().contains(core2)
        && !s.core_states[core1].is_idle() && !s.core_states[core2].is_idle()
        && s.core_states[core1].vaddr() == s.core_states[core2].vaddr() implies core1 == core2
    by {
        let mr1 = MemRegion {
            base: s.core_states[core1].vaddr(),
            size: s.core_states[core1].pte_size(s.interp_pt_mem()),
        };
        let mr2 = MemRegion {
            base: s.core_states[core2].vaddr(),
            size: s.core_states[core2].pte_size(s.interp_pt_mem()),
        };
        assert(overlap(mr1, mr2));
    }
}

proof fn unmap_vaddr_set_le_extra_mappings_dom(c: os::Constants, s: os::State)
    requires s.inv(c), s.sound,
    ensures s.unmap_vaddr_set() <= s.extra_mappings().dom()
{
    assert forall |vaddr| #![all_triggers] s.unmap_vaddr_set().contains(vaddr)
        implies s.extra_mappings().dom().contains(vaddr)
    by {
        vaddr_distinct(c, s);
        reveal(os::State::extra_mappings);
        let core = choose |core: Core| s.is_unmap_vaddr_core(core, vaddr);
        assert(s.is_extra_vaddr_core(core, vaddr));
        assert(s.is_extra_vaddr(vaddr));
        assert(!s.candidate_vaddr_overlaps(vaddr));
    }
}

proof fn extra_mappings_preserved(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
)
    requires
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
            
        s1.effective_mappings() == s2.effective_mappings(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    hide(candidate_mapping_overlaps_existing_vmem);

    assume(s1.inv(c)); assume(s1.sound);
    assume(s2.inv(c)); assume(s2.sound);
    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if s1.extra_mappings().dom().contains(vaddr) {
            let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
            assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
            assert(s1.get_extra_vaddr_core(vaddr) == core);
            assert(s2.get_extra_vaddr_core(vaddr) == core);
            assert(s2.is_extra_vaddr(vaddr));
            assert(!s1.candidate_vaddr_overlaps(vaddr));
            assert(!s2.candidate_vaddr_overlaps(vaddr));
            assert(s2.extra_mappings().dom().contains(vaddr));
        }
        if s2.extra_mappings().dom().contains(vaddr) {
            assert(s1.extra_mappings().dom().contains(vaddr));
        }
    });
}

proof fn extra_mappings_preserved_effective_mapping_inserted(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
            
        s1.core_states.dom().contains(this_core),
        match s1.core_states[this_core] {
            CoreState::MapDone { ult_id, vaddr, pte, result: Ok(_) } => {
                !s1.effective_mappings().dom().contains(vaddr)
                && s2.effective_mappings() =~= s1.effective_mappings().insert(vaddr, pte)
            }
            _ => false,
        }
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let this_vaddr = s1.core_states[this_core]->MapDone_vaddr;
    let this_pte = s1.core_states[this_core]->MapDone_pte;

    assume(s1.inv(c)); assume(s1.sound);
    assume(s2.inv(c)); assume(s2.sound);
    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().dom().contains(vaddr) {
                assert(s2.extra_mappings().dom().contains(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                assert(s1.extra_mappings().dom().contains(vaddr));
            }
        } else {
            if s1.extra_mappings().dom().contains(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));

                match s2.core_states[s2.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        let mappings = s2.effective_mappings();
                        assert(vaddr1 == vaddr);

                        let core1 = this_core;
                        let core2 = s2.get_extra_vaddr_core(vaddr);
                        let mr1 = MemRegion {
                            base: s1.core_states[core1].vaddr(),
                            size: s1.core_states[core1].pte_size(s1.interp_pt_mem()),
                        };
                        let mr2 = MemRegion {
                            base: s1.core_states[core2].vaddr(),
                            size: s1.core_states[core2].pte_size(s1.interp_pt_mem()),
                        };
                        assert(!overlap(mr1, mr2));
                        assert(!overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size },
                        ));
                    }
                    _ => { }
                }

                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().dom().contains(vaddr));
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                let core = choose |core: Core| s2.is_extra_vaddr_core(core, vaddr);

                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s1.is_extra_vaddr(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));

                match s1.core_states[s1.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        monotonic_candidate_mapping_overlaps_existing_vmem(
                            s1.effective_mappings(),
                            s2.effective_mappings(),
                            vaddr,
                            pte);
                    }
                    _ => { }
                }

                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(s1.extra_mappings().dom().contains(vaddr));
            }
        }
    });
}

proof fn monotonic_candidate_mapping_overlaps_existing_vmem(
    mappings1: Map<nat, PTE>,
    mappings2: Map<nat, PTE>,
    base: nat,
    pte: PTE,
)
    requires mappings1.submap_of(mappings2)
    ensures
        candidate_mapping_overlaps_existing_vmem(mappings1, base, pte)
        ==> candidate_mapping_overlaps_existing_vmem(mappings2, base, pte)
{
    assert(forall |b| #[trigger] mappings1.contains_key(b) ==> mappings2.contains_key(b));
}

proof fn extra_mappings_preserved_effective_mapping_removed(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s1.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        forall |core: Core|
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }),
            
        s2.core_states.dom().contains(this_core),
        match s2.core_states[this_core] {
            CoreState::UnmapWaiting { ult_id, vaddr } => {
                s1.effective_mappings().dom().contains(vaddr)
                && s2.effective_mappings() =~= s1.effective_mappings().remove(vaddr)
                && s1.interp_pt_mem().dom().contains(vaddr)
            }
            _ => false,
        },
        s1.interp_pt_mem() =~= s2.interp_pt_mem(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let this_vaddr = s2.core_states[this_core]->UnmapWaiting_vaddr;

    assume(s1.inv(c)); assume(s1.sound);
    assume(s2.inv(c)); assume(s2.sound);
    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            if s1.extra_mappings().dom().contains(vaddr) {
                assert(s2.extra_mappings().dom().contains(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                assert(s1.extra_mappings().dom().contains(vaddr));
            }
        } else {
            if s1.extra_mappings().dom().contains(vaddr) {
                let core = choose |core: Core| s1.is_extra_vaddr_core(core, vaddr);
                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s2.is_extra_vaddr(vaddr));
                assert(!s1.candidate_vaddr_overlaps(vaddr));

                match s2.core_states[s2.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        monotonic_candidate_mapping_overlaps_existing_vmem(
                            s2.effective_mappings(),
                            s1.effective_mappings(),
                            vaddr,
                            pte);
                    }
                    _ => { }
                }

                assert(!s2.candidate_vaddr_overlaps(vaddr));
                assert(s2.extra_mappings().dom().contains(vaddr));
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                let core = choose |core: Core| s2.is_extra_vaddr_core(core, vaddr);

                assert(s1.core_states[core].PTE() == s2.core_states[core].PTE());
                assert(s1.get_extra_vaddr_core(vaddr) == core);
                assert(s2.get_extra_vaddr_core(vaddr) == core);
                assert(s1.is_extra_vaddr(vaddr));
                assert(!s2.candidate_vaddr_overlaps(vaddr));

                match s1.core_states[s1.get_extra_vaddr_core(vaddr)] {
                    CoreState::MapWaiting { vaddr: vaddr1, pte, .. }
                    | CoreState::MapExecuting { vaddr: vaddr1, pte, .. } => 
                    {
                        let mappings = s1.effective_mappings();
                        assert(vaddr1 == vaddr);

                        let core1 = this_core;
                        let core2 = core;
                        let mr1 = MemRegion {
                            base: s2.core_states[core1].vaddr(),
                            size: s2.core_states[core1].pte_size(s2.interp_pt_mem()),
                        };
                        let mr2 = MemRegion {
                            base: s2.core_states[core2].vaddr(),
                            size: s2.core_states[core2].pte_size(s2.interp_pt_mem()),
                        };
                        assert(!overlap(mr1, mr2));
                        assert(s2.core_states[core1].vaddr() == this_vaddr);

                        assert(s2.core_states[core1].pte_size(s2.interp_pt_mem())
                            == mappings[this_vaddr].frame.size);

                        assert(mr1 == MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size });
                        assert(mr2 == MemRegion { base: vaddr, size: pte.frame.size });
                        assert(!overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: this_vaddr, size: mappings[this_vaddr].frame.size },
                        ));
                    }
                    _ => { }
                }

                assert(!s1.candidate_vaddr_overlaps(vaddr));
                assert(s1.extra_mappings().dom().contains(vaddr));
            }
        }
    });
}

// can go either direction:
// either starting a Map operation that is destined to fail because of overlap
// (thus moving Idle -> MapWaiting) or ending such an operation (MapExecution -> MapDone Err case)
proof fn extra_mappings_preserved_for_overlap_map(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    this_core: Core,
)
    requires
        forall |core: Core, vaddr: nat|
            core != this_core ==>
            s1.is_extra_vaddr_core(core, vaddr) ==> s2.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==> s1.is_extra_vaddr_core(core, vaddr),
        forall |core: Core, vaddr: nat|
            s2.is_extra_vaddr_core(core, vaddr) ==>
                s1.core_states[core].PTE() == s2.core_states[core].PTE(),
        s1.core_states.dom().contains(this_core),
        match s1.core_states[this_core] {
            CoreState::MapWaiting { ult_id, vaddr, pte }
            | CoreState::MapExecuting { ult_id, vaddr, pte } =>
                candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte),
            _ => false,
        },
        forall |core: Core| core != this_core ==> (
            (match #[trigger] s1.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            }) <==> (match #[trigger] s2.core_states[core] {
                CoreState::MapWaiting { .. } | CoreState::MapExecuting { .. } => true,
                _ => false,
            })
        ),
        s2.core_states.dom().contains(this_core),
        match s2.core_states[this_core] {
            CoreState::Idle | CoreState::MapDone { result: Err(_), .. } => true,
            _ => false,
        },
            
        s1.effective_mappings() == s2.effective_mappings(),
        s1.interp_pt_mem() =~= s2.interp_pt_mem(),
    ensures
        s1.extra_mappings() == s2.extra_mappings()
{
    let (this_vaddr, this_pte) = match s1.core_states[this_core] {
        CoreState::MapWaiting { ult_id, vaddr, pte }
        | CoreState::MapExecuting { ult_id, vaddr, pte } => (vaddr, pte),
        _ => arbitrary(),
    };

    assume(s1.inv(c)); assume(s1.sound);
    assume(s2.inv(c)); assume(s2.sound);
    vaddr_distinct(c, s1);
    vaddr_distinct(c, s2);

    reveal(os::State::extra_mappings);
    assert_maps_equal!(s1.extra_mappings(), s2.extra_mappings(), vaddr => {
        if vaddr == this_vaddr {
            let pte = this_pte;
            if s1.extra_mappings().dom().contains(vaddr) {
                assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
                assert(!s1.inflight_vaddr().contains(vaddr));


                if !candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte) {
                    // need to show candidate can't overlap anything in
                    // interp_pt_mem() - effective_mappings()
                    // i.e., need to show candidate can't overlap anything in inflight_vaddr
                    let ov_vaddr = choose |b: nat|
                        #[trigger] s1.interp_pt_mem().contains_key(b)
                        && overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: b, size: s1.interp_pt_mem()[b].frame.size },
                        );
                    assert(s1.interp_pt_mem().contains_key(ov_vaddr));
                    assert(overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: ov_vaddr, size: s1.interp_pt_mem()[ov_vaddr].frame.size },
                    ));
                    assert(!s1.effective_mappings().contains_key(ov_vaddr));
                    assert(s1.inflight_vaddr().contains(ov_vaddr));

                    let ov_core = choose|ov_core: Core|
                        #[trigger] s1.core_states.contains_key(ov_core) &&
                        !s1.core_states[ov_core].is_idle() &&
                        s1.core_states[ov_core].vaddr() == ov_vaddr;
                    assert(s1.core_states.contains_key(ov_core));
                    assert(s1.core_states[ov_core].vaddr() == ov_vaddr);

                    // contradiction through inv_inflight_map_no_overlap_inflight_vmem

                    let mr1 = MemRegion {
                        base: s1.core_states[this_core].vaddr(),
                        size: s1.core_states[this_core].pte_size(s1.interp_pt_mem()),
                    };
                    let mr2 = MemRegion {
                        base: s1.core_states[ov_core].vaddr(),
                        size: s1.core_states[ov_core].pte_size(s1.interp_pt_mem()),
                    };
                    //assert(mr1 == MemRegion { base: vaddr, size: pte.frame.size });
                    //assert(s1.core_states[ov_core].vaddr() == ov_vaddr);
                    //assert(s1.core_states[ov_core].pte_size(s1.interp_pt_mem()) == s1.interp_pt_mem()[ov_vaddr].frame.size);
                    //assert(mr2 == MemRegion { base: ov_vaddr, size: s1.interp_pt_mem()[ov_vaddr].frame.size });
                    assert(overlap(mr1, mr2));
                    //assert(c.valid_core(this_core));
                    //assert(c.valid_core(ov_core));
                    //assert(!s1.core_states[ov_core].is_idle());
                    //assert(!s2.core_states[this_core].is_idle());
                    //assert(ov_core == this_core);

                    //assert(s1.inflight_vaddr().contains(this_vaddr));

                    assert(false);
                }

                assert(candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte));
                assert(s1.candidate_vaddr_overlaps(vaddr));
                //assert(s2.extra_mappings().dom().contains(vaddr));
                //assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
                assert(false);
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                assert(false);
            }
        } else {
            if s1.extra_mappings().dom().contains(vaddr) {
                assert(s2.extra_mappings().dom().contains(vaddr));
                assert(s1.extra_mappings()[vaddr] == s2.extra_mappings()[vaddr]);
            }
            if s2.extra_mappings().dom().contains(vaddr) {
                assert(s1.extra_mappings().dom().contains(vaddr));
            }
        }
    });
}

proof fn vaddr_mapping_is_being_modified_from_vaddr_unmap(
    c: os::Constants,
    s: os::State,
    core: Core,
    tlb_va: usize,
    vaddr: nat,
)
    requires
        s.inv(c),
        s.sound,
        s.extra_mappings().dom().contains(tlb_va as nat)
           || s.inflight_vaddr().contains(tlb_va as nat),
        c.valid_core(core),
        s.mmu@.tlbs[core].dom().contains(tlb_va),
        between(vaddr, tlb_va as nat, tlb_va as nat + s.mmu@.tlbs[core][tlb_va].frame.size)
    ensures
        s.interp(c).vaddr_mapping_is_being_modified(c.interp(), vaddr),
        s.interp(c).vaddr_mapping_is_being_modified_choose(c.interp(), vaddr)
            == Some((tlb_va as nat, s.mmu@.tlbs[core][tlb_va]))
{
    assume(false);
}

spec fn no_overlaps(m: Map<nat, PTE>) -> bool {
    forall |i, j|
        #[trigger] m.dom().contains(i) && #[trigger] m.dom().contains(j) && i != j
          ==> i + m[i].frame.size <= j
           || j + m[j].frame.size <= i
}

proof fn no_overlaps_applied_mappings(c: os::Constants, s: os::State)
    requires s.inv(c),
    ensures no_overlaps(s.applied_mappings()),
{
    assume(false);
}

proof fn no_overlaps_interp_pt_mem(c: os::Constants, s: os::State)
    requires s.inv(c),
    ensures no_overlaps(s.interp_pt_mem()),
{
    let m = s.interp_pt_mem();
    assert forall |i, j|
        #[trigger] m.dom().contains(i) && #[trigger] m.dom().contains(j) && i != j
          && i + m[i].frame.size > j
          && j + m[j].frame.size > i
          implies false
    by {
        reveal(PTMem::view);
        if i <= j < i + m[i].frame.size {
            s.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(i as usize, j as usize);
            assert(false);
        } else if j <= i < j + m[j].frame.size {
            s.mmu@.pt_mem.lemma_pt_walk_agrees_in_frame(j as usize, i as usize);
            assert(false);
        } else {
            assert(false);
        }
    }
}

proof fn interp_vmem_subrange(c: os::Constants, s: os::State, base: nat, pte: PTE, vaddr: int, size: int)
    requires
        no_overlaps(s.applied_mappings()),
        s.applied_mappings().dom().contains(base),
        s.applied_mappings()[base] == pte,
        base <= vaddr,
        size >= 0,
        vaddr + size <= base + pte.frame.size,

        base + pte.frame.size <= s.interp_vmem(c).len(),
        pte.frame.base + pte.frame.size <= s.mmu@.phys_mem.len(),

    ensures ({
        let paddr = pte.frame.base + vaddr - base;
        s.interp_vmem(c).subrange(vaddr, vaddr + size)
            == s.mmu@.phys_mem.subrange(paddr, paddr + size)
    })
{
    let paddr = pte.frame.base + vaddr - base;

    vstd::seq_lib::assert_seqs_equal!(
        s.interp_vmem(c).subrange(vaddr, vaddr + size),
        s.mmu@.phys_mem.subrange(paddr, paddr + size),
        idx => {
            let v = vaddr + idx;
            let p = paddr + idx;

            let (base0, pte0) = os::State::base_and_pte_for_vaddr(s.applied_mappings(), vaddr);

            assert(s.applied_mappings().contains_pair(base, pte));
            assert(between(v as nat, base, base + pte.frame.size));

            assert(s.applied_mappings().contains_pair(base0, pte0)
              && between(v as nat, base0, base0 + pte0.frame.size));

            assert(base0 == base);
            assert(pte0 == pte);

            assert(s.interp_vmem(c)[v] == s.mmu@.phys_mem[p]);
        }
    );
}

proof fn interp_vmem_update_range(c: os::Constants, s: os::State, base: nat, pte: PTE, vaddr: int, size: int, new: Seq<u8>,)
    requires
        no_overlaps(s.applied_mappings()),
        s.applied_mappings().dom().contains(base),
        s.applied_mappings()[base] == pte,
        base <= vaddr,
        size >= 0,
        vaddr + size <= base + pte.frame.size,

        base + pte.frame.size <= s.interp_vmem(c).len(),
        pte.frame.base + pte.frame.size <= s.mmu@.phys_mem.len(),

        size == new.len(),

    ensures ({
        let paddr = pte.frame.base + vaddr - base;
        update_range(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem), vaddr, new)
          == os::State::vmem_apply_mappings(s.applied_mappings(), update_range(s.mmu@.phys_mem, paddr, new))
    })
{
    let paddr = pte.frame.base + vaddr - base;

    let b1 = update_range(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem), vaddr, new);
    let b2 = os::State::vmem_apply_mappings(s.applied_mappings(), update_range(s.mmu@.phys_mem, paddr, new));

    assert(b1.len() == b2.len());

    vstd::assert_seqs_equal!(b1, b2, idx => {
        let (base0, pte0) = os::State::base_and_pte_for_vaddr(s.applied_mappings(), idx);

        if base <= idx < base + pte.frame.size {
            assert(s.applied_mappings().contains_pair(base, pte));
            assert(between(idx as nat, base, base + pte.frame.size));

            assert(s.applied_mappings().contains_pair(base0, pte0)
              && between(idx as nat, base0, base0 + pte0.frame.size));

            assert(base == base0);
            assert(pte == pte0);

            assert(b1[idx] == b2[idx]);
        } else {
            if os::State::has_base_and_pte_for_vaddr(s.applied_mappings(), idx) {
                assert(base != base0);
                let p_idx = pte0.frame.base + idx - base0;
                assert(!(vaddr <= idx < vaddr + new.len()));

                assume(pte0.frame.base + pte0.frame.size <= s.mmu@.phys_mem.len());

                assert(base0 <= idx < base0 + pte0.frame.size);
                assert(pte0.frame.base <= p_idx < pte0.frame.base + pte0.frame.size);

                assert(base <= vaddr <= vaddr + new.len() <= base + pte.frame.size);
                assert(s.applied_mappings().dom().contains(base));
                assert(s.applied_mappings().dom().contains(base0));
                assert(pte.frame.base <= paddr <= paddr + new.len() <= pte.frame.base + pte.frame.size);

                // need physical ranges of the mappings don't overlap
                assume(!(paddr <= p_idx < paddr + new.len()));

                assert(paddr + new.len() <= s.mmu@.phys_mem.len());
                assert(0 <= p_idx < s.mmu@.phys_mem.len());

                assert(b1[idx] == os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem)[idx]);
                assert(os::State::vmem_apply_mappings(s.applied_mappings(), s.mmu@.phys_mem)[idx]
                    == s.mmu@.phys_mem[p_idx]);
                assert(s.mmu@.phys_mem[p_idx]
                    == update_range(s.mmu@.phys_mem, paddr, new)[p_idx]);

                assert(b1[idx] == b2[idx]);
            } else {
                assert(b1[idx] == b2[idx]);
            }
        }
    });
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
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
        lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
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
        assert(s1.inflight_vaddr() =~= s2.inflight_vaddr()) by {
            assert(s2.inflight_vaddr().subset_of(s1.inflight_vaddr()));
            assert forall|v| s1.inflight_vaddr().contains(v) implies s2.inflight_vaddr().contains(v) by {
                    if (!s1.inflight_unmap_vaddr().contains(v)) {
                        let map_core = choose|core| s1.core_states.contains_key(core) && s1.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:v, result: Ok(()), .. };
                        assert(s2.core_states.contains_key(map_core));
                        assert(s2.interp_pt_mem().contains_key(v));
                    }
                }
            assert(s1.inflight_vaddr().subset_of(s2.inflight_vaddr()));
        }
        assert(s1.effective_mappings() =~= s2.effective_mappings());
        assert(hl_s2.mappings === hl_s1.mappings);
        assert(hlspec::state_unchanged_besides_thread_state_and_mem(
            hl_s1,
            hl_s2,
            ult_id,
            hlspec::ThreadState::Map { vaddr, pte },
        ));

        if candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte) {
            extra_mappings_preserved_for_overlap_map(c, s2, s1, core);
            assert(hl_s1.mem == hl_s2.mem);
        }

        assume(forall|vaddr: nat|  #[trigger] is_in_mapped_region(c.interp().phys_mem_size, hl_s1.mappings, vaddr) ==> hl_s2.mem[vaddr as int] === hl_s1.mem[vaddr as int]);

        // this was originally in MapEnd, needs fixing for MapStart
        //proofgoal (4/4):  forall|vaddr: int| is_in_mapped_region(c.phys_mem_size, s1.mappings, vaddr as nat) ==> s2.mem[vaddr] === s1.mem[vaddr]
        /*assert forall|mem_vaddr: nat| #![auto]
            is_in_mapped_region(c.common.phys_mem_size, hl_s1.mappings, mem_vaddr)
        implies hl_s2.mem[mem_vaddr as int] === hl_s1.mem[mem_vaddr as int]
        by {
            let (mem_base, mem_pte) = os::State::base_and_pte_for_vaddr(s1.effective_mappings(), mem_vaddr as int);
            assert forall|page, entry|
                hl_s2.mappings.contains_pair(page, entry) && between(
                    mem_vaddr,
                    page,
                    page + entry.frame.size,
                ) implies (page == mem_base) && (entry == mem_pte)
            by {
                if hl_s2.mappings.contains_pair(page, entry) && between(
                    mem_vaddr,
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
                mem_vaddr,
                page,
                page + entry.frame.size,
            ) implies (page == mem_base) && (entry == mem_pte) by {
                assert(s1.effective_mappings().dom().subset_of(
                    s2.effective_mappings().dom(),
                ));
                assert(hl_s1.mappings.submap_of(hl_s2.mappings));
                assert(hl_s2.mappings.contains_pair(page, entry) && between(
                    mem_vaddr,
                    page,
                    page + entry.frame.size,
                ));
            }

            assert(hl_s1.mappings.submap_of(hl_s2.mappings));
            assert(hl_s2.mappings.contains_pair(mem_base, mem_pte));
            assert(is_in_mapped_region(c.common.phys_mem_size, hl_s2.mappings, mem_vaddr));
            let (mem_base2, mem_pte2) = os::State::base_and_pte_for_vaddr(s2.effective_mappings(), mem_vaddr as int);
            assert(mem_base2 == mem_base);
            assert(mem_pte2 == mem_pte);

            assert (s1.mmu@.phys_mem =~= s2.mmu@.phys_mem);

            assert(candidate_mapping_in_bounds(mem_base, mem_pte));
            x86_arch_spec_upper_bound();

            assert(0 <= mem_vaddr < MAX_BASE);
            assert(s1.interp_vmem(c).len() == MAX_BASE );
        }*/

    } else {
        assert(!s2.sound);
        assert(hlspec::unsound_state(hl_s1, hl_s2));
    };
}


proof fn step_MapOpChange_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, paddr: usize, value: usize,  lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        os::step_MapOpChange(c, s1, s2, core, paddr, value, lbl),
        s1.sound,
    ensures
        hlspec::step_Stutter(c.interp(), s1.interp(c), s2.interp(c), lbl)
{
    broadcast use to_rl1::next_refines;
    //interpretations
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    //corestate
    assert(s1.core_states[core] is MapExecuting);
    let ult_id = s1.core_states[core]->MapExecuting_ult_id;
    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
    let pte = s1.core_states[core]->MapExecuting_pte;
    let result: std::result::Result<(), ()> = Ok(());

    //First goal prove soundess
    assert(hl_s2.sound);

    //Second goal: prove  //assert(hl_s1.thread_state === hl_s2.thread_state);
    assert(hl_c.valid_thread(ult_id));
    assert(s1.interp(c).thread_state[ult_id] is Map);
    assert(s1.core_states[core] is MapExecuting);
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
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                        },
                    ));
                }
            }
        }
    }
    assert(hl_s1.thread_state =~= hl_s2.thread_state);

    //third goal: prove
    //(hl_s2.mappings === hl_s1.mappings);
    //(hl_s2.mem === hl_s1.mem); follows directly

    assert(s1.effective_mappings() =~= s2.effective_mappings()) by {
        // ==> direction
        assert(!s1.interp_pt_mem().contains_key(vaddr));
        assert(!s1.effective_mappings().contains_key(vaddr));
        assert(s2.interp_pt_mem().remove(vaddr) =~= s1.interp_pt_mem());
        assert(s1.effective_mappings().dom().subset_of(s2.effective_mappings().dom()));

        // <== direction
        assert(s2.interp_pt_mem().contains_key(vaddr) && s2.core_states.contains_key(core) &&
                s2.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:vaddr, result: Ok(()), .. });
        assert(s2.inflight_vaddr().contains(vaddr));
        assert forall |v| s2.effective_mappings().contains_key(v) implies s1.effective_mappings().contains_key(v) by {
            if (v == vaddr || !s1.inflight_vaddr().contains(v)) {
                assert(!s2.effective_mappings().contains_key(vaddr));
            } else {
                assert(s1.inflight_unmap_vaddr().contains(v));
                let unmap_core = choose|cr|
                    s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                            vaddr === v
                        },
                        _ => false,
                    };
                assert(s2.interp_pt_mem().contains_key(v));
                // assert(!(unmap_core == core));
                assert(s2.core_states.contains_key(unmap_core));
                // assert(s1.core_states[unmap_core] == s2.core_states[unmap_core]);
                assert(s2.inflight_unmap_vaddr().contains(v));
            }
        }
    }

    assume(s2.extra_mappings() == s1.extra_mappings().remove(vaddr));
    assume(s1.extra_mappings().dom().contains(vaddr));
    assume(s1.extra_mappings()[vaddr] == s2.interp_pt_mem()[vaddr]);
    assert(s1.applied_mappings() =~= s2.applied_mappings());
}

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
    assert(lbl is MapEnd);
    let vaddr = lbl->MapEnd_vaddr;
    let thread_id = lbl->MapEnd_thread_id;
    let result = lbl->MapEnd_result;
    //core_state
    assert(s1.core_states[core] is MapDone);
    let ult_id = s1.core_states[core]->MapDone_ult_id;
    let vaddr2 = s1.core_states[core]->MapDone_vaddr;
    let pte = s1.core_states[core]->MapDone_pte;
    let result = s1.core_states[core]->MapDone_result;

    assert(vaddr == vaddr2);
    assert(hl_c.valid_thread(ult_id));
    assert(hl_s2.sound == hl_s1.sound);
    assert(hl_s2.thread_state === hl_s1.thread_state.insert(
            ult_id,
            hlspec::ThreadState::Idle,
    ));
    assert(s1.interp(c).thread_state[ult_id] is Map);

    if result is Ok {

        //proofgoal: ! os overlap => ! hl overlap
        //by inv_overlap_of_mapped_maps-invariant we know:
        assert(!candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem().remove(vaddr), vaddr, pte));
        //thereby follows as effective mappings is always a subset of interp_pt_mem and vaddr not being in effective mappings:
        assert(!candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte)) by {
            assert(s1.core_states.contains_key(core));
            assert(s1.inflight_vaddr().contains(vaddr));
            assert(!s1.effective_mappings().dom().contains(vaddr));
            assert(s1.effective_mappings().dom().subset_of(s2.interp_pt_mem().remove(vaddr).dom()));
        }

        //proofgoal (1/4): (result is Ok);
        assert ( result is Ok);

        //proofgoal (2/4): ( hl_s2.mappings === hl_s1.mappings.insert(vaddr, pte))
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert(s1.interp_pt_mem().contains_pair(vaddr, pte));
        assert(!s1.inflight_unmap_vaddr().contains(vaddr)) by {
            let unmap_vaddr = vaddr;
            if (s1.inflight_unmap_vaddr().contains(vaddr)) {
                let unmap_core = choose |c: Core|
                s1.core_states.contains_key(c) && match s1.core_states[c] {
                    os::CoreState::UnmapWaiting { ult_id, vaddr }
                    | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                        vaddr == unmap_vaddr
                    },
                    _ => false,
                };
                assert(s1.core_states[unmap_core] is UnmapWaiting);
                assert(s1.interp_pt_mem().contains_key(vaddr));
                assert(s1.core_states[unmap_core].pte_size(s1.interp_pt_mem()) == s1.interp_pt_mem()[vaddr].frame.size);
                assert(s1.interp_pt_mem()[vaddr].frame.size > 0);
                assert(c.valid_core(core));
                assert(c.valid_core(unmap_core));
                assert(!s1.core_states[core].is_idle());
                assert(!s1.core_states[unmap_core].is_idle());
                assert(overlap(
                    MemRegion {
                        base: s1.core_states[core].vaddr(),
                        size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[unmap_core].vaddr(),
                        size: s1.core_states[unmap_core].pte_size(s1.interp_pt_mem()),
                    }));
                assert(core != unmap_core);
                // contradiction to inflight_map_no_overlap_inflight_vmem
                assert(false);
            }
        }
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
                            size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s1.core_states[unmap_core].vaddr(),
                            size: s1.core_states[unmap_core].pte_size(
                                s1.interp_pt_mem(),
                            ),
                        },
                    ));
                }
            }
        };
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr());
        assert(!s2.inflight_vaddr().contains(vaddr));
        assert(s1.inflight_vaddr() =~= s1.inflight_unmap_vaddr().insert(vaddr));
        assert(s2.inflight_vaddr() =~= s1.inflight_vaddr().remove(vaddr));
        assert(hl_s2.mappings === hl_s1.mappings.insert(vaddr, pte));

        extra_mappings_preserved_effective_mapping_inserted(c, s1, s2, core);
    } else {

        //proofgoal: os overlap => hl overlap
        assert(candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte));
        assert(candidate_mapping_overlaps_existing_vmem(s1.effective_mappings(), vaddr, pte)) by {
            let os_overlap_vaddr = choose|b: nat| #![auto] {
                &&& s1.interp_pt_mem().dom().contains(b)
                &&& overlap(
                    MemRegion { base: vaddr, size: pte.frame.size },
                    MemRegion { base: b, size: s1.interp_pt_mem()[b].frame.size },
                )
            };
            if (s1.inflight_vaddr().contains(os_overlap_vaddr)) {
                assert(s1.inflight_unmap_vaddr().contains(os_overlap_vaddr));
                let os_overlap_core = choose |core: Core|
                s1.core_states.contains_key(core) && match s1.core_states[core] {
                    os::CoreState::UnmapWaiting { ult_id, vaddr }
                    | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
                    | os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                        vaddr === os_overlap_vaddr
                    },
                    _ => false,
                };
                assert(c.valid_core(core));
                assert(c.valid_core(os_overlap_core));
                assert(!s1.core_states[core].is_idle());
                assert(!s1.core_states[os_overlap_core].is_idle());
                assert(overlap(
                    MemRegion {
                        base: s1.core_states[core].vaddr(),
                        size: s1.core_states[core].pte_size(s1.interp_pt_mem()),
                    },
                    MemRegion {
                        base: s1.core_states[os_overlap_core].vaddr(),
                        size: s1.core_states[os_overlap_core].pte_size(s1.interp_pt_mem()),
                    }));
                assert(core != os_overlap_core);
                // contradiction to inflight_map_no_overlap_inflight_vmem
                assert(false);
            } else {
                assert(s1.effective_mappings().contains_key(os_overlap_vaddr));
            }
        }

        //proofgoal (1/3) result is Err
        assert(result is Err);

        //proofgoal (2/3) s2.mappings === s1.mappings
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert(s1.inflight_unmap_vaddr() =~= s2.inflight_unmap_vaddr()) by {
            assert(s2.inflight_unmap_vaddr().subset_of(s1.inflight_unmap_vaddr()));
            assert(s1.core_states[core] is MapDone);
            assert(s1.core_states.remove(core) =~= s2.core_states.remove(core));
            assert(s1.inflight_unmap_vaddr().subset_of(s2.inflight_unmap_vaddr()));
        };
        assert(s1.inflight_unmap_vaddr() =~= s1.inflight_vaddr());
        assert(s1.inflight_vaddr() =~= s2.inflight_vaddr());
        assert(s2.effective_mappings() =~= s1.effective_mappings());

        extra_mappings_preserved(c, s1, s2);

        //proofgoal (3/3) s2.mem === s1.mem
        assert(hl_s1.mem =~= hl_s2.mem);
    }
}
//disclaimer this probably dosnt have to be so long.
proof fn step_UnmapStart_refines(c: os::Constants, s1: os::State, s2: os::State, core: Core, lbl: RLbl)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapStart(c, s1, s2, core, lbl),
    ensures
        hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl),
{
    //label
    let vaddr = lbl->UnmapStart_vaddr;
    let ult_id = lbl->UnmapStart_thread_id;

    //interpretation
    let hl_c = c.interp();
    let hl_s1 = s1.interp(c);
    let hl_s2 = s2.interp(c);

    //let pt = s1.interp_pt_mem();
    //let pte_size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
    let pte = if s1.interp_pt_mem().dom().contains(vaddr) { Some(s1.interp_pt_mem()[vaddr]) } else { Option::None };
    let hl_pte = if hl_s1.mappings.contains_key(vaddr) { Some(hl_s1.mappings[vaddr]) } else { Option::None };

    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };
    let hl_pte_size = if hl_pte is Some { hl_pte.unwrap().frame.size } else { 0 };

    assert(hl_pte_size <= pte_size);

    lemma_unmap_soundness_equality(c, s1, vaddr, pte_size);
    //assert(s1.sound && os::step_Unmap_sound(c, s1, vaddr, pte_size) == hl_s1.soud && hl);
    assert(hl_s1.sound);
    if (pte == hl_pte){
        if hlspec::step_Unmap_sound(hl_s1, vaddr, pte_size) {
            assert(hl_s1.sound == hl_s2.sound);

            assert forall|key| #[trigger]
                hl_s1.thread_state.dom().contains(key)
            implies hl_s1.thread_state.insert( ult_id, hlspec::ThreadState::Unmap { vaddr, pte },)[key]
                 == hl_s2.thread_state[key] by {
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
                            && s1.inflight_vaddr().contains(vaddr) {
                            let overlap_core = choose|core|
                                s1.core_states.dom().contains(core) && match s1.core_states[core] {
                                    os::CoreState::UnmapWaiting { ult_id, vaddr: v }
                                    | os::CoreState::UnmapExecuting { ult_id, vaddr: v, .. }
                                    | os::CoreState::UnmapOpDone { ult_id, vaddr: v, .. }
                                    | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr: v, .. }
                                    | os::CoreState::MapDone {ult_id, vaddr: v, result: Ok(()), .. } => {
                                        vaddr === v
                                    },
                                    _ => false,
                                };
                            //overlap{};
                            assert(!s2.core_states[core].is_idle()
                                && !s2.core_states[overlap_core].is_idle() && overlap(
                                MemRegion {

                                    base: s2.core_states[core].vaddr(),
                                    size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
                                },
                                MemRegion {
                                    base: s2.core_states[overlap_core].vaddr(),
                                    size: s2.core_states[overlap_core].pte_size(
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
            // jp: unstable indeed but i think its better now?
            assert(hl_s2.thread_state =~= hl_s1.thread_state.insert(
                ult_id,
                hlspec::ThreadState::Unmap { vaddr, pte },
            ));
            if pte is None {
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert forall|ids|
                    s1.inflight_vaddr().contains(ids) implies s2.inflight_vaddr().contains(
                    ids,
                ) by {
                    if s1.inflight_vaddr().contains(ids) {
                        let critical_core = choose|cr|
                            s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                                os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. }
                                | os::CoreState::UnmapWaiting { ult_id, vaddr }
                                | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                                | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                    vaddr === ids
                                },
                                _ => false,
                            };
                        assert(!(critical_core == core));
                        assert(s2.core_states.dom().contains(critical_core));
                    }
                }
                assert(hl_s2.mappings === hl_s1.mappings);
                extra_mappings_preserved(c, s1, s2);
                assert(hl_s2.mem =~= hl_s1.mem);
                //assert(hl_s1.mem.dom() === hlspec::mem_domain_from_mappings(
                //    hl_c.phys_mem_size,
                //    hl_s1.mappings,
                //));
                assert(hl_s1.mappings =~= hl_s1.mappings.remove(vaddr));
                //assert(hl_s2.mem.dom() === hlspec::mem_domain_from_mappings(
                //    hl_c.phys_mem_size,
                //    hl_s1.mappings.remove(vaddr),
                //));
                assert(hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            } else {

                assert (hl_pte == pte);

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
                assert(s2.inflight_unmap_vaddr() =~= s1.inflight_unmap_vaddr().insert(vaddr));
                assert(s2.inflight_vaddr() =~= s1.inflight_vaddr().insert(vaddr)) by {
                    assert(s2.inflight_vaddr().subset_of(s1.inflight_vaddr().insert(vaddr)));
                    assert forall |v| #![auto] s1.inflight_vaddr().insert(vaddr).contains(v) implies s2.inflight_vaddr().contains(v) by {
                        if (!s1.inflight_unmap_vaddr().contains(v) && v != vaddr) {
                            let map_core = choose|core|  s1.core_states.contains_key(core) &&
                            s1.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:v, result: Ok(()), .. };
                            assert(s1.interp_pt_mem().dom().contains(v));
                            assert(s2.interp_pt_mem().dom().contains(v));
                            assert(s2.core_states.contains_key(map_core));
                            assert(s1.core_states[map_core] == s2.core_states[map_core]);
                            assert( s2.core_states.contains_key(map_core) &&
                            s2.core_states[map_core] matches os::CoreState::MapDone {ult_id, vaddr:v, result: Ok(()), .. });
                        } else {
                            assert(s1.inflight_unmap_vaddr().insert(vaddr).contains(v));
                            assert(s2.inflight_unmap_vaddr().contains(v));
                        }
                    }
                }
                assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
                assert(s2.effective_mappings().dom().subset_of(s1.effective_mappings().dom()));
                assert(hl_s2.mappings =~= hl_s1.mappings.remove(vaddr));

                assert(hl_s1.mappings =~= hl_s2.mappings.insert(vaddr, hl_s1.mappings.index(vaddr)));

                extra_mappings_preserved_effective_mapping_removed(c, s1, s2, core);

                assert(hlspec::step_UnmapStart(c.interp(), s1.interp(c), s2.interp(c), lbl));
            }
        }
    } else {
        assert(hl_pte is None);
        assert(pte is Some);
        assert(s1.interp_pt_mem().dom().contains(vaddr));
        assert(s1.inflight_vaddr().contains(vaddr));
        let inflight_vaddr = vaddr;
        let inflight_core = choose|c: Core| s1.core_states.contains_key(c)
                                    && match s1.core_states[c] {
                                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                                        | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                                        | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
                                        | os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                                            vaddr === inflight_vaddr
                                        },
                                        _ => false,
                                    };
        assert(s1.core_states.values().contains(s1.core_states[inflight_core]));
        assert(os::candidate_mapping_overlaps_inflight_vmem(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte_size));
        assert(!s2.sound);
        if(s1.inflight_unmap_vaddr().contains(inflight_vaddr)){
            lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
            let unmap_thread_state = choose |thread_state|
                   s1.interp_thread_state(c).values().contains(thread_state)
                && s1.interp_pt_mem().dom().contains(inflight_vaddr)
                && (thread_state matches hlspec::ThreadState::Unmap { vaddr, .. } && vaddr === inflight_vaddr);
            let unmap_pte = unmap_thread_state->Unmap_pte;
            let unmap_size = if unmap_pte.is_some() { unmap_pte.unwrap().frame.size } else { 0 };
            assert (overlap(
                    MemRegion { base: inflight_vaddr, size: unmap_size },
                    MemRegion { base: inflight_vaddr, size: 0},
                ));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), inflight_vaddr, 0));
            assert(!hlspec::step_Unmap_sound(hl_s1, inflight_vaddr, 0));
        } else {
            let map_core = choose|core|  s1.core_states.contains_key(core) &&
            s1.core_states[core] matches os::CoreState::MapDone {ult_id, vaddr:inflight_vaddr, result: Ok(()), .. };
            let map_ult = s1.core_states[map_core]->MapDone_ult_id;
            assert(s1.interp_thread_state(c).dom().contains(map_ult));
            assert(s1.interp_thread_state(c)[map_ult] is Map);
            assert(s1.interp_thread_state(c).values().contains(s1.interp_thread_state(c)[map_ult]));
            let map_pte = s1.interp_thread_state(c)[map_ult]->Map_pte;
            assert (overlap(
                MemRegion { base: inflight_vaddr, size: map_pte.frame.size  },
                MemRegion { base: inflight_vaddr, size: 0},
            ));
            assert(hlspec::candidate_mapping_overlaps_inflight_vmem(hl_s1.thread_state.values(), inflight_vaddr, 0));
            assert(!hlspec::step_Unmap_sound(hl_s1, inflight_vaddr, 0));
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
    lbl: RLbl,
)
    requires
        s1.inv(c),
        s2.inv(c),
        s1.sound,
        os::step_UnmapOpChange(c, s1, s2, core, paddr, value, lbl),
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
                            size: s2.core_states[core_of_key].pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: s2.core_states[core].vaddr(),
                            size: s2.core_states[core].pte_size(s2.interp_pt_mem()),
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
        assert(s1.inflight_vaddr().contains(vaddr));
        assert forall|ids|
            s1.inflight_vaddr().contains(
                ids,
            ) implies #[trigger] s2.inflight_vaddr().insert(vaddr).contains(ids) by {
            if s1.inflight_vaddr().contains(ids) {
                if ids === vaddr {
                } else {
                    assert(s1.interp_pt_mem().dom().contains(ids));
                    assert(s2.interp_pt_mem().dom().contains(ids));
                    let critical_core = choose|cr|
                        s1.core_states.dom().contains(cr) && match s1.core_states[cr] {
                            os::CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. }
                            |os::CoreState::UnmapWaiting { ult_id, vaddr }
                            | os::CoreState::UnmapExecuting { ult_id, vaddr, .. }
                            | os::CoreState::UnmapOpDone { ult_id, vaddr, .. }
                            | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. } => {
                                vaddr === ids
                            },
                            _ => false,
                        };
                    assert(!(critical_core == core));
                    assert(s2.core_states.dom().contains(critical_core));
                }
            }
        }
        assert(s1.inflight_vaddr() =~= s2.inflight_vaddr().insert(vaddr));

    } else {
        assert(s1.interp_pt_mem() =~= s2.interp_pt_mem());
        assert forall|ids|
            s1.inflight_vaddr().contains(ids) implies s2.inflight_vaddr().contains(
            ids,
        ) by {
            if s1.inflight_vaddr().contains(ids) {
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
        assert(s1.inflight_vaddr() =~= s2.inflight_vaddr());
    }
    assert(s1.effective_mappings() =~= s2.effective_mappings());

    assume(!s1.extra_mappings().dom().contains(vaddr));
    assume(s2.extra_mappings() =~= s1.extra_mappings().insert(vaddr, s1.interp_pt_mem()[vaddr]));
    assert(s1.applied_mappings() =~= s2.applied_mappings());
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
            lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s2);
            lemma_inflight_unmap_vaddr_equals_hl_unmap(c, s1);
            //assert(s1.inflight_unmap_vaddr().subset_of(s2.inflight_unmap_vaddr()));
            assert(s1.inflight_vaddr() =~= s1.inflight_unmap_vaddr());
            assert(s2.inflight_vaddr() =~= s2.inflight_unmap_vaddr());
            assert forall|key|
                s2.effective_mappings().dom().contains(
                    key,
                ) implies s1.effective_mappings().dom().contains(key) by {
                assert(s2.interp_pt_mem().dom().contains(key));
                assert(s1.interp_pt_mem().dom().contains(key));
                if key == vaddr {
                    assert(false);
                } else {
                    if s1.inflight_vaddr().contains(key) {
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

            assume(forall|mem_vaddr: nat| #![auto] is_in_mapped_region(c.common.phys_mem_size, hl_s2.mappings, mem_vaddr) 
                    ==> (hl_s2.mem[mem_vaddr as int] === hl_s1.mem[mem_vaddr as int]));
            // this was moved here from UnmapStart, needs updating
            /*
            assert forall|mem_vaddr: nat| #![auto] is_in_mapped_region(c.common.phys_mem_size, hl_s2.mappings, mem_vaddr) 
                    implies (hl_s2.mem[mem_vaddr as int] === hl_s1.mem[mem_vaddr as int]) 
            by {
                let (mem_base, mem_pte) = os::State::base_and_pte_for_vaddr(s2.effective_mappings(), mem_vaddr as int);
                assert forall|page, entry|
                    hl_s1.mappings.contains_pair(page, entry) && between(
                        mem_vaddr,
                        page,
                        page + entry.frame.size,
                    ) implies (page == mem_base) && (entry == mem_pte)
                by {
                    if hl_s1.mappings.contains_pair(page, entry) && between(
                        mem_vaddr,
                        page,
                        page + entry.frame.size,
                    ) {
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
                }
                assert forall|page, entry|
                hl_s2.mappings.contains_pair(page, entry) && between(
                    mem_vaddr,
                    page,
                    page + entry.frame.size,
                ) implies (page == mem_base) && (entry == mem_pte) by {
                    assert(s2.effective_mappings().dom().subset_of(
                        s1.effective_mappings().dom(),
                    ));
                    assert(hl_s2.mappings.submap_of(hl_s1.mappings));
                    assert(hl_s1.mappings.contains_pair(page, entry) && between(
                        mem_vaddr,
                        page,
                        page + entry.frame.size,
                    ));
                }
    
                assert(hl_s2.mappings.submap_of(hl_s1.mappings));
                assert(hl_s1.mappings.contains_pair(mem_base, mem_pte));
                assert(is_in_mapped_region(c.common.phys_mem_size, hl_s1.mappings, mem_vaddr));
                let (mem_base2, mem_pte2) = os::State::base_and_pte_for_vaddr(s1.effective_mappings(), mem_vaddr as int);
                assert(mem_base2 == mem_base);
                assert(mem_pte2 == mem_pte);
    
                assert (s1.mmu@.phys_mem =~= s2.mmu@.phys_mem);
                assert(candidate_mapping_in_bounds(mem_base, mem_pte));
                x86_arch_spec_upper_bound();
                assert(s1.interp_vmem(c).len() == MAX_BASE );
            }
            */

            assert(hlspec::step_UnmapEnd(c.interp(), s1.interp(c), s2.interp(c), lbl));
        },
        _ => {
            assert(false);
        },
    };
}

} // verus!
