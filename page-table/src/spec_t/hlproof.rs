#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    candidate_mapping_overlaps_existing_pmem, overlap, PTE
};
use crate::theorem::RLbl;
use crate::spec_t::hlspec::*;

verus! {

//ensures that if a new mapping is added the old ones are still in there and no new other mappings appear
//pub proof fn lemma_mem_domain_from_mappings(
//    phys_mem_size: nat,
//    mappings: Map<nat, PTE>,
//    base: nat,
//    pte: PTE,
//)
//    requires
//        !mappings.dom().contains(base),
//    ensures
//        (forall|word_idx: nat|
//            mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
//                ==> #[trigger] mem_domain_from_mappings_contains(
//                phys_mem_size,
//                word_idx,
//                mappings.insert(base, pte),
//            )),
//        (forall|word_idx: nat|
//            !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
//                && #[trigger] mem_domain_from_mappings_contains(
//                phys_mem_size,
//                word_idx,
//                mappings.insert(base, pte),
//            ) ==> between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size)),
//{
//    assert forall|word_idx: nat|
//        mem_domain_from_mappings_contains(
//            phys_mem_size,
//            word_idx,
//            mappings,
//        ) implies #[trigger] mem_domain_from_mappings_contains(
//        phys_mem_size,
//        word_idx,
//        mappings.insert(base, pte),
//    ) by {
//        let vaddr = word_idx * WORD_SIZE as nat;
//        let (base2, pte2) = choose|base: nat, pte: PTE|
//            {
//                let paddr = (pte.frame.base + (vaddr - base)) as nat;
//                let pmem_idx = word_index_spec(paddr);
//                &&& #[trigger] mappings.contains_pair(base, pte)
//                &&& between(vaddr, base, base + pte.frame.size)
//                &&& pmem_idx < phys_mem_size
//            };
//        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
//    };
//    assert forall|word_idx: nat|
//        !mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings)
//            && #[trigger] mem_domain_from_mappings_contains(
//            phys_mem_size,
//            word_idx,
//            mappings.insert(base, pte),
//        ) implies between(word_idx * WORD_SIZE as nat, base, base + pte.frame.size) by {
//        let vaddr = word_idx * WORD_SIZE as nat;
//        let (base2, pte2) = choose|base2: nat, pte2: PTE|
//            {
//                let paddr = (pte2.frame.base + (vaddr - base2)) as nat;
//                let pmem_idx = word_index_spec(paddr);
//                &&& #[trigger] mappings.insert(base, pte).contains_pair(base2, pte2)
//                &&& between(vaddr, base2, base2 + pte2.frame.size)
//                &&& pmem_idx < phys_mem_size
//            };
//        assert(mappings.insert(base, pte).contains_pair(base2, pte2));
//        assert(between(vaddr, base2, base2 + pte2.frame.size));
//        if !between(vaddr, base, base + pte.frame.size) {
//            assert(base2 != base || pte2 !== pte);
//            if base2 != base {
//                assert(mappings.contains_pair(base2, pte2));
//                assert(mem_domain_from_mappings_contains(phys_mem_size, word_idx, mappings));
//            }
//            assert(false);
//        } else {
//        }
//    };
//}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                               //
//                                        Step preserves inv lemmata                                             //
//                                                                                                               //
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub proof fn lemma_overlap(mappings: Map<nat, PTE>, base: nat, pte: PTE)
    requires
        pmem_no_overlap(mappings),
        !candidate_mapping_overlaps_existing_pmem(mappings, pte),
    ensures
        pmem_no_overlap(mappings.insert(base, pte)),
{
    assert(forall|bs1: nat|
        #![auto]
        mappings.dom().contains(bs1) ==> !overlap(pte.frame, mappings.index(bs1).frame));
    assert(pmem_no_overlap(mappings.insert(base, pte)));
}

pub proof fn insert_non_map_preserves_unique(
    thread_state: Map<nat, ThreadState>,
    base: nat,
    arg: ThreadState,
)
    requires
        inflight_maps_unique(thread_state),
        !(arg is Map),
    ensures
        inflight_maps_unique(thread_state.insert(base, arg)),
{
    let args = thread_state.insert(base, arg);
    assert forall|id: nat| #[trigger] args.dom().contains(id) implies if_map_then_unique(
        args,
        id,
    ) by {
        if id != base {
            if let ThreadState::Map { vaddr, pte } = thread_state.index(id) {
                assert(args.remove(id) == thread_state.remove(id).insert(base, arg));
            } 
        }
    }
}

pub proof fn insert_map_preserves_unique(
    thread_state: Map<nat, ThreadState>,
    thread_id: nat,
    vaddr: nat,
    pte: PTE,
)
    requires
        inflight_maps_unique(thread_state),
        !candidate_mapping_overlaps_inflight_pmem(thread_state.values(), pte),
    ensures
        inflight_maps_unique(thread_state.insert(thread_id, ThreadState::Map { vaddr, pte })),
{
    let arg = ThreadState::Map { vaddr, pte };
    let args = thread_state.insert(thread_id, arg);
    let p = pte;
    assert forall|id: nat| #[trigger] args.dom().contains(id) implies if_map_then_unique(args, id)
    by {
        if id == thread_id {
            assert forall|other_id: nat| #[trigger]
                thread_state.dom().contains(other_id) implies arg != thread_state.index(
                other_id,
            ) by {
                if let ThreadState::Map { vaddr: x, pte: y } = thread_state.index(
                    other_id,
                ) {
                    assert(thread_state.values().contains(
                        ThreadState::Map { vaddr: x, pte: y },
                    ));
                    assert(!overlap(pte.frame, y.frame));
                } 
            }
        } else {
            if let ThreadState::Map { vaddr: x, pte: y } = thread_state.index(id) {
                assert(thread_state.dom().contains(id));
                assert(thread_state.values().contains(
                    ThreadState::Map { vaddr: x, pte: y },
                ));
                assert(!overlap(pte.frame, y.frame));
                assert(args.index(id) != arg);
                assert(args.remove(id) == thread_state.remove(id).insert(thread_id, arg));
            } 
        }
    }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                               //
//                                        Step preserves inv proofs                                              //
//                                                                                                               //
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn unmap_start_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_UnmapStart(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.dom().contains(lbl->UnmapStart_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
{
    let vaddr = lbl->UnmapStart_vaddr;
    let thread_id = lbl->UnmapStart_thread_id;
    if s2.sound {
        assert(forall|id: nat| #![auto] s2.mappings.dom().contains(id) ==> s1.mappings[id] == s2.mappings[id]);
        let pte = if s1.mappings.dom().contains(vaddr) { Some(s1.mappings[vaddr]) } else { Option::None };
        assert(s2.thread_state.values().subset_of(s1.thread_state.values().insert(ThreadState::Unmap { vaddr, pte })));
        insert_non_map_preserves_unique(s1.thread_state, thread_id, ThreadState::Unmap { vaddr, pte });
    } 
}

pub proof fn map_start_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_MapStart(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.dom().contains(lbl->MapStart_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
{
    let thread_id = lbl->MapStart_thread_id;
    let vaddr = lbl->MapStart_vaddr;
    let pte = lbl->MapStart_pte;
    if s2.sound {
        assert(forall|id: nat| #![auto] s2.mappings.dom().contains(id) ==> s1.mappings[id] == s2.mappings[id]);
        assert(s2.thread_state.values().subset_of(s1.thread_state.values().insert(ThreadState::Map { vaddr, pte })));
        insert_map_preserves_unique(s1.thread_state, thread_id, vaddr, pte);
    } 
}

pub proof fn map_end_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_MapEnd(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.contains_key(lbl->MapEnd_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
{
    let thread_id = lbl->MapEnd_thread_id;
    let result = lbl->MapEnd_result;
    if let ThreadState::Map { vaddr, pte } = s1.thread_state.index(thread_id) {
        assert(s2.thread_state.values().subset_of(
            s1.thread_state.values().insert(ThreadState::Idle),
        ));
        insert_non_map_preserves_unique(s1.thread_state, thread_id, ThreadState::Idle);
        if result is Ok {
            assert(s1.thread_state.values().contains(ThreadState::Map { vaddr, pte }));
            assert(s2.thread_state == s1.thread_state.remove(thread_id).insert(
                thread_id,
                ThreadState::Idle,
            ));
        } 
    } 
}
} // verus!
