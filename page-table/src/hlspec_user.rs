use vstd::prelude::*;

use crate::spec_t::mmu::defs::{
    aligned, axiom_max_phyaddr_width_facts, candidate_mapping_in_bounds, x86_arch_spec_upper_bound,
    Flags, LoadResult, MemRegion, PTE, MemOp, StoreResult, MAX_PHYADDR_SPEC, WORD_SIZE,
    word_index_spec,
};
use crate::spec_t::hlspec::*;
use crate::theorem::RLbl;

verus! {

pub proof fn lemma_max_phyaddr_at_least()
    ensures
        MAX_PHYADDR_SPEC >= 0xffffffff,
{
    axiom_max_phyaddr_width_facts();

    assert((1u64 << 32) - 1u64 == 0xffffffff) by (compute);
    assert(forall|m: u64, n: u64| n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
}

use util::*;

proof fn program_1() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants { thread_no: 4, phys_mem_size: 4096 * 4096 };

    let s1 = State {
        mem: Map::empty(),
        thread_state:
            map![
            0 => ThreadState::Idle,
            1 => ThreadState::Idle,
            2 => ThreadState::Idle,
            3 => ThreadState::Idle,
        ],
        mappings: Map::empty(),
        sound: true,
    };

    assert(wf(c, s1));
    assert(init(c, s1));

    let pte1 = PTE {
        frame: MemRegion { base: 4096, size: 4096 },
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(set![], s1.mappings, 4096 * 3, pte1));

    let s2 = State {
        thread_state: s1.thread_state.insert(
            1,
            ThreadState::Map { vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s1
    };

    // assert(step_Map_start(c, s1, s2, 1, 4096 * 3, pte1));
    let s1s2rlbl = RLbl::MapStart { thread_id: 1, vaddr: 4096 * 3, pte: pte1 };
    assert(next_step(
        c,
        s1,
        s2,
        Step::MapStart,
        s1s2rlbl,
    ));
    assert(next(c, s1, s2, s1s2rlbl));

    let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let s3 = State {
        thread_state: s2.thread_state.insert(1, ThreadState::Idle),
        mappings: s2.mappings.insert(4096 * 3, pte1),
        mem: mem3,
        ..s2
    };
    assert(s3.mem.dom() == s2.mem.dom().union(
        Set::new(
            |w: nat|
                crate::spec_t::mmu::defs::word_index_spec(4096 * 3) <= w
                    < crate::spec_t::mmu::defs::word_index_spec(4096 * 3) + (4096nat / WORD_SIZE as nat),
        ),
    ));

    assert(s3.mappings.contains_pair(4096 * 3, pte1));  // discharge exists in `mem_domain_from_mappings_contains`
    assert(s3.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s3.mappings));

    let s2s3rlbl = RLbl::MapEnd { thread_id: 1, vaddr: 4096 * 3, result: Ok(()) };
    assert(next_step(c, s2, s3, Step::MapEnd, s2s3rlbl));

    let s4 = State { mem: s3.mem.insert(512 * 3, 42), ..s3 };

    assert(crate::spec_t::mmu::defs::word_index_spec(4096 * 3) == 512 * 3) by (nonlinear_arith){
        assert(aligned(4096 * 3, WORD_SIZE as nat));
    }
    assert(next_step(
        c,
        s3,
        s4,
        Step::MemOp { pte: Some((4096 * 3, pte1)) },
        RLbl::MemOp {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: MemOp::Store { new_value: 42, result: StoreResult::Ok },
        },
    ));

    let s5 = s4;
    assert(next_step(
        c,
        s4,
        s5,
        Step::MemOp { pte: Some((4096 * 3, pte1)) },
        RLbl::MemOp {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: MemOp::Load { is_exec: false, result: LoadResult::Value(42) },
        },
    ));

    let mem6 = lemma_contract_mem_domain(s5.mem, 4096 * 3, 4096);
    let s6 = State {
        thread_state: s5.thread_state.insert(
            2,
            ThreadState::Unmap { vaddr: 4096 * 3, pte: Some(pte1) },
        ),
        mappings: s5.mappings.remove(4096 * 3),
        mem: mem6,
        ..s5
    };
    // assume(false);  //TODO

    assert(s6.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s6.mappings));
    assert(next_step(c, s5, s6, Step::UnmapStart, RLbl::UnmapStart { thread_id: 2, vaddr: 4096 * 3 }));

}

mod util {
    use super::*;

    pub open spec fn all_words_in_range(vaddr: nat, size: nat) -> Set<nat>
        recommends
            aligned(vaddr, WORD_SIZE as nat),
            aligned(size, WORD_SIZE as nat),
        decreases size,
        when aligned(size, WORD_SIZE as nat)
        via all_words_in_range_decreases
    {
        if size > 0 {
            all_words_in_range((vaddr + WORD_SIZE) as nat, (size - WORD_SIZE) as nat).insert(
                crate::spec_t::mmu::defs::word_index_spec(vaddr),
            )
        } else {
            Set::empty()
        }
    }

    #[via_fn]
    proof fn all_words_in_range_decreases(vaddr: nat, size: nat) {
        assert(aligned(size, WORD_SIZE as nat));
        if size > 0 {
            if size - WORD_SIZE >= 0 {
            } else {
                assert(0 < size < WORD_SIZE);
                broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
                assert(false);
            }
        } else {
        }
    }

    pub proof fn lemma_extend_mem_domain(map: Map<nat, nat>, vaddr: nat, size: nat) -> (r: Map<
        nat,
        nat,
    >)
        requires
            aligned(vaddr, WORD_SIZE as nat),
            aligned(size, WORD_SIZE as nat),
        ensures
            r.dom() =~= map.dom() + all_words_in_range(vaddr, size),
            r.dom() =~= map.dom().union(
                Set::new(
                    |w: nat|
                        crate::spec_t::mmu::defs::word_index_spec(vaddr) <= w
                            < crate::spec_t::mmu::defs::word_index_spec(vaddr) + (size
                            / WORD_SIZE as nat),
                ),
            ),
        decreases size,
    {
        if size > 0 {
            assert(aligned(size, WORD_SIZE as nat));
            if size - WORD_SIZE >= 0 {
            } else {
                assert(0 < size < WORD_SIZE);
                broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
                assert(false);
            }
            assert(aligned((vaddr + WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
                requires
                    aligned(vaddr, WORD_SIZE as nat),
            {}
            assert(aligned((size - WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
                requires
                    aligned(size, WORD_SIZE as nat),
                    size > 0,
            {}
            let extended = lemma_extend_mem_domain(
                map,
                (vaddr + WORD_SIZE) as nat,
                (size - WORD_SIZE) as nat,
            );
            let r = extended.insert(crate::spec_t::mmu::defs::word_index_spec(vaddr), arbitrary());
            r
        } else {
            map
        }
    }

    pub proof fn lemma_contract_mem_domain(map: Map<nat, nat>, vaddr: nat, size: nat) -> (r: Map<
        nat,
        nat,
    >)
        requires
            aligned(vaddr, WORD_SIZE as nat),
            aligned(size, WORD_SIZE as nat),
        ensures
            r.dom() =~= map.dom() - all_words_in_range(vaddr, size),
            r.dom() =~= map.dom().difference(
                Set::new(
                    |w: nat|
                        crate::spec_t::mmu::defs::word_index_spec(vaddr) <= w
                            < crate::spec_t::mmu::defs::word_index_spec(vaddr) + (size
                            / WORD_SIZE as nat),
                ),
            ),
        decreases size,
    {
        if size > 0 {
            assert(aligned(size, WORD_SIZE as nat));
            if size - WORD_SIZE >= 0 {
            } else {
                assert(0 < size < WORD_SIZE);
                broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
                assert(false);
            }
            assert(aligned((vaddr + WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
                requires
                    aligned(vaddr, WORD_SIZE as nat),
            {}
            assert(aligned((size - WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
                requires
                    aligned(size, WORD_SIZE as nat),
                    size > 0,
            {}
            let contracted = lemma_contract_mem_domain(
                map,
                (vaddr + WORD_SIZE) as nat,
                (size - WORD_SIZE) as nat,
            );
            let r = contracted.remove(crate::spec_t::mmu::defs::word_index_spec(vaddr));
            r
        } else {
            map
        }
    }

}

proof fn get_frame(n: nat, size: nat) -> (m: MemRegion)
    requires size < 106_496,
    ensures m == (MemRegion { base: 106_496 * n, size: 4096 })
{
    MemRegion { base: 106_496 * n, size: 4096 }
}

proof fn program_threads_10() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants { thread_no: 4, phys_mem_size: 8_192_000 };

    let s1 = State {
        mem: Map::empty(),
        thread_state:
            map![
            0 => ThreadState::Idle,
            1 => ThreadState::Idle,
            2 => ThreadState::Idle,
            3 => ThreadState::Idle,
        ],
        mappings: Map::empty(),
        sound: true,
    };

    assert(wf(c, s1));
    assert(init(c, s1));

    let pte1_memregion = get_frame(0, 4096);
    let pte1 = PTE {
        frame: pte1_memregion,
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    let pte1_vaddr = 4_096_000;
    let s2 = State {
        thread_state: s1.thread_state.insert(
            1,
            ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 },
        ),
        ..s1
    };

    let s1s2rlbl = RLbl::MapStart { thread_id: 1, vaddr: pte1_vaddr, pte: pte1 };
    assert(next_step(
        c,
        s1,
        s2,
        Step::MapStart,
        s1s2rlbl,
    ));

    let mem3 = lemma_extend_mem_domain(s2.mem, pte1_vaddr, 4096);
    let s3 = State {
        thread_state: s2.thread_state.insert(1, ThreadState::Idle),
        mappings: s2.mappings.insert(pte1_vaddr, pte1),
        mem: mem3,
        ..s2
    };
    assert(s3.mem.dom() == s2.mem.dom().union(
        Set::new(
            |w: nat|
                crate::spec_t::mmu::defs::word_index_spec(pte1_vaddr) <= w
                    < crate::spec_t::mmu::defs::word_index_spec(pte1_vaddr) + (4096nat / WORD_SIZE as nat),
        ),
    ));

    assert(s3.mappings.contains_pair(pte1_vaddr, pte1));  // discharge exists in `mem_domain_from_mappings_contains`
    assert(s3.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s3.mappings));

    let s2s3rlbl = RLbl::MapEnd { thread_id: 1, vaddr: pte1_vaddr, result: Ok(()) };
    assert(next_step(c, s2, s3, Step::MapEnd, s2s3rlbl));

    // sync point
    
    let mut threads = set![0nat, 1, 2, 3];
    assert(threads.contains(0));
    let which_thread1 = choose|t: nat| threads.contains(t);
    assert(which_thread1 < 4);

    let s4 = State { mem: s3.mem.insert(word_index_spec(pte1_vaddr + (which_thread1 * WORD_SIZE) as nat), which_thread1), ..s3 };

    // assert(crate::spec_t::mmu::defs::word_index_spec(pte1_vaddr + (which_thread1 * 8)) == 512 * 3) by (nonlinear_arith){
    //     assert(aligned(4096 * 3, WORD_SIZE as nat));
    // }
    assert(next_step(
        c,
        s3,
        s4,
        Step::MemOp { pte: Some((pte1_vaddr + (which_thread1 * WORD_SIZE) as nat, pte1)) },
        RLbl::MemOp {
            thread_id: which_thread1,
            vaddr: pte1_vaddr + (which_thread1 * 8),
            op: MemOp::Store { new_value: 42, result: StoreResult::Ok },
        },
    ));

    //let s2 = choose|s2: State| {
    //    ||| step_MemOp(
    //}
    
}

} // verus!
