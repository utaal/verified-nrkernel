use vstd::pervasive::arbitrary;
use vstd::prelude::*;

use crate::spec_t::mmu::defs::{
    aligned, axiom_max_phyaddr_width_facts, candidate_mapping_in_bounds, x86_arch_spec_upper_bound,
    Flags, LoadResult, MemRegion, PTE, MemOp, StoreResult, MAX_PHYADDR_SPEC,
    update_range,
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
    // reveal_with_fuel(seq_update_range, 5);

    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants { thread_no: 4, phys_mem_size: 4096 * 4096 };

    let s1 = State {
        mem: seq![arbitrary(); crate::spec_t::mmu::defs::MAX_BASE],
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

    // let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let mem3 = s2.mem;
    let s3 = State {
        thread_state: s2.thread_state.insert(1, ThreadState::Idle),
        mappings: s2.mappings.insert(4096 * 3, pte1),
        mem: mem3,
        ..s2
    };
    // assert(s3.mem.dom() == s2.mem.dom().union(
    //     Set::new(
    //         |w: nat|
    //             crate::spec_t::mmu::defs::word_index_spec(4096 * 3) <= w
    //                 < crate::spec_t::mmu::defs::word_index_spec(4096 * 3) + (4096nat / WORD_SIZE as nat),
    //     ),
    // ));

    assert(s3.mappings.contains_pair(4096 * 3, pte1));  // discharge exists in `mem_domain_from_mappings_contains`
    // assert(s3.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s3.mappings));

    let s2s3rlbl = RLbl::MapEnd { thread_id: 1, vaddr: 4096 * 3, result: Ok(()) };
    assert(next_step(c, s2, s3, Step::MapEnd, s2s3rlbl));

    let s4 = State { mem: update_range(s3.mem, 4096 * 3 as int, seq![42, 0, 0, 0]), ..s3 };

    let s3s4op = MemOp::Store { new_value: seq![42, 0, 0, 0], result: StoreResult::Ok };
    assert(s3s4op.op_size() == 4);

    assert(next_step(
        c,
        s3,
        s4,
        Step::MemOp { pte: Some((4096 * 3, pte1)) },
        RLbl::MemOp {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: s3s4op,
        },
    ));

    let s5 = s4;

    assert(s4.mem.subrange(4096 * 3 as int, 4096 * 3 + 4 as int) == seq![42u8, 0, 0, 0]);
    let s4s5op = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![42, 0, 0, 0]) };
    assert(s4s5op.op_size() == 4);

    assert(next_step(
        c,
        s4,
        s5,
        Step::MemOp { pte: Some((4096 * 3, pte1)) },
        RLbl::MemOp {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: s4s5op,
        },
    ));

    // let mem6 = lemma_contract_mem_domain(s5.mem, 4096 * 3, 4096);
    let mem6 = s5.mem;
    let s6 = State {
        thread_state: s5.thread_state.insert(
            2,
            ThreadState::Unmap { vaddr: 4096 * 3, pte: Some(pte1) },
        ),
        mappings: s5.mappings.remove(4096 * 3),
        mem: mem6,
        ..s5
    };

    // assert(s6.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s6.mappings));
    assert(next_step(c, s5, s6, Step::UnmapStart, RLbl::UnmapStart { thread_id: 2, vaddr: 4096 * 3 }));

}

mod util {

    use super::*;

    pub open spec fn all_bytes_in_range(vaddr: nat, size: nat) -> Set<nat>
        decreases size,
        // via all_bytes_in_range_decreases
    {
        if size > 0 {
            all_bytes_in_range((vaddr + 1) as nat, (size - 1) as nat).insert(vaddr)
        } else {
            Set::empty()
        }
    }
    
    // pub open spec fn seq_update_range(s: Seq<u8>, i: int, v: Seq<u8>) -> (r: Seq<u8>)
    //     recommends
    //         0 <= i <= s.len() as int,
    //     decreases v.len(),
    // {
    //     if v.len() == 0 {
    //         s
    //     } else {
    //         let r = seq_update_range(s, i + 1, v.skip(1));
    //         let r = r.update(i, v[0]);
    //         r
    //     }
    // }

    // #[via_fn]
    // proof fn all_bytes_in_range_decreases(vaddr: nat, size: nat) {
    //     assert(aligned(size, WORD_SIZE as nat));
    //     if size > 0 {
    //         if size - WORD_SIZE >= 0 {
    //         } else {
    //             assert(0 < size < WORD_SIZE);
    //             broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
    //             assert(false);
    //         }
    //     } else {
    //     }
    // }

    // pub proof fn lemma_extend_mem_domain(map: Seq<u8>, vaddr: nat, size: nat) -> (r: Seq<u8>)
    //     requires
    //         aligned(vaddr, WORD_SIZE as nat),
    //         aligned(size, WORD_SIZE as nat),
    //     ensures
    //         r.dom() =~= map.dom() + all_bytes_in_range(vaddr, size),
    //         r.dom() =~= map.dom().union(Set::new(|w: nat| vaddr <= w < vaddr + size)),
    //     decreases size,
    // {
    //     if size > 0 {
    //         assert(aligned(size, WORD_SIZE as nat));
    //         if size - WORD_SIZE >= 0 {
    //         } else {
    //             assert(0 < size < WORD_SIZE);
    //             broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
    //             assert(false);
    //         }
    //         assert(aligned((vaddr + WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
    //             requires
    //                 aligned(vaddr, WORD_SIZE as nat),
    //         {}
    //         assert(aligned((size - WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
    //             requires
    //                 aligned(size, WORD_SIZE as nat),
    //                 size > 0,
    //         {}
    //         let extended = lemma_extend_mem_domain(
    //             map,
    //             (vaddr + WORD_SIZE) as nat,
    //             (size - WORD_SIZE) as nat,
    //         );
    //         let r = extended.insert(vaddr, arbitrary());
    //         r
    //     } else {
    //         map
    //     }
    // }

    // pub proof fn lemma_contract_mem_domain(map: Seq<u8>, vaddr: nat, size: nat) -> (r: Map<
    //     nat,
    //     nat,
    // >)
    //     requires
    //         aligned(vaddr, WORD_SIZE as nat),
    //         aligned(size, WORD_SIZE as nat),
    //     ensures
    //         r.dom() =~= map.dom() - all_bytes_in_range(vaddr, size),
    //         r.dom() =~= map.dom().difference(Set::new(|w: nat| vaddr <= w < vaddr + size)),
    //     decreases size,
    // {
    //     if size > 0 {
    //         assert(aligned(size, WORD_SIZE as nat));
    //         if size - WORD_SIZE >= 0 {
    //         } else {
    //             assert(0 < size < WORD_SIZE);
    //             broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;
    //             assert(false);
    //         }
    //         assert(aligned((vaddr + WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
    //             requires
    //                 aligned(vaddr, WORD_SIZE as nat),
    //         {}
    //         assert(aligned((size - WORD_SIZE) as nat, WORD_SIZE as nat)) by (nonlinear_arith)
    //             requires
    //                 aligned(size, WORD_SIZE as nat),
    //                 size > 0,
    //         {}
    //         let contracted = lemma_contract_mem_domain(
    //             map,
    //             (vaddr + WORD_SIZE) as nat,
    //             (size - WORD_SIZE) as nat,
    //         );
    //         let r = contracted.remove(vaddr);
    //         r
    //     } else {
    //         map
    //     }
    // }

}

proof fn get_frame(n: nat, size: nat) -> (m: MemRegion)
    requires size < 106_496,
    ensures m == (MemRegion { base: 106_496 * n, size: 4096 })
{
    MemRegion { base: 106_496 * n, size: 4096 }
}

#[verifier::rlimit(10000)]
proof fn program_threads_10() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants { thread_no: 4, phys_mem_size: 8_192_000 };

    let s1 = State {
        mem: seq![arbitrary(); crate::spec_t::mmu::defs::MAX_BASE],
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

    let mem3 = s2.mem;
    let s3 = State {
        thread_state: s2.thread_state.insert(1, ThreadState::Idle),
        mappings: s2.mappings.insert(pte1_vaddr, pte1),
        mem: mem3,
        ..s2
    };

    assert(s3.mappings.contains_pair(pte1_vaddr, pte1));  // discharge exists in `mem_domain_from_mappings_contains`

    let s2s3rlbl = RLbl::MapEnd { thread_id: 1, vaddr: pte1_vaddr, result: Ok(()) };
    assert(next_step(c, s2, s3, Step::MapEnd, s2s3rlbl));

    // sync point
    
    let mut threads = set![0nat, 1, 2, 3];
    let all_threads = threads;
    assert(threads.contains(0));
    let s4 = {
        let which_thread = threads.choose();
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let s4 = State { mem: update_range(s3.mem, pte1_vaddr + (which_thread * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s3 };

        let s3s4op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s3s4op.op_size() == 4);
        assert(next_step(
            c,
            s3,
            s4,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: s3s4op,
            },
        ));
        threads = threads.remove(which_thread);
        assert(threads <= all_threads);
        assert(forall|t| all_threads.contains(t) ==> t < 4);

        s4
    };

    let s5 = {
        assert(threads.len() == 3);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s4.mappings.contains_pair(pte1_vaddr, pte1));

        let s5 = State { mem: update_range(s4.mem, pte1_vaddr + (which_thread * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s4 };

        let s4s5op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s4s5op.op_size() == 4);
        assert(next_step(
            c,
            s4,
            s5,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: s4s5op,
            },
        ));
        threads = threads.remove(which_thread);
        s5
    };

    let s6 = {
        assert(threads.len() == 2);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s4.mappings.contains_pair(pte1_vaddr, pte1));

        let s6 = State { mem: update_range(s5.mem, pte1_vaddr + (which_thread * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s5 };

        let s5s6op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s5s6op.op_size() == 4);
        assert(next_step(
            c,
            s5,
            s6,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: s5s6op,
            },
        ));
        threads = threads.remove(which_thread);
        s6
    };

    let s7 = {
        assert(threads.len() == 1);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let s7 = State { mem: update_range(s6.mem, pte1_vaddr + (which_thread * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s6 };

        let s6s7op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s6s7op.op_size() == 4);
        assert(next_step(
            c,
            s6,
            s7,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: s6s7op,
            },
        ));
        threads = threads.remove(which_thread);
        s7
    };

    assert(threads.len() == 0);

    // sync point
    
    assert(s7.mem.subrange(pte1_vaddr + (0 * 4) as int, pte1_vaddr + (0 * 4) + 4 as int) == seq![0u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (1 * 4) as int, pte1_vaddr + (1 * 4) + 4 as int) == seq![1u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (2 * 4) as int, pte1_vaddr + (2 * 4) + 4 as int) == seq![2u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (3 * 4) as int, pte1_vaddr + (3 * 4) + 4 as int) == seq![3u8, 0, 0, 0]);
    
    let s_sync_2 = s7;
    
    let mut threads = set![0nat, 1, 2, 3];
    let all_threads = threads;
    let v0 = {
        assert(threads.len() == 4);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![which_thread as u8, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: v0rop,
            },
        ));
        threads = threads.remove(which_thread);
        which_thread as u8
    };

    let v1 = {
        assert(threads.len() == 3);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![which_thread as u8, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: v0rop,
            },
        ));
        threads = threads.remove(which_thread);
        which_thread as u8
    };

    let v2 = {
        assert(threads.len() == 2);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![which_thread as u8, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: v0rop,
            },
        ));
        threads = threads.remove(which_thread);
        which_thread as u8
    };

    let v3 = {
        assert(threads.len() == 1);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 4);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![which_thread as u8, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + (which_thread * 4),
                op: v0rop,
            },
        ));
        threads = threads.remove(which_thread);
        which_thread as u8
    };

    assert(threads.len() == 0);
    
    assert(set![v0, v1, v2, v3] == set![0u8, 1, 2, 3]);

    assert(v0 + v1 + v2 + v3 == 6);
}

} // verus!
