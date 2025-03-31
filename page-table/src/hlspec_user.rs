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
    ensures m == (MemRegion { base: 106_496 * n, size })
{
    MemRegion { base: 106_496 * n, size }
}

#[verifier::rlimit(10000)]
proof fn program_threads_4() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = Constants { thread_no: 5, phys_mem_size: 8_192_000 };

    let s1 = State {
        mem: seq![arbitrary(); crate::spec_t::mmu::defs::MAX_BASE],
        thread_state:
            map![
            0 => ThreadState::Idle,
            1 => ThreadState::Idle,
            2 => ThreadState::Idle,
            3 => ThreadState::Idle,
            4 => ThreadState::Idle,
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

    let pte1_vaddr = 549_755_813_888;
    let s2 = State {
        thread_state: s1.thread_state.insert(
            0,
            ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 },
        ),
        ..s1
    };

    let s1s2rlbl = RLbl::MapStart { thread_id: 0, vaddr: pte1_vaddr, pte: pte1 };
    assert(next_step(
        c,
        s1,
        s2,
        Step::MapStart,
        s1s2rlbl,
    ));

    let mem3 = s2.mem;
    let s3 = State {
        thread_state: s2.thread_state.insert(0, ThreadState::Idle),
        mappings: s2.mappings.insert(pte1_vaddr, pte1),
        mem: mem3,
        ..s2
    };

    assert(s3.mappings.contains_pair(pte1_vaddr, pte1));  // discharge exists in `mem_domain_from_mappings_contains`

    let s2s3rlbl = RLbl::MapEnd { thread_id: 0, vaddr: pte1_vaddr, result: Ok(()) };
    assert(next_step(c, s2, s3, Step::MapEnd, s2s3rlbl));

    // sync point
    
    let mut threads = set![1nat, 2, 3, 4];
    let all_threads = threads;
    assert(threads <= all_threads);
    assert(forall|t| all_threads.contains(t) ==> t < 5);
    let s4 = {
        assert(threads.len() == 4);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 5);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let s4 = State { mem: update_range(s3.mem, pte1_vaddr + ((which_thread - 1) * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s3 };

        let s3s4op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s3s4op.op_size() == 4);
        assert(next_step(
            c,
            s3,
            s4,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + ((which_thread - 1) * 4) as nat,
                op: s3s4op,
            },
        ));
        threads = threads.remove(which_thread);
        assert(threads <= all_threads);
        assert(forall|t| all_threads.contains(t) ==> t < 5);

        s4
    };

    let s5 = {
        assert(threads.len() == 3);
        let which_thread = threads.choose();
        assert(threads.contains(which_thread));
        assert(which_thread < 5);
        
        assert(s4.mappings.contains_pair(pte1_vaddr, pte1));

        let s5 = State { mem: update_range(s4.mem, pte1_vaddr + ((which_thread - 1) * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s4 };

        let s4s5op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s4s5op.op_size() == 4);
        assert(next_step(
            c,
            s4,
            s5,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + ((which_thread - 1) * 4) as nat,
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
        assert(which_thread < 5);
        
        assert(s4.mappings.contains_pair(pte1_vaddr, pte1));

        let s6 = State { mem: update_range(s5.mem, pte1_vaddr + ((which_thread - 1) * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s5 };

        let s5s6op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s5s6op.op_size() == 4);
        assert(next_step(
            c,
            s5,
            s6,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + ((which_thread - 1) * 4) as nat,
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
        assert(which_thread < 5);
        
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let s7 = State { mem: update_range(s6.mem, pte1_vaddr + ((which_thread - 1) * 4) as int, seq![which_thread as u8, 0, 0, 0]), ..s6 };

        let s6s7op = MemOp::Store { new_value: seq![which_thread as u8, 0, 0, 0], result: StoreResult::Ok };
        assert(s6s7op.op_size() == 4);
        assert(next_step(
            c,
            s6,
            s7,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: which_thread,
                vaddr: pte1_vaddr + ((which_thread - 1) * 4) as nat,
                op: s6s7op,
            },
        ));
        threads = threads.remove(which_thread);
        s7
    };

    assert(threads.len() == 0);

    // sync point
    
    assert(s7.mem.subrange(pte1_vaddr + (0 * 4) as int, pte1_vaddr + (0 * 4) + 4 as int) == seq![1u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (1 * 4) as int, pte1_vaddr + (1 * 4) + 4 as int) == seq![2u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (2 * 4) as int, pte1_vaddr + (2 * 4) + 4 as int) == seq![3u8, 0, 0, 0]);
    assert(s7.mem.subrange(pte1_vaddr + (3 * 4) as int, pte1_vaddr + (3 * 4) + 4 as int) == seq![4u8, 0, 0, 0]);
    
    let s_sync_2 = s7;
    
    let v0 = {
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v: u8 = 1;
        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![v, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: 0,
                vaddr: pte1_vaddr + (0 * 4),
                op: v0rop,
            },
        ));
        v
    };

    let v1 = {
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v: u8 = 2;
        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![v, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: 1,
                vaddr: pte1_vaddr + (1 * 4),
                op: v0rop,
            },
        ));
        v
    };

    let v2 = {
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v: u8 = 3;
        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![v, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: 2,
                vaddr: pte1_vaddr + (2 * 4),
                op: v0rop,
            },
        ));
        v
    };

    let v3 = {
        assert(s3.mappings.contains_pair(pte1_vaddr, pte1));

        let v: u8 = 4;
        let v0rop = MemOp::Load { is_exec: false, size: 4, result: LoadResult::Value(seq![v, 0, 0, 0]) };
        assert(next_step(
            c,
            s_sync_2,
            s_sync_2,
            Step::MemOp { pte: Some((pte1_vaddr, pte1)) },
            RLbl::MemOp {
                thread_id: 3,
                vaddr: pte1_vaddr + (3 * 4),
                op: v0rop,
            },
        ));
        v
    };

    assert(v0 + v1 + v2 + v3 == 10);
}

mod program_two {
    use super::*;

    pub enum MapTransition {
        T1MapStart,
        T1MapEnd,
        T2MapStart,
        T2MapEnd,
    }
    
    spec fn pending_inv(pending: Set<MapTransition>) -> bool {
        &&& pending.contains(MapTransition::T1MapStart) ==> pending.contains(MapTransition::T1MapEnd)
        &&& pending.contains(MapTransition::T2MapStart) ==> pending.contains(MapTransition::T2MapEnd)
        &&& !pending.is_empty() ==> exists|t| pending_enabled(pending, t)
    }
    
    spec(checked) fn pending_enabled(pending: Set<MapTransition>, t: MapTransition) -> bool
        // recommends pending_inv(pending),
    {
        &&& pending.contains(t)
        &&& match t {
            MapTransition::T1MapStart => true,
            MapTransition::T1MapEnd => !pending.contains(MapTransition::T1MapStart),
            MapTransition::T2MapStart => true,
            MapTransition::T2MapEnd => !pending.contains(MapTransition::T2MapStart),
        }
    }

    spec const pte1_memregion: MemRegion = MemRegion { base: 106_496 * 0, size: 4096 };
    spec const pte2_memregion: MemRegion = MemRegion { base: 106_496 * 2, size: 4096 };

    spec const pte1_vaddr: nat = 549_755_813_888;
    spec const pte2_vaddr: nat = 549_755_813_888 + 4096;

    spec const pte1: PTE = PTE {
        frame: pte1_memregion,
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };
    spec const pte2: PTE = PTE {
        frame: pte2_memregion,
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    spec const t1_map_start_rlbl: RLbl = RLbl::MapStart { thread_id: 0, vaddr: pte1_vaddr, pte: pte1 };
    spec const t2_map_start_rlbl: RLbl = RLbl::MapStart { thread_id: 1, vaddr: pte2_vaddr, pte: pte2 };
    spec const t1_map_end_rlbl: RLbl = RLbl::MapEnd { thread_id: 0, vaddr: pte1_vaddr, result: Ok(()) };
    spec const t2_map_end_rlbl: RLbl = RLbl::MapEnd { thread_id: 1, vaddr: pte2_vaddr, result: Ok(()) };
    
    spec fn transition_to_rlbl(t: MapTransition) -> RLbl {
        match t {
            MapTransition::T1MapStart => t1_map_start_rlbl,
            MapTransition::T1MapEnd => t1_map_end_rlbl,
            MapTransition::T2MapStart => t2_map_start_rlbl,
            MapTransition::T2MapEnd => t2_map_end_rlbl,
        }
    }
    
    spec fn t1_map_start_step(c: Constants, s1: State) -> (s2: State) {
        State { thread_state: s1.thread_state.insert(0, ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 },), ..s1 }
    }

    spec fn t2_map_start_step(c: Constants, s1: State) -> (s2: State) {
        State { thread_state: s1.thread_state.insert(1, ThreadState::Map { vaddr: pte2_vaddr, pte: pte2},), ..s1 }
    }

    spec fn t1_map_end_step(c: Constants, s1: State) -> (s2: State) {
        State { thread_state: s1.thread_state.insert(0, ThreadState::Idle,), ..s1 }
    }

    spec fn t2_map_end_step(c: Constants, s1: State) -> (s2: State) {
        State { thread_state: s1.thread_state.insert(1, ThreadState::Idle,), ..s1 }
    }
    
    spec fn map_next(
        c: Constants,
        s: State,
        pending: Set<MapTransition>,
    ) -> (MapTransition, State, Set<MapTransition>)
        recommends
            pending_inv(pending),
            !pending.is_empty(),
    {
        let t = choose|t| pending_enabled(pending, t);
        let s2 = match t {
            MapTransition::T1MapStart => t1_map_start_step(c, s),
            MapTransition::T1MapEnd => t1_map_end_step(c, s),
            MapTransition::T2MapStart => t2_map_start_step(c, s),
            MapTransition::T2MapEnd => t2_map_end_step(c, s),
        };
        let pending = pending.remove(t);
        (t, s2, pending)
    }
    
    spec fn map_inv(c: Constants, s: State, pending: Set<MapTransition>) -> bool {
        &&& s.sound
        &&& forall|n: nat| n < c.thread_no ==> s.thread_state.contains_key(n)
        &&& if pending.contains(MapTransition::T1MapStart) { s.thread_state[0] == ThreadState::Idle } else {
            pending.contains(MapTransition::T1MapEnd) ==> s.thread_state[0] == ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 }
        }
        &&& if pending.contains(MapTransition::T2MapStart) { s.thread_state[1] == ThreadState::Idle } else {
            pending.contains(MapTransition::T2MapEnd) ==> s.thread_state[1] == ThreadState::Map { vaddr: pte2_vaddr, pte: pte2 }
        }
        &&& s.thread_state[0] == ThreadState::Idle || s.thread_state[0] == ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 }
        &&& s.thread_state[1] == ThreadState::Idle || s.thread_state[1] == ThreadState::Map { vaddr: pte2_vaddr, pte: pte2 }
        &&& s.mappings == (
            if !pending.contains(MapTransition::T1MapEnd) { map![pte1_vaddr => pte1] } else { Map::empty() }.union_prefer_right(
            if !pending.contains(MapTransition::T2MapEnd) { map![pte2_vaddr => pte2] } else { Map::empty() })
        )
    }
    
    proof fn map_next_ensures(
        c: Constants,
        s1: State,
        s2: State,
        pending1: Set<MapTransition>,
        pending2: Set<MapTransition>,
        t: MapTransition,
    )
        requires
            c == (Constants { thread_no: 2, phys_mem_size: 8_192_000 }),
            map_inv(c, s1, pending1),
            pending1.finite(),
            !pending1.is_empty(),
            pending_inv(pending1),
            map_next(c, s1, pending1) == (t, s2, pending2),
        ensures
            pending2.finite(),
            pending_enabled(pending1, t),
            pending_inv(pending2),
            map_inv(c, s2, pending2),
            next(c, s1, s2, transition_to_rlbl(t)),
    {
        lemma_max_phyaddr_at_least();
        x86_arch_spec_upper_bound();

        if pending1.len() == 0 {
            assert(false);
        } else if pending1.len() == 1 {
            assert(exists|t| pending_enabled(pending1, t));
            assert(pending_enabled(pending1, t));
            assert(pending1 == set![t]);
            assert(set![t].remove(t) == Set::<MapTransition>::empty());
            assert(pending2.is_empty());
        } else {
            assert(pending1.len() > 1);
            match t {
                MapTransition::T1MapStart => {
                    assert(pending2.contains(MapTransition::T1MapEnd));
                    assert(pending_enabled(pending2, MapTransition::T1MapEnd));
                    assert(pending_inv(pending2));
                }
                MapTransition::T1MapEnd => {
                    assert(!pending1.contains(MapTransition::T1MapStart));
                    assert(pending2 <= set![MapTransition::T2MapStart, MapTransition::T2MapEnd]);
                    if pending2.contains(MapTransition::T2MapStart) {
                        assert(pending_enabled(pending2, MapTransition::T2MapStart));
                    } else {
                        if pending2.contains(MapTransition::T2MapEnd) {
                            assert(pending_enabled(pending2, MapTransition::T2MapEnd));
                        }
                    }
                    assert(pending_inv(pending2));
                }
                MapTransition::T2MapStart => {
                    assert(pending1.contains(MapTransition::T2MapEnd));
                    assert(pending_enabled(pending2, MapTransition::T2MapEnd));
                    assert(pending_inv(pending2));
                }
                MapTransition::T2MapEnd => {
                    assert(!pending1.contains(MapTransition::T2MapStart));
                    assert(pending2 <= set![MapTransition::T1MapStart, MapTransition::T1MapEnd]);
                    if pending2.contains(MapTransition::T1MapStart) {
                        assert(pending_enabled(pending2, MapTransition::T1MapStart));
                    } else {
                        if pending2.contains(MapTransition::T1MapEnd) {
                            assert(pending_enabled(pending2, MapTransition::T1MapEnd));
                        }
                    }
                }
            }
        }
        
        match t {
            MapTransition::T1MapStart => {
                assert(step_Map_sound(s1.mappings, s1.thread_state.values(), pte1_vaddr, pte1));
                assert(s1.thread_state[0] == ThreadState::Idle);
                assert(s2.thread_state[0] == ThreadState::Map { vaddr: pte1_vaddr, pte: pte1 });
                assert(next_step(c, s1, s2, Step::MapStart, t1_map_start_rlbl));
            }
            MapTransition::T1MapEnd => {
                // assert(s2.thread_state[0] == ThreadState::Idle);
                assume(next_step(c, s1, s2, Step::MapEnd, t1_map_end_rlbl));
            }
            MapTransition::T2MapStart => {
                assert(step_Map_sound(s1.mappings, s1.thread_state.values(), pte2_vaddr, pte2));
                assert(s1.thread_state[1] == ThreadState::Idle);
                assert(s2.thread_state[1] == ThreadState::Map { vaddr: pte2_vaddr, pte: pte2 });
                assert(next_step(c, s1, s2, Step::MapStart, t2_map_start_rlbl));
            }
            MapTransition::T2MapEnd => {
                // assert(s2.thread_state[1] == ThreadState::Idle);
                assume(next_step(c, s1, s2, Step::MapEnd, t2_map_end_rlbl));
            }
        }
    }
    
    #[verifier::rlimit(10000)]
    proof fn program_two_threads_map() {
        lemma_max_phyaddr_at_least();
        x86_arch_spec_upper_bound();
    
        let c = Constants { thread_no: 2, phys_mem_size: 8_192_000 };
    
        let s1 = State {
            mem: seq![arbitrary(); crate::spec_t::mmu::defs::MAX_BASE],
            thread_state:
                map![
                0 => ThreadState::Idle,
                1 => ThreadState::Idle,
            ],
            mappings: Map::empty(),
            sound: true,
        };
    
        assert(wf(c, s1));
        assert(init(c, s1));
    
        let pending1 = set![MapTransition::T1MapStart, MapTransition::T1MapEnd, MapTransition::T2MapStart, MapTransition::T2MapEnd];
        assert(pending_enabled(pending1, MapTransition::T1MapStart));
        assert(pending_inv(pending1));
        let (t1, s2, pending2) = map_next(c, s1, pending1);
        map_next_ensures(c, s1, s2, pending1, pending2, t1);
        assert(pending2.len() == 3);
        let (t2, s3, pending3) = map_next(c, s2, pending2);
        map_next_ensures(c, s2, s3, pending2, pending3, t2);
        assert(pending3.len() == 2);
        let (t3, s4, pending4) = map_next(c, s3, pending3);
        map_next_ensures(c, s3, s4, pending3, pending4, t3);
        assert(pending4.len() == 1);
        let (t4, s5, pending5) = map_next(c, s4, pending4);
        map_next_ensures(c, s4, s5, pending4, pending5, t4);
        assert(pending5.len() == 0);
    
        assert(s5.thread_state == s1.thread_state);
        assert(s5.mappings == map![
            pte1_vaddr => pte1,
            pte2_vaddr => pte2,
        ]);
        // let s_t2s = State { thread_state: s1.thread_state.insert( 0, ThreadState::Map { vaddr: pte2_vaddr, pte: pte1 },), ..s1 };
    
        // let s1s_t2srlbl = RLbl::MapStart { thread_id: 0, vaddr: pte2_vaddr, pte: pte1 };
        // assert(next_step(c, s1, s_t2s, Step::MapStart, s1s_t2srlbl,));
    }
}

} // verus!
