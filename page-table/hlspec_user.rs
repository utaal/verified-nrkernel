use vstd::prelude::*;

use crate::definitions_t::{
    aligned, axiom_max_phyaddr_width_facts, candidate_mapping_in_bounds, x86_arch_spec_upper_bound,
    Flags, LoadResult, MemRegion, PageTableEntry, RWOp, StoreResult, MAX_PHYADDR_SPEC, WORD_SIZE,
};
use crate::spec_t::hlspec::*;

verus! {

proof fn lemma_max_phyaddr_at_least()
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

    let c = AbstractConstants { thread_no: 4, phys_mem_size: 4096 * 4096 };

    let s1 = AbstractVariables {
        mem: Map::empty(),
        thread_state:
            map![
            0 => AbstractArguments::Empty,
            1 => AbstractArguments::Empty,
            2 => AbstractArguments::Empty,
            3 => AbstractArguments::Empty,
        ],
        mappings: Map::empty(),
        sound: true,
    };

    assert(wf(c, s1));
    assert(init(c, s1));

    let pte1 = PageTableEntry {
        frame: MemRegion { base: 4096, size: 4096 },
        flags: Flags { is_writable: true, is_supervisor: false, disable_execute: true },
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(set![], s1.mappings, 4096 * 3, pte1));

    let s2 = AbstractVariables {
        thread_state: s1.thread_state.insert(
            1,
            AbstractArguments::Map { vaddr: 4096 * 3, pte: pte1 },
        ),
        ..s1
    };

    // assert(step_Map_start(c, s1, s2, 1, 4096 * 3, pte1));
    assert(next_step(
        c,
        s1,
        s2,
        AbstractStep::MapStart { thread_id: 1, vaddr: 4096 * 3, pte: pte1 },
    ));
    assert(next(c, s1, s2));

    let mem3 = lemma_extend_mem_domain(s2.mem, 4096 * 3, 4096);
    let s3 = AbstractVariables {
        thread_state: s2.thread_state.insert(1, AbstractArguments::Empty),
        mappings: s2.mappings.insert(4096 * 3, pte1),
        mem: mem3,
        ..s2
    };
    assert(s3.mem.dom() == s2.mem.dom().union(
        Set::new(
            |w: nat|
                crate::spec_t::mem::word_index_spec(4096 * 3) <= w
                    < crate::spec_t::mem::word_index_spec(4096 * 3) + (4096nat / WORD_SIZE as nat),
        ),
    ));

    assert(s3.mappings.contains_pair(4096 * 3, pte1));  // discharge exists in `mem_domain_from_mappings_contains`
    assert(s3.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s3.mappings));

    assert(next_step(c, s2, s3, AbstractStep::MapEnd { thread_id: 1, result: Ok(()) }));

    let s4 = AbstractVariables { mem: s3.mem.insert(512 * 3, 42), ..s3 };

    assert(crate::spec_t::mem::word_index_spec(4096 * 3) == 512 * 3) by (nonlinear_arith){
        assert(aligned(4096 * 3, WORD_SIZE as nat));
    }
    assert(next_step(
        c,
        s3,
        s4,
        AbstractStep::ReadWrite {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: RWOp::Store { new_value: 42, result: StoreResult::Ok },
            pte: Some((4096 * 3, pte1)),
        },
    ));

    let s5 = s4;
    assert(next_step(
        c,
        s4,
        s5,
        AbstractStep::ReadWrite {
            thread_id: 1,
            vaddr: 4096 * 3,
            op: RWOp::Load { is_exec: false, result: LoadResult::Value(42) },
            pte: Some((4096 * 3, pte1)),
        },
    ));

    let s6 = AbstractVariables {
        thread_state: s5.thread_state.insert(
            2,
            AbstractArguments::Unmap { vaddr: 4096 * 3, pte: Some(pte1) },
        ),
        mappings: s5.mappings.remove(4096 * 3),
        mem: arbitrary(),  // TODO
        ..s5
    };
    assume(false); //TODO

    assert(s6.mem.dom() =~= mem_domain_from_mappings(c.phys_mem_size, s6.mappings));
    assert(next_step(c, s5, s6, AbstractStep::UnmapStart { thread_id: 2, vaddr: 4096 * 3 }));

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
                crate::spec_t::mem::word_index_spec(vaddr),
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
                // TODO(matthias) can you try verusfind here?
                assert(!aligned(size, WORD_SIZE as nat)) by (nonlinear_arith){}
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
                        crate::spec_t::mem::word_index_spec(vaddr) <= w
                            < crate::spec_t::mem::word_index_spec(vaddr) + (size
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
                // TODO(matthias) can you try verusfind here?
                assert(!aligned(size, WORD_SIZE as nat)) by (nonlinear_arith)
                    requires
                        0 < size < WORD_SIZE,
                {}
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
            let r = extended.insert(crate::spec_t::mem::word_index_spec(vaddr), arbitrary());
            r
        } else {
            map
        }
    }

}

} // verus!
