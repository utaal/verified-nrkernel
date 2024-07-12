use vstd::prelude::*;

use crate::spec_t::hlspec::*;
use crate::definitions_t::{PageTableEntry, MemRegion, Flags, MAX_PHYADDR_SPEC, axiom_max_phyaddr_width_facts, candidate_mapping_in_bounds, x86_arch_spec_upper_bound};

verus! {
proof fn lemma_max_phyaddr_at_least()
    ensures MAX_PHYADDR_SPEC >= 0xffffffff {

    axiom_max_phyaddr_width_facts();

    assert((1u64 << 32) - 1u64 == 0xffffffff) by (compute);
    assert(forall|m:u64,n:u64|  n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
}

proof fn program_1() {
    lemma_max_phyaddr_at_least();
    x86_arch_spec_upper_bound();

    let c = AbstractConstants {
        thread_no: 4,
        phys_mem_size: 4096 * 4096,
    };

    let s1 = AbstractVariables {
        mem: Map::empty(),
        thread_state: map![
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
        frame: MemRegion {
            base: 4096,
            size: 4096,
        },
        flags: Flags {
            is_writable: true,
            is_supervisor: false,
            disable_execute: true,
        }
    };

    assert(candidate_mapping_in_bounds(4096 * 3, pte1));
    assert(step_Map_enabled(set![], s1.mappings, 4096 * 3, pte1));

    let s2 = AbstractVariables {
        thread_state: s1.thread_state.insert(
            1,
            AbstractArguments::Map {
                vaddr: 4096 * 3, 
                pte: pte1,
            }),
        ..s1
    };

    // assert(step_Map_start(c, s1, s2, 1, 4096 * 3, pte1));
    assert(next_step(c, s1, s2, AbstractStep::MapStart {
        thread_id: 1,
        vaddr: 4096 * 3,
        pte: pte1,
    }));
    assert(next(c, s1, s2));

}
}
