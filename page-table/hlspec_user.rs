use vstd::prelude::*;

use crate::spec_t::hlspec::*;

verus! {
proof fn program_1() {
    let c = AbstractConstants {
        thread_no: 4,
        phys_mem_size: 4096 * 4096,
    };

    let s = AbstractVariables {
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

    //assert forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id) by {
    //    if id < 4 {
    //        assert(id <= c.thread_no);
    //        assert(s.thread_state.contains_key(id));
    //    } else {
    //        assert(!s.thread_state.contains_key(id));
    //    }
    //};
    assert(wf(c, s));
    assert(init(c, s));

}
}
