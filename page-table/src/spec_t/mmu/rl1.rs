use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, Core };
use crate::spec_t::mmu::rl3::{ Writes };
use crate::spec_t::hardware::{ MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 2 of the MMU. Compared to layer 3, it removes store buffers
// and defines an atomic semantics to page table walks.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    pub writes: Writes,
    /// Tracks the virtual address ranges for which we cannot guarantee atomic walk results
    /// If polarity is negative, we give no guarantees about the results in these ranges; If it's
    /// positive, the possible results are atomic semantics or an "invalid" result.
    /// Each element is a tuple `(vbase, size)`
    pub pending_maps: Map<usize, PTE>,
}

pub enum Step {
    // Mixed
    Invlpg,
    // Atomic page table walk
    Walk { vaddr: usize },
    // Non-atomic page table walk
    WalkNA { vb: usize },
    // TSO
    Write,
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}


impl State {
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.all.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonneg_write(addr, value)
    }

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.all.contains(addr) ==> self.writes.core == core
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        true
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            //neg: pre.writes.neg.insert(core, set![]),
            core: pre.writes.core,
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}


// ---- Non-atomic page table walks ----

/// An atomic page table walk
pub open spec fn step_Walk(pre: State, post: State, c: Constants, vaddr: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, walk_res)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& walk_res == pre.pt_mem.pt_walk(vaddr).result()

    &&& post == pre
}

/// A non-atomic page table walk. This can only be an invalid result and only on specific ranges.
pub open spec fn step_WalkNA(pre: State, post: State, c: Constants, vb: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, WalkResult::Invalid { vaddr })

    &&& pre.happy
    &&& c.valid_core(core)
    //&&& aligned(vaddr as nat, 8)
    &&& pre.pending_maps.contains_key(vb)
    &&& vb <= vaddr < vb + pre.pending_maps[vb].frame.size

    &&& post == pre
}


// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value)

    &&& post.happy      == pre.happy
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.writes.all == pre.writes.all.insert(addr)
    //&&& post.writes.neg == if !pre.pt_mem.is_nonneg_write(addr, value) {
    //        pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
    //    } else { pre.writes.neg }
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_tso_read_deterministic(core, addr)
            ==> value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            ..pre.writes
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& !pre.is_this_write_happy(core, addr, value)
    &&& !post.happy
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg         => step_Invlpg(pre, post, c, lbl),
        Step::Walk { vaddr } => step_Walk(pre, post, c, vaddr, lbl),
        Step::WalkNA { vb }  => step_WalkNA(pre, post, c, vb, lbl),
        Step::Write          => step_Write(pre, post, c, lbl),
        Step::Read           => step_Read(pre, post, c, lbl),
        Step::Barrier        => step_Barrier(pre, post, c, lbl),
        Step::SadWrite       => step_SadWrite(pre, post, c, lbl),
        Step::Sadness        => step_Sadness(pre, post, c, lbl),
        Step::Stutter        => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    //&&& pre.pt_mem == ..
    &&& pre.happy == true
    //&&& pre.writes.core == ..
    &&& pre.writes.all === set![]
    &&& pre.pending_maps === map![]

    &&& c.valid_core(pre.writes.core)
    &&& forall|va| aligned(va as nat, 8) ==> #[trigger] pre.pt_mem.mem.contains_key(va)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& pre.pt_mem.pml4 <= u64::MAX - 4096
}

proof fn init_implies_inv(pre: State, c: Constants)
    requires init(pre, c)
    ensures pre.inv(c)
{}

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv(c)
{}


} // verus!
