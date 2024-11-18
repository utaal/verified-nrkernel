use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, Core };
use crate::spec_t::mmu::rl4::{ Writes, MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 2 of the MMU. Compared to layer 3, it removes store buffers
// and defines an atomic semantics to page table walks.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    ///// In-progress page table walks
    //pub walks: Map<Core, Set<Walk>>,
    ///// Store buffers
    //pub sbuf: Map<Core, Seq<(usize, usize)>>,
    pub writes: Writes,
    ///// Current polarity: Are we doing only positive writes or only negative writes? Polarity can be
    ///// flipped when neg and writes are all empty.
    ///// A non-flipping write with the wrong polarity sets happy to false.
    ///// Additionally tracks the current writer core.
    ///// Technically we could probably infer the polarity from the write tracking but this is easier.
    //pub polarity: Polarity,
    /// Tracks the virtual address ranges for which we cannot guarantee atomic walk results
    /// If polarity is negative, we give no guarantees about the results in these ranges; If it's
    /// positive, the possible results are atomic semantics or an "invalid" result.
    /// Each element is a tuple `(vbase, size)`
    pub pending_maps: Map<usize, PTE>,
}


impl State {
    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    // TODO: I may want/need to add these conditions as well:
    // - when unmapping directory, it must be empty
    //   - and its entries must not be modified
    //      - not necessary because these would only be problematic if positive which is not allowed
    // - the location corresponds to *exactly* one leaf entry in the page table
    //   - previous conditions are important for this: i cannot know if there's exactly one leaf
    //     entry, if e.g. allow unmapping non-empty
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize, c: Constants) -> bool {
        &&& !self.writes.all.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonneg_write(addr, value)
        //&&& !self.can_change_polarity(c) ==> {
        //    // If we're not at the start of an operation, the writer must stay the same
        //    &&& self.polarity.core() == core
        //    // and the polarity must match
        //    &&& if self.polarity is Pos { self.pt_mem.is_nonneg_write(addr) } else { self.pt_mem.is_neg_write(addr) }
        //}
        // The write must be to a location that's currently a leaf of the page table.
        // FIXME: i'm not sure this is doing what i want it to do.
        // TODO: maybe bad trigger
        //&&& exists|path, i| #![auto]
        //    self.pt_mem.page_table_paths().contains(path)
        //    && 0 <= i < path.len() && path[i].0 == addr
    }

    //pub open spec fn can_change_polarity(self, c: Constants) -> bool {
    //    &&& self.writes.all.is_empty()
    //    &&& forall|core| #![auto] c.valid_core(core) ==> self.writes.neg[core].is_empty()
    //}

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.all.contains(addr) ==> self.writes.core == core
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] self.writes.neg.contains_key(core) ==> self.writes.neg[core].finite()
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        }
    }
    
    pub open spec fn writes_neg_contains(self, addr: usize) -> bool {
        exists|core| #![auto] self.writes.neg.contains_key(core) && self.writes.neg[core].contains(addr)
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)

    &&& post.happy      ==  pre.happy
    &&& post.pt_mem     ==  pre.pt_mem
    &&& post.writes.all === set![]
    &&& post.writes.neg ==  pre.writes.neg.insert(core, set![])
    &&& post.pending_maps  === map![] // This might not be correct when we have negative writes as well
    //&&& post.polarity   == pre.polarity
}


// ---- Non-atomic page table walks ----

/// An atomic page table walk
pub open spec fn step_Walk(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, walk_res)

    &&& c.valid_core(core)
    &&& walk_res == rl3::iter_walk(pre.pt_mem, walk_res.vaddr()).result()

    &&& post == pre
}

/// A non-atomic page table walk. This can only be an invalid result and only on specific ranges.
pub open spec fn step_WalkNA(pre: State, post: State, c: Constants, vb: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, WalkResult::Invalid { vaddr })

    // TODO: aligned(vaddr, 8)
    &&& c.valid_core(core)
    &&& pre.pending_maps.contains_key(vb)
    &&& vb <= vaddr < vb + pre.pending_maps[vb].frame.size

    &&& post == pre
}


// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy      == pre.happy && pre.is_this_write_happy(core, addr, value, c)
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.writes.all == pre.writes.all.insert(addr)
    &&& post.writes.neg == if !pre.pt_mem.is_nonneg_write(addr, value) {
            pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.writes.neg }
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
    //&&& post.polarity   == if pre.pt_mem.is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

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

    &&& c.valid_core(core)

    &&& post.happy      ==  pre.happy
    &&& post.pt_mem     ==  pre.pt_mem
    &&& post.writes.all === set![]
    &&& post.writes.neg ==  pre.writes.neg
    &&& post.pending_maps === map![] // This might not be correct when we have negative writes as well
    //&&& post.polarity   == pre.polarity
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Atomic page table walk
    Walk,
    // Non-atomic page table walk
    WalkNA { vb: usize },
    // TSO
    Write,
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg        => step_Invlpg(pre, post, c, lbl),
        Step::Walk          => step_Walk(pre, post, c, lbl),
        Step::WalkNA { vb } => step_WalkNA(pre, post, c, vb, lbl),
        Step::Write         => step_Write(pre, post, c, lbl),
        Step::Read          => step_Read(pre, post, c, lbl),
        Step::Barrier       => step_Barrier(pre, post, c, lbl),
        Step::Stutter       => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    if pre.happy {
        exists|step| next_step(pre, post, c, step, lbl)
    } else {
        post.happy == pre.happy
    }
}

proof fn init_implies_inv(pre: State, c: Constants)
    requires pre.init()
    ensures pre.inv(c)
{ admit(); }

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv(c)
{
    //if pre.happy {
    //    match step {
    //        Step::Invlpg                         => assert(post.inv(c)),
    //        Step::WalkInit { core, vaddr }       => assert(post.inv(c)),
    //        Step::WalkStep { core, walk, value } => assert(post.inv(c)),
    //        Step::WalkDone { walk, value }       => assert(post.inv(c)),
    //        Step::Write                          => assert(post.inv(c)),
    //        Step::Writeback { core }             => assert(post.inv(c)),
    //        Step::Read                           => assert(post.inv(c)),
    //        Step::Barrier                        => assert(post.inv(c)),
    //        Step::Stutter                        => assert(post.inv(c)),
    //    }
    //}
}


} // verus!
