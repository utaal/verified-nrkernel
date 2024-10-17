use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ MASK_DIRTY_ACCESS };
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::definitions_t::{ aligned, Core };

verus! {

// This file contains refinement layer 2 of the MMU, which removes store buffers and expresses
// writes as modifications of a single Map representing the memory.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    /// History variables.
    pub hist: History,
}

pub struct History {
    pub neg_writes: Map<Core, Set<usize>>,
}

impl State {
    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, value: usize) -> bool {
        self.is_tso_read_deterministic(core, addr)
            ==> value & MASK_DIRTY_ACCESS == self.pt_mem.read(addr) & MASK_DIRTY_ACCESS
    }

    /// For the active writer core, the memory always behaves like a Map. For other cores this is
    /// only true for addresses that haven't been written to.
    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        ||| self.no_other_writers(core)
        ||| !self.write_addrs().contains(addr)
    }

    pub open spec fn is_neg_write(self, addr: usize) -> bool {
        &&& self.pt_mem.page_addrs().contains_key(addr)
        &&& !(self.pt_mem.page_addrs()[addr] is Empty)
    }

    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores().subset_of(set![core])
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn write_addrs(self) -> Set<usize> {
        self.writes.map(|x:(_,_)| x.1)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core,value| #[trigger] self.writes.contains((core,value)) ==> c.valid_core(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    // Invlpg cancels inflight walks
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.pt_mem == pre.pt_mem
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)

    &&& post.hist.neg_writes == pre.hist.neg_writes.insert(core, set![])
}


// ---- Non-atomic page table walks ----

// FIXME: this should make sure the alignment of va fits with the PTE
pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, va: usize, lbl: Lbl) -> bool {
    let walk = Walk { va, path: seq![] };
    &&& lbl is Tau

    &&& c.valid_core(core)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    value: usize,
    lbl: Lbl
    ) -> bool
{
    let (res, addr) = walk.next(pre.pt_mem.pml4, value);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& res is Incomplete

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(res.walk()))

    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_WalkDone(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    value: usize,
    lbl: Lbl
    ) -> bool
{
    let (res, addr) = walk.next(pre.pt_mem.pml4, value);
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk.pte() == walk_result
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& !(res is Incomplete)

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks

    &&& post.hist.neg_writes == pre.hist.neg_writes
}


// ---- TSO ----

pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes.insert((core, addr))

    &&& post.hist.neg_writes == if pre.is_neg_write(addr) {
            pre.hist.neg_writes.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.hist.neg_writes }
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes

    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)

    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Non-atomic page table walks
    WalkInit { core: Core, va: usize },
    WalkStep { core: Core, walk: Walk, value: usize },
    WalkDone { walk: Walk, value: usize },
    // TSO
    Write,
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                         => step_Invlpg(pre, post, c, lbl),
        Step::WalkInit { core, va }          => step_WalkInit(pre, post, c, core, va, lbl),
        Step::WalkStep { core, walk, value } => step_WalkStep(pre, post, c, core, walk, value, lbl),
        Step::WalkDone { walk, value }       => step_WalkDone(pre, post, c, walk, value, lbl),
        Step::Write                          => step_Write(pre, post, c, lbl),
        Step::Read                           => step_Read(pre, post, c, lbl),
        Step::Barrier                        => step_Barrier(pre, post, c, lbl),
        Step::Stutter                        => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    pre.happy ==> exists|step| next_step(pre, post, c, step, lbl)
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
    admit();
}

mod refinement {
    use crate::spec_t::mmu::*;
    //use crate::spec_t::mmu::pt_mem::{ PTMem };
    use crate::spec_t::mmu::rl1;
    use crate::spec_t::mmu::rl2;
    //use crate::spec_t::mmu::rl4::{ get_first };

    impl rl2::State {
        pub open spec fn interp(self) -> rl1::State {
            arbitrary()
        }
    }
}

} // verus!
