use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ MASK_DIRTY_ACCESS };
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::spec_t::hardware::{ Core, PageDirectoryEntry, GhostPageDirectoryEntry, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ aligned, bitmask_inc };

verus! {

// This file contains refinement layer 3 of the MMU, which expresses translation caching and
// non-atomicity of page walks as a single concept.

pub struct Constants {
    pub cores: Set<Core>,
}

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<PTWalk>>,
    ///// Addresses that have been used in a page table walk
    ///// TODO: This can probably be at least partially reset in invlpg.
    //pub used_addrs: Set<usize>,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    ///// History variables.
    //pub hist: History,
}

pub struct History {
}

impl State {
    pub open spec fn stutter(pre: State, post: State) -> bool {
        let State { happy, pt_mem, walks, writes } = post;
        &&& happy == pre.happy
        &&& pt_mem@ == pre.pt_mem@
        &&& walks == pre.walks
        &&& writes == pre.writes
    }

    /// For the active writer core, the memory always behaves like a Map. For other cores this is
    /// only true for addresses that haven't been written to.
    pub open spec fn read_from_mem_tso(self, c: Constants, core: Core, addr: usize, value: usize) -> bool {
        self.no_other_writers(core) || !self.write_addrs().contains(addr)
            ==> value & MASK_DIRTY_ACCESS == self.pt_mem@[addr] & MASK_DIRTY_ACCESS
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    /// Is true if only this core's store buffer is non-empty.
    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores().subset_of(set![core])
        //self.writer_cores() === set![] || self.writer_cores() === set![core] 
        //forall|core2| #[trigger] c.valid_core(core2) && self.sbuf[core2].len() > 0 ==> core2 == core1
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn write_addrs(self) -> Set<usize> {
        self.writes.map(|x:(_,_)| x.1)
    }

    ///// Is true if only this core has performed writes since the last store buffer drain.
    //pub open spec fn is_single_writer(self, c: Constants, core1: Core) -> bool {
    //    forall|core2, v| c.valid_core(core2) && #[trigger] self.writes.contains((core2, v)) ==> core2 == core1
    //}
    //
    ///// Is true if only one core has performed writes since the last store buffer drain.
    //pub open spec fn single_writer(self) -> bool {
    //    forall|core1, core2, v1, v2| #![auto] self.writes.contains((core1, v1)) && self.writes.contains((core2, v2)) ==> core2 == core1
    //}

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core,value| #[trigger] self.writes.contains((core,value)) ==> c.valid_core(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        //&&& self.inv_unchanged_walks_match_memory(c)
        //&&& self.inv_sbuf_subset_writes(c)
        }
    }
}

impl Constants {
    pub open spec fn valid_core(self, core: Core) -> bool {
        self.cores.contains(core)
    }
}

// ---- Mixed (relevant to multiple of TSO/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    // Invlpg cancels inflight walks
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.pt_mem@ == pre.pt_mem@
    //&&& post.used_addrs == pre.used_addrs
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)
}


// ---- Non-atomic page table walks ----

pub open spec fn step_Walk1(pre: State, post: State, c: Constants, core: Core, va: usize, l0ev: usize, lbl: Lbl) -> bool {
    let addr = add(pre.pt_mem.pml4(), l0_bits!(va as u64) as usize);
    let l0e = (addr, PageDirectoryEntry { entry: l0ev as u64, layer: Ghost(0) });
    let walk = match l0e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e] },
        _                                         => arbitrary(), // No page mappings here
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?
    &&& pre.read_from_mem_tso(c, core, addr, l0ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)
    &&& post.writes == pre.writes
}

pub open spec fn step_Walk2(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l1ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0];
    let addr = add(l0e.1@->Directory_addr, l1_bits!(va as u64) as usize);
    let l1e = (addr, PageDirectoryEntry { entry: l1ev as u64, layer: Ghost(1) });
    let new_walk = match l1e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid   { va, path: seq![l0e, l1e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e, l1e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 1
    &&& pre.read_from_mem_tso(c, core, addr, l1ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)
    &&& post.writes == pre.writes
}

pub open spec fn step_Walk3(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l2ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1];
    let addr = add(l1e.1@->Directory_addr, l2_bits!(va as u64) as usize);
    let l2e = (addr, PageDirectoryEntry { entry: l2ev as u64, layer: Ghost(2) });
    let new_walk = match l2e.1@ {
        GhostPageDirectoryEntry::Directory { .. } => PTWalk::Partial { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Page { .. }      => PTWalk::Valid   { va, path: seq![l0e, l1e, l2e] },
        GhostPageDirectoryEntry::Empty            => PTWalk::Invalid { va, path: seq![l0e, l1e, l2e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 2
    &&& pre.read_from_mem_tso(c, core, addr, l2ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)
    &&& post.writes == pre.writes
}

pub open spec fn step_Walk4(pre: State, post: State, c: Constants, core: Core, walk: PTWalk, l3ev: usize, lbl: Lbl) -> bool {
    let PTWalk::Partial { va, path } = walk else { arbitrary() };
    let l0e = path[0]; let l1e = path[1]; let l2e = path[2];
    let addr = add(l2e.1@->Directory_addr, l3_bits!(va as u64) as usize);
    let l3e = (addr, PageDirectoryEntry { entry: l3ev as u64, layer: Ghost(3) });
    let new_walk = match l3e.1@ {
        GhostPageDirectoryEntry::Page { .. } => PTWalk::Valid { va, path: seq![l0e, l1e, l2e, l3e] },
        GhostPageDirectoryEntry::Directory { .. }
        | GhostPageDirectoryEntry::Empty => PTWalk::Invalid { va, path: seq![l0e, l1e, l2e, l3e] },
    };
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk is Partial
    &&& path.len() == 3
    &&& pre.read_from_mem_tso(c, core, addr, l3ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)
    &&& post.writes == pre.writes
}

pub open spec fn step_Walk(pre: State, post: State, c: Constants, path: Seq<(usize, PageDirectoryEntry)>, lbl: Lbl) -> bool {
    let walk = match lbl {
        Lbl::Walk(_, va, Some(pte)) => PTWalk::Valid { va, path },
        Lbl::Walk(_, va, None) => PTWalk::Invalid { va, path },
        _ => arbitrary(),
    };
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& (pte matches Some(pte) ==> pte == walk.pte())

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs
    &&& post.writes == pre.writes
}


// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs
    &&& post.writes == pre.writes.insert((core, addr))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(c, core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs
    &&& post.writes == pre.writes
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& State::stutter(pre, post)
}

pub enum Step {
    // Mixed
    Invlpg,
    // Non-atomic page table walks
    Walk1 { core: Core, va: usize, l0ev: usize },
    Walk2 { core: Core, walk: PTWalk, l1ev: usize },
    Walk3 { core: Core, walk: PTWalk, l2ev: usize },
    Walk4 { core: Core, walk: PTWalk, l3ev: usize },
    Walk { path: Seq<(usize, PageDirectoryEntry)> },
    // TSO
    Write,
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                     => step_Invlpg(pre, post, c, lbl),
        Step::Walk1 { core, va, l0ev }   => step_Walk1(pre, post, c, core, va, l0ev, lbl),
        Step::Walk2 { core, walk, l1ev } => step_Walk2(pre, post, c, core, walk, l1ev, lbl),
        Step::Walk3 { core, walk, l2ev } => step_Walk3(pre, post, c, core, walk, l2ev, lbl),
        Step::Walk4 { core, walk, l3ev } => step_Walk4(pre, post, c, core, walk, l3ev, lbl),
        Step::Walk { path }              => step_Walk(pre, post, c, path, lbl),
        Step::Write                      => step_Write(pre, post, c, lbl),
        Step::Read                       => step_Read(pre, post, c, lbl),
        Step::Barrier                    => step_Barrier(pre, post, c, lbl),
        Step::Stutter                    => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants) -> bool {
    pre.happy ==> exists|step, lbl| next_step(pre, post, c, step, lbl)
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

} // verus!
