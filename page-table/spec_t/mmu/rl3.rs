use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ get_first, MASK_DIRTY_ACCESS };
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
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    ///// Addresses that have been used in a page table walk
    ///// TODO: This can probably be at least partially reset in invlpg.
    //pub used_addrs: Set<usize>,
    /// History variables
    pub hist: History,
    //pub proph: Prophecy,
}

pub struct History {
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
}

//pub struct Prophecy {
//    /// Prophesied memories after future writeback transitions
//    pub pt_mems: Seq<PTMem>,
//}

impl State {
    pub open spec fn stutter(pre: State, post: State) -> bool {
        let State { happy, pt_mem, walks, sbuf, hist } = post;
        &&& happy == pre.happy
        &&& pt_mem@ == pre.pt_mem@
        &&& walks == pre.walks
        &&& sbuf == pre.sbuf
        &&& hist == pre.hist
    }

    /// This predicate is true whenever `value` is a value that might be read from the address
    /// `addr` on core `core`. See rl4.rs for explanation.
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, value: usize) -> bool {
        let val = match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem@[addr],
        };
        value & MASK_DIRTY_ACCESS == val & MASK_DIRTY_ACCESS
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
        self.hist.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core,value| #[trigger] self.hist.writes.contains((core,value)) ==> c.valid_core(core)
    }

    // This invariant is wrong. Memory used in walks might change but not in a way that changes the
    // result.
    ///// Some `core` accessed memory as part of a pt walk, at address `addr` and resulting in value
    ///// `value`. If no other core wrote to `address`, then reading from memory will still return
    ///// `value`.
    //pub open spec fn inv_unchanged_walks_match_memory(self, c: Constants) -> bool {
    //    //self.single_writer() ==>
    //    forall|addr, value, walk, core1|
    //           c.valid_core(core1)
    //        && #[trigger] self.walks[core1].contains(walk)
    //        && walk.path().to_set().contains((addr, value))
    //        && (forall|core2| #![auto] !self.hist.writes.contains((core2, addr)))
    //            ==> #[trigger] self.read_from_mem_tso(core1, addr, value.entry as usize)
    //}

    pub open spec fn inv_sbuf_subset_writes(self, c: Constants) -> bool {
        forall|core: Core, addr: usize, value: usize| #![auto]
            c.valid_core(core) && self.sbuf[core].to_set().contains((addr, value))
                ==> self.hist.writes.contains((core, addr))
    }

    pub open spec fn inv_writer_cores(self, c: Constants) -> bool {
        &&& self.writer_cores().len() <= 1
        &&& forall|core| #[trigger] c.valid_core(core) && self.sbuf[core].len() > 0 ==> self.writer_cores().contains(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        //&&& self.inv_unchanged_walks_match_memory(c)
        &&& self.inv_sbuf_subset_writes(c)
        &&& self.inv_writer_cores(c)
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
    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    // .. and cancels inflight walks.
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    &&& pre.read_from_mem_tso(core, addr, l0ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    &&& pre.read_from_mem_tso(core, addr, l1ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    &&& pre.read_from_mem_tso(core, addr, l2ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    &&& pre.read_from_mem_tso(core, addr, l3ev)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    //&&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
// TODO: we don't model atomics, so technically the user-space threads cannot synchronize
// TODO: max physical size?
/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes.insert((core, addr))
    //&&& post.proph.pt_mems == pre.proph.pt_mems.push(proph)
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    //// Prophetic enabling condition
    //&&& pre.proph.pt_mems.len() >= 1
    //&&& post.pt_mem == pre.proph.pt_mems[0]

    &&& post.happy == pre.happy
    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems.drop_first()
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
    //&&& post.proph.pt_mems == pre.proph.pt_mems
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    //&&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    //&&& post.proph.pt_mems == pre.proph.pt_mems
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
    Writeback { core: Core },
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
        Step::Writeback { core }         => step_Writeback(pre, post, c, core, lbl),
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

proof fn next_step_preserves_inv_sbuf_subset_writes(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_sbuf_subset_writes(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_sbuf_subset_writes(c)
{
    match step {
        rl3::Step::Invlpg => assert(post.inv_sbuf_subset_writes(c)),
        rl3::Step::Walk1 { core, va, l0ev }   => assert(post.inv_sbuf_subset_writes(c)),
        rl3::Step::Walk2 { core, walk, l1ev } => assert(post.inv_sbuf_subset_writes(c)),
        rl3::Step::Walk3 { core, walk, l2ev } => assert(post.inv_sbuf_subset_writes(c)),
        rl3::Step::Walk4 { core, walk, l3ev } => assert(post.inv_sbuf_subset_writes(c)),
        rl3::Step::Walk { path } => {
            assert(post.inv_sbuf_subset_writes(c));
        },
        rl3::Step::Write => {
            let core = lbl->Write_0;
            assert forall|core2: Core, addr: usize, value: usize| #![auto]
                c.valid_core(core2) && post.sbuf[core2].to_set().contains((addr, value))
                    implies post.hist.writes.contains((core2, addr))
            by {
                if core2 == core && pre.sbuf[core].to_set().contains((addr, value)) { }
            };
            assert(post.inv_sbuf_subset_writes(c))
        },
        rl3::Step::Writeback { core } => {
            // should be easy
            assume(post.inv_sbuf_subset_writes(c));
        },
        rl3::Step::Read => {
            assert(post.inv_sbuf_subset_writes(c));
        },
        rl3::Step::Barrier => {
            assert(post.inv_sbuf_subset_writes(c));
        },
        rl3::Step::Stutter => {
            assert(post.inv_sbuf_subset_writes(c));
        },
    }
}

proof fn next_step_preserves_inv_writer_cores(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.happy ==> post.inv_writer_cores(c)
{
    match step {
        rl3::Step::Invlpg => {
            let core = lbl->Invlpg_0;
            assert(pre.writer_cores().len() <= 1);
            lemma_writer_cores_filter(pre.hist.writes, core);
            assert(post.writer_cores().len() <= pre.writer_cores().len());

            // Conjunct 1
            assert(post.writer_cores().len() <= 1);

            admit();
            // Conjunct 2
            assert forall|core| #[trigger] c.valid_core(core) && post.sbuf[core].len() > 0
                implies post.writer_cores().contains(core)
            by {
                assert(forall|core| #[trigger] c.valid_core(core) && post.sbuf[core].len() > 0 ==> pre.sbuf[core].len() > 0);
                assert(forall|core| post.writer_cores().contains(core) ==> pre.writer_cores().contains(core));
                assert(pre.writer_cores().contains(core));
            };
            assert(post.inv_writer_cores(c));
        },
        rl3::Step::Walk1 { core, va, l0ev }   => assert(post.inv_writer_cores(c)),
        rl3::Step::Walk2 { core, walk, l1ev } => assert(post.inv_writer_cores(c)),
        rl3::Step::Walk3 { core, walk, l2ev } => assert(post.inv_writer_cores(c)),
        rl3::Step::Walk4 { core, walk, l3ev } => assert(post.inv_writer_cores(c)),
        rl3::Step::Walk { path } => {
            assert(post.inv_writer_cores(c));
        },
        rl3::Step::Write => {
            let core = lbl->Write_0;
            broadcast use lemma_writer_cores_insert;
            assert(pre.writer_cores() === set![] || pre.writer_cores() === set![core]);
            assert(post.inv_writer_cores(c));
            //if pre.no_other_writers(core) {
            //    if pre.writer_cores() === set![] {
            //        assert(post.inv_writer_cores(c))
            //    } else {
            //        assert(pre.writer_cores() === set![core]);
            //        assert(post.inv_writer_cores(c))
            //    }
            //} else {
            //    assert(post.inv_writer_cores(c))
            //}
        },
        rl3::Step::Writeback { core } => {
            assert(post.inv_writer_cores(c));
        },
        rl3::Step::Read => {
            assert(post.inv_writer_cores(c));
        },
        rl3::Step::Barrier => {
            let core = lbl->Barrier_0;
            assert(pre.writer_cores().len() <= 1);
            lemma_writer_cores_filter(pre.hist.writes, core);
            assert(post.writer_cores().len() <= pre.writer_cores().len());
            admit();
            assert(post.inv_writer_cores(c));
        },
        rl3::Step::Stutter => {
            assert(post.inv_writer_cores(c));
        },
    }
}

// TODO: Any way to reasonably broadcast this?
proof fn lemma_writer_cores_filter(s: Set<(Core, usize)>, core: Core)
    ensures
        s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).subset_of(s.map(|x:(_,_)| x.0)),
        s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).len() <= s.map(|x:(_,_)| x.0).len()
{
    assert(s.filter(|e:(Core, usize)| e.0 != core).map(|x:(_,_)| x.0).subset_of(s.map(|x:(_,_)| x.0)));
    admit();
}

broadcast proof fn lemma_writer_cores_insert(s: Set<(Core, usize)>, core: Core, addr: usize)
    // probably need finite
    //requires s.finite()
    ensures
        (#[trigger] s.insert((core, addr))).map(|x:(_,_)| x.0) == s.map(|x:(_,_)| x.0).insert(core)
{
    admit();
}


//proof fn next_step_preserves_inv_unchanged_walks_match_memory(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next_step(pre, post, c, step, lbl),
//    ensures post.inv_unchanged_walks_match_memory(c)
//{
//    admit(); // XXX: This invariant isn't true
//    match step {
//        rl3::Step::Invlpg => {
//            let core = lbl->Invlpg_0;
//
//            // TODO: two concerns:
//            // other processors might still see outdated walks because inflight walks on other
//            // processors aren't canceled?
//            //
//            // "The read of a paging-structure entry in translating an address being used to fetch
//            // an instruction may appear to execute before an earlier write to that
//            // paging-structure entry if there is no serializing instruction between the write and
//            // the instruction fetch. Note that the invalidating instructions identified in Section
//            // 4.10.4.1 are all serializing instructions."
//
//            assert forall|addr, value, walk, core1|
//                   c.valid_core(core1)
//                && #[trigger] post.walks[core1].contains(walk)
//                && walk.path().to_set().contains((addr, value))
//                && (forall|core2| #![auto] !post.hist.writes.contains((core2, addr)))
//                    implies #[trigger] post.read_from_mem_tso(core1, addr, value.entry as usize)
//            by {
//                assert(c.valid_core(core1));
//                assert(post.walks[core1].contains(walk));
//                assert(walk.path().to_set().contains((addr, value)));
//                assert(forall|core2| #![auto] !post.hist.writes.contains((core2, addr)));
//
//                assert(pre.walks[core1].contains(walk));
//
//                if forall|core2| #![auto] !pre.hist.writes.contains((core2, addr)) {
//                    assert(forall|core2| #![auto] !pre.hist.writes.contains((core2, addr)));
//                    assert(pre.read_from_mem_tso(core1, addr, value.entry as usize));
//                    assert(post.read_from_mem_tso(core1, addr, value.entry as usize));
//                } else {
//                    let core2 = choose|core2| #![auto] pre.hist.writes.contains((core2, addr));
//                    assert(pre.hist.writes.contains((core2, addr)));
//                    assert(!post.hist.writes.contains((core2, addr)));
//                    assert(core2 == core);
//                    assert(pre.sbuf[core] =~= seq![]);
//                    assert(core != core1);
//                    assert(post.sbuf[core1] =~= pre.sbuf[core1]);
//                    //assert(pre.read_from_mem_tso(core1, addr, value.entry as usize));
//
//                    assert(post.read_from_mem_tso(core1, addr, value.entry as usize));
//                }
//            };
//            assert(post.inv_unchanged_walks_match_memory(c));
//        },
//        rl3::Step::Walk1 { core, va, l0ev }   => assume(post.inv(c)),
//        rl3::Step::Walk2 { core, walk, l1ev } => assume(post.inv(c)),
//        rl3::Step::Walk3 { core, walk, l2ev } => assume(post.inv(c)),
//        rl3::Step::Walk4 { core, walk, l3ev } => assume(post.inv(c)),
//        rl3::Step::Walk { path } => {
//            assert(post.inv(c));
//        },
//        rl3::Step::Write => {
//            assume(post.inv(c))
//        },
//        rl3::Step::Writeback { core } => {
//            assume(post.inv(c));
//        },
//        rl3::Step::Read => {
//            assert(post.inv(c));
//        },
//        rl3::Step::Barrier => {
//            assume(post.inv(c));
//        },
//        rl3::Step::Stutter => {
//            assert(post.inv(c));
//        },
//    }
//}

//proof fn lemma_read_from_mem_tso_empty_sbuf(s1: State, s2: State, core1: Core, core2: Core, addr: usize, value: usize)
//    requires
//        s1.read_from_mem_tso(core1, addr, value),
//        s2.pt_mem@ == s1.pt_mem@,
//        s2.sbuf[core1] == s1.sbuf[core],
//    ensures s2.read_from_mem_tso(core2, addr, value)
//{
//}

//proof fn lemma_read_from_mem_tso(s1: State, s2: State, core: Core, addr: usize, value: usize)
//    requires
//        s1.read_from_mem_tso(core, addr, value),
//        s2.pt_mem@ == s1.pt_mem@,
//        s2.sbuf[core] == s1.sbuf[core],
//    ensures s2.read_from_mem_tso(core, addr, value)
//{
//}

mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::pt_mem::{ PTMem };
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;

    impl rl3::State {
        pub open spec fn interp(self, c: rl3::Constants) -> rl2::State {
            let writers = self.writer_cores();
            let pt_mem = if writers.len() == 0 {
                self.pt_mem
            } else if writers.len() == 1 {
                let wcore = writers.choose();
                self.sbuf[wcore].fold_left(self.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
            } else {
                // implies !self.happy
                arbitrary()
            };
            rl2::State {
                happy: self.happy,
                pt_mem: self.pt_mem, // + sbuf
                walks: self.walks,
                writes: self.hist.writes,
            }
        }
    }

    impl rl3::Constants {
        pub open spec fn interp(self) -> rl2::Constants {
            rl2::Constants {
                cores: self.cores,
            }
        }
    }

    impl rl3::Step {
        pub open spec fn interp(self) -> rl2::Step {
            match self {
                rl3::Step::Invlpg                     => rl2::Step::Invlpg,
                rl3::Step::Walk1 { core, va, l0ev }   => rl2::Step::Walk1 { core, va, l0ev },
                rl3::Step::Walk2 { core, walk, l1ev } => rl2::Step::Walk2 { core, walk, l1ev },
                rl3::Step::Walk3 { core, walk, l2ev } => rl2::Step::Walk3 { core, walk, l2ev },
                rl3::Step::Walk4 { core, walk, l3ev } => rl2::Step::Walk4 { core, walk, l3ev },
                rl3::Step::Walk { path }              => rl2::Step::Walk { path },
                rl3::Step::Write                      => rl2::Step::Write,
                rl3::Step::Writeback { core }         => rl2::Step::Stutter,
                rl3::Step::Read                       => rl2::Step::Read,
                rl3::Step::Barrier                    => rl2::Step::Barrier,
                rl3::Step::Stutter                    => rl2::Step::Stutter,
            }
        }
    }

    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
        requires
            pre.happy,
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl2::next_step(pre.interp(c), post.interp(c), c.interp(), step.interp(), lbl)
    {
        match step {
            rl3::Step::Invlpg => {
                assert(rl2::step_Invlpg(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
            rl3::Step::Walk1 { core, va, l0ev }        => {
                admit();
                assert(rl2::step_Walk1(pre.interp(c), post.interp(c), c.interp(), core, va, l0ev, lbl));
            },
            rl3::Step::Walk2 { core, walk, l1ev }      => {
                admit();
                assert(rl2::step_Walk2(pre.interp(c), post.interp(c), c.interp(), core, walk, l1ev, lbl));
            },
            rl3::Step::Walk3 { core, walk, l2ev }      => {
                admit();
                assert(rl2::step_Walk3(pre.interp(c), post.interp(c), c.interp(), core, walk, l2ev, lbl));
            },
            rl3::Step::Walk4 { core, walk, l3ev }      => {
                admit();
                assert(rl2::step_Walk4(pre.interp(c), post.interp(c), c.interp(), core, walk, l3ev, lbl));
            },
            rl3::Step::Walk { path } => {
                admit();
                let core = lbl->Walk_0;
                assert(rl2::step_Walk(pre.interp(c), post.interp(c), c.interp(), path, lbl));
            },
            rl3::Step::Write => {
                admit();
                assert(rl2::step_Write(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
            rl3::Step::Writeback { core } => {
                admit();
                assert(pre.no_other_writers(core));
                lemma_pt_mem_fold_writeback(pre, post, c, core);
                assert(rl2::step_Stutter(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
            rl3::Step::Read                      => {
                admit();
                assert(rl2::step_Read(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
            rl3::Step::Barrier                   => {
                assert(rl2::step_Barrier(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
            rl3::Step::Stutter                   => {
                assert(rl2::step_Stutter(pre.interp(c), post.interp(c), c.interp(), lbl));
            },
        }
    }

    proof fn next_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants)
        requires
            pre.inv(c),
            rl3::next(pre, post, c),
        ensures
            rl2::next(pre.interp(c), post.interp(c), c.interp()),
    {
        if pre.happy {
            // TODO: ...
            assume(exists|x:(rl3::Step, Lbl)| #[trigger] rl3::next_step(pre, post, c, x.0, x.1));
            let (step, lbl) = choose|x:(rl3::Step, Lbl)| #[trigger] rl3::next_step(pre, post, c, x.0, x.1);
            next_step_refines(pre, post, c, step, lbl);
        }
    }


    proof fn lemma_pt_mem_fold_writeback(pre: rl3::State, post: rl3::State, c: rl3::Constants, core: Core)
        requires
            pre.happy,
            pre.inv(c),
            c.valid_core(core),
            pre.sbuf[core].len() > 0,
            pre.no_other_writers(core),
            post.pt_mem == pre.pt_mem.write(pre.sbuf[core][0].0, pre.sbuf[core][0].1),
            post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first()),
        ensures
            post.sbuf[core].fold_left(pre.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
                == pre.sbuf[core].fold_left(post.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    {
        admit();
    }

}


} // verus!
