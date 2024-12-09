use vstd::prelude::*;
use vstd::assert_by_contradiction;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, Core, bit, WORD_SIZE };
use crate::spec_t::mmu::rl4::{ Writes, MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 3 of the MMU. Compared to layer 4, it expresses translation
// caching and non-atomic walks as a single concept, and it doesn't explicitly consider the values
// of dirty/accessed bits.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    pub writes: Writes,
    pub hist: History,
    ///// Current polarity: Are we doing only positive writes or only negative writes? Polarity can be
    ///// flipped when neg and writes are all empty.
    ///// A non-flipping write with the wrong polarity sets happy to false.
    ///// Additionally tracks the current writer core.
    ///// Technically we could probably infer the polarity from the write tracking but this is easier.
    //pub polarity: Polarity,
}

pub struct History {
    pub pending_maps: Map<usize, PTE>,
}


impl State {
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize) -> usize {
        self.mem_view_of_core(core).read(addr)
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn writer_sbuf(self) -> Seq<(usize, usize)> {
        self.sbuf[self.writes.core]
    }

    /// The memory as seen by the given core. I.e. taking into consideration the core's store
    /// buffers.
    pub open spec fn mem_view_of_core(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    /// The view of the memory from the writer core's perspective.
    pub open spec fn mem_view_of_writer(self) -> PTMem {
        self.mem_view_of_core(self.writes.core)
    }

    pub open spec fn writer_mem_prefix(self, n: int) -> PTMem
        recommends 0 <= n <= self.sbuf[self.writes.core].len()
    {
        self.pt_mem.write_seq(self.sbuf[self.writes.core].take(n))
    }

    // TODO: I may want/need to add these conditions as well:
    // - when unmapping directory, it must be empty
    // - the location corresponds to *exactly* one leaf entry in the page table
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize, c: Constants) -> bool {
        &&& !self.writes.all.is_empty() ==> core == self.writes.core
        &&& self.mem_view_of_writer().is_nonneg_write(addr, value)
        //&&& !self.can_change_polarity(c) ==> {
        //    // If we're not at the start of an operation, the writer must stay the same
        //    &&& self.polarity.core() == core
        //    // and the polarity must match
        //    &&& if self.polarity is Pos { self.mem_view_of_writer().is_nonneg_write(addr) } else { self.mem_view_of_writer().is_neg_write(addr) }
        //}
        // The write must be to a location that's currently a leaf of the page table.
        // FIXME: i'm not sure this is doing what i want it to do.
        // TODO: maybe bad trigger
        //&&& exists|path, i| #![auto]
        //    self.mem_view_of_writer().page_table_paths().contains(path)
        //    && 0 <= i < path.len() && path[i].0 == addr
    }

    pub open spec fn pending_map_for(self, va: usize) -> bool {
        exists|vb| {
        &&& #[trigger] self.hist.pending_maps.contains_key(vb)
        &&& vb <= va < vb + self.hist.pending_maps[vb].frame.size
        }
    }

    //pub open spec fn can_change_polarity(self, c: Constants) -> bool {
    //    &&& self.writes.all.is_empty()
    //    &&& forall|core| #![auto] c.valid_core(core) ==> self.writes.neg[core].is_empty()
    //}

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& c.valid_core(self.writes.core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] self.walks.contains_key(core) ==> self.walks[core].finite()
        &&& forall|core| #[trigger] self.writes.neg.contains_key(core) ==> self.writes.neg[core].finite()
        // TODO: maybe change this?
        &&& forall|va|   #[trigger] aligned(va as nat, 8) ==> self.pt_mem.mem.contains_key(va)
    }

    // Since we only have positive writes, all currently inflight walks are prefixes of existing
    // paths.
    //pub open spec fn inv_walks_are_prefixes(self, c: Constants) -> bool {
    //    forall|walk| self.walks.contains(walk) ==> ...
    //}

    pub open spec fn non_writer_sbufs_are_empty(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) && core != self.writes.core ==> self.sbuf[core] === seq![]
    }

    pub open spec fn writer_sbuf_entries_are_unique(self) -> bool {
        let sbuf = self.sbuf[self.writes.core];
        forall|i1, i2, a1: usize, a2: usize, v1: usize, v2: usize|
               0 <= i1 < sbuf.len()
            && 0 <= i2 < sbuf.len()
            && i1 != i2
            && sbuf[i1] == (a1, v1)
            && sbuf[i2] == (a2, v2)
                ==> a2 != a1
    }

    pub open spec fn writer_sbuf_entries_have_P_bit(self) -> bool {
        let sbuf = self.sbuf[self.writes.core];
        forall|i, a: usize, v: usize| 0 <= i < sbuf.len() && sbuf[i] == (a, v) ==> v & 1 == 1
    }

    pub open spec fn inv_sbuf_facts(self, c: Constants) -> bool {
        &&& self.non_writer_sbufs_are_empty(c)
        &&& self.writer_sbuf_entries_are_unique()
        &&& self.writer_sbuf_entries_have_P_bit()
    }

    pub open spec fn inv_walks_basic(self, c: Constants) -> bool {
        forall|core, walk|
            c.valid_core(core) && self.walks[core].contains(walk) ==> {
                &&& walk.path.len() <= 4
                &&& walk.path.len() == 3 ==> walk.complete
            }
    }

    /// Any inflight page table walks didn't read from addresses that currently have P=0.
    /// TODO: might be better to instead show that values at addresses in walk paths have P=1.
    pub open spec fn inv_walks_disjoint_with_present_bit_0_addrs(self, c: Constants) -> bool {
        forall|core, addr, walk, i| #![auto] {
            &&& c.valid_core(core)
            &&& self.mem_view_of_writer().read(addr) & 1 == 0
            &&& self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> walk.path[i].0 != addr
    }

    pub open spec fn inv_invalid_on_writer_is_invalid(self, c: Constants) -> bool {
        forall|core, addr| #![auto] {
            &&& c.valid_core(core)
            &&& self.mem_view_of_writer().read(addr) & 1 == 0
        } ==> self.mem_view_of_core(core).read(addr) & 1 == 0
    }

    // XXX: too weak to preserve currently. E.g. sbuf could contain (addr, 0), (addr, 1), (addr, 0)
    // Problem during writeback step preservation proof.
    pub open spec fn inv_walk_addr_is_same_on_writer(self, c: Constants) -> bool {
        forall|core, walk, i| #![auto] {
            &&& c.valid_core(core)
            &&& self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> self.mem_view_of_core(core).read(walk.path[i].0)
                == self.mem_view_of_writer().read(walk.path[i].0)
    }

    pub open spec fn inv_walk_entry_matches_current(self, c: Constants) -> bool {
        forall|core, walk, i| {
            &&& c.valid_core(core)
            &&& #[trigger] self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> {
            let mem = self.mem_view_of_core(core);
            let addr = (#[trigger] walk.path[i]).0;
            let entry = PDE { entry: mem.read(addr) as u64, layer: Ghost(i as nat) }@;
            walk.path[i].1 == entry
        }
    }

    pub open spec fn inv_walks_match_memory(self, c: Constants) -> bool {
        forall|core, walk, i| #![auto] {
            &&& c.valid_core(core)
            &&& self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> walk.path[i] == self.mem_view_of_writer().pt_walk(walk.vaddr).path[i]
    }

    pub open spec fn inv_walks_match_memory2(self, c: Constants) -> bool {
        forall|core, walk, n| {
            &&& c.valid_core(core)
            &&& self.walks[core].contains(walk)
            &&& n == walk.path.len()
        } ==> walk == #[trigger] iter_walk_aux(self.mem_view_of_core(core), walk.vaddr, sub(4, n))
    }

    // FIXME: rename
    pub open spec fn inv_x(self, c: Constants) -> bool {
        forall|core, addr| #![trigger self.mem_view_of_core(core).pt_walk(addr)]
            c.valid_core(core) ==> {
                let mem_core = self.mem_view_of_core(core);
                let mem_writer = self.mem_view_of_writer();
                match mem_core.pt_walk(addr).result() {
                    WalkResult::Valid { .. } =>
                        mem_core.pt_walk(addr) == mem_writer.pt_walk(addr),
                    WalkResult::Invalid { .. } =>
                        !self.pending_map_for(addr)
                            ==> mem_core.pt_walk(addr).result() == mem_writer.pt_walk(addr).result(),
                }
            }
    }

    // FIXME: rename
    /// If any non-writer core reads a value that has the P bit set, we know that no write for that address is
    /// in the writer's store buffer.
    pub open spec fn inv_valid_is_valid(self, c: Constants) -> bool {
        forall|core, addr: usize|
            c.valid_core(core) && aligned(addr as nat, 8) &&
            core != self.writes.core &&
            #[trigger] self.mem_view_of_core(core).read(addr) & 1 == 1
                ==> !self.sbuf[self.writes.core].contains_addr(addr)
    }

    //pub open spec fn inv_walks_match_memory(self, c: Constants) -> bool {
    //    forall|core, walk, i| #![auto] {
    //        &&& c.valid_core(core)
    //        &&& self.walks[core].contains(walk)
    //        &&& 0 <= i < walk.path.len()
    //    } ==> PDE {
    //            entry: self.mem_view_of_writer().read(walk.path[i].0) as u64,
    //            layer: Ghost(i as nat)
    //        }@ == walk.path[i].1
    //}

    // I think this is strong enough to preserve during writeback and implies (mem@ is submap of
    // mem_view_of_writer@)
    pub open spec fn inv_view_plus_sbuf_is_submap(self, c: Constants) -> bool {
        forall|n| 0 <= n < self.writer_sbuf().len()
            ==> (#[trigger] self.writer_mem_prefix(n))@.submap_of(self.writer_mem_prefix(n + 1)@)
    }

    pub open spec fn inv_1(self, c: Constants) -> bool {
        forall|vbase, pte| !self.pt_mem@.contains_key(vbase) && self.mem_view_of_writer()@.contains_pair(vbase, pte)
            ==> self.hist.pending_maps.contains_pair(vbase, pte)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        &&& self.inv_walks_basic(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        walks: pre.walks.insert(core, set![]),
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            neg: pre.writes.neg.insert(core, set![]),
            core: pre.writes.core,
        },
        hist: if core == pre.writes.core { History { pending_maps: map![] } } else { pre.hist },
        ..pre
    }
}


// ---- Non-atomic page table walks ----

pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau

    &&& c.valid_core(core)
    //&&& aligned(vaddr as nat, L3_ENTRY_SIZE as nat)
    //&&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.writes == pre.writes
    &&& post.hist.pending_maps == pre.hist.pending_maps
    //&&& post.polarity == pre.polarity
}

// This thing has to be opaque because the iterated if makes Z3 explode, especially but not only
// with how we use this function in `iter_walk`.
#[verifier(opaque)]
pub open spec fn walk_next(mem: PTMem, walk: Walk) -> Walk {
    let vaddr = walk.vaddr; let path = walk.path;
    let addr = if path.len() == 0 {
        add(mem.pml4, (l0_bits!(vaddr as u64) * WORD_SIZE) as usize)
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, (l1_bits!(vaddr as u64) * WORD_SIZE) as usize)
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, (l2_bits!(vaddr as u64) * WORD_SIZE) as usize)
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, (l3_bits!(vaddr as u64) * WORD_SIZE) as usize)
    } else { arbitrary() };

    let entry = PDE { entry: mem.read(addr) as u64, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory)
    };
    walk
}

//// TODO: might be easier to just spell out the whole thing and do case distinctions
//// Or may want to generate the path prefix set...
//pub open spec fn complete_walk(state: State, core: Core, walk: Walk) -> Walk
//    recommends walk.path.len() < 4 && !walk.complete
//    decreases 4 - walk.path.len()
//{
//    if walk.path.len() < 4 {
//        if walk.complete {
//            walk
//        } else {
//            complete_walk(state, core, walk_next(state, core, walk))
//        }
//    } else {
//        arbitrary()
//    }
//}

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre.mem_view_of_core(core), walk);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk_next))
    &&& post.writes == pre.writes
    &&& post.hist.pending_maps == pre.hist.pending_maps
    //&&& post.polarity == pre.polarity
}

pub open spec fn step_WalkDone(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    lbl: Lbl
    ) -> bool
{
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& {
    let walk_next = walk_next(pre.mem_view_of_core(core), walk);
    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.result() == walk_result
    &&& walk_next.complete
    }

    &&& post == pre
}


// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.is_this_write_happy(core, addr, value, c)
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.all === pre.writes.all.insert(addr)
    &&& post.writes.neg == if !pre.mem_view_of_writer().is_nonneg_write(addr, value) {
            pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.writes.neg }
    &&& post.writes.core == core
    &&& post.hist.pending_maps == pre.hist.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
    // Whenever this causes polarity to change and happy isn't set to false, the
    // conditions for polarity to change are satisfied (`can_change_polarity`)
    //&&& post.polarity == if pre.mem_view_of_writer().is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes
    &&& post.hist.pending_maps == pre.hist.pending_maps
    //&&& post.polarity == pre.polarity
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value & MASK_NEG_DIRTY_ACCESS == pre.read_from_mem_tso(core, addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            ..pre.writes
        },
        hist: if core == pre.writes.core { History { pending_maps: map![] } } else { pre.hist },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk },
    WalkDone { walk: Walk },
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                   => step_Invlpg(pre, post, c, lbl),
        Step::WalkInit { core, vaddr } => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk }  => step_WalkStep(pre, post, c, core, walk, lbl),
        Step::WalkDone { walk }        => step_WalkDone(pre, post, c, walk, lbl),
        Step::Write                    => step_Write(pre, post, c, lbl),
        Step::Writeback { core }       => step_Writeback(pre, post, c, core, lbl),
        Step::Read                     => step_Read(pre, post, c, lbl),
        Step::Barrier                  => step_Barrier(pre, post, c, lbl),
        Step::Stutter                  => step_Stutter(pre, post, c, lbl),
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

proof fn next_step_preserves_wf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        next_step(pre, post, c, step, lbl),
    ensures post.wf(c)
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


proof fn next_step_preserves_inv_sbuf_facts(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.happy ==> post.inv_sbuf_facts(c)
{
    match step {
        Step::Write => {
            let Lbl::Write(core, wraddr, value) = lbl else { arbitrary() };
            if post.happy {
                if core == pre.writes.core {
                    assert_by_contradiction!(post.writer_sbuf_entries_are_unique(), {
                        // XXX: This follows from the uniqueness of addresses in sbuf
                        assume(forall|i, a, v: usize| 0 <= i < pre.sbuf[core].len() && pre.sbuf[core][i] == (a, v) ==> pre.mem_view_of_writer().read(a) == v);
                    });
                } else {
                    // XXX: need an invariant that shows this from the knowledge we have about
                    // pre.writes from is_this_write_happy.
                    assume(pre.sbuf[pre.writes.core] === seq![]);
                    assert(post.non_writer_sbufs_are_empty(c));
                }
                assert(post.inv_sbuf_facts(c));
            }
        },
        _ => assert(post.inv_sbuf_facts(c)),
    }
}

proof fn next_step_preserves_inv_walks_disjoint_with_present_bit_0_addrs(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_walks_disjoint_with_present_bit_0_addrs(c),
        next_step(pre, post, c, step, lbl),
    ensures post.happy ==> post.inv_walks_disjoint_with_present_bit_0_addrs(c)
{
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            //assume(pre.single_writer()); // prove this in separate invariant
            // TODO: Why do I have to manually call this lemma? Broadcast doesn't work even
            // though I mention all the triggers.
            //broadcast use lemma_writer_sbuf_empty_implies_writer_mem_equal;
            assert(pre.sbuf[core].len() == 0);
            //lemma_writes_filter_empty_if_writer_core(pre, post);
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::WalkInit { core, vaddr } => {
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::WalkStep { core, walk } => {
            let walk_next = walk_next(pre.mem_view_of_core(core), walk);
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert forall|core2, addr, walk2, i| #![auto] {
                &&& c.valid_core(core2)
                    &&& post.mem_view_of_writer().read(addr) & 1 == 0
                    &&& post.walks[core2].contains(walk2)
                    &&& 0 <= i < walk2.path.len()
            } implies walk2.path[i].0 != addr by {
                if core2 == core && walk2 == walk_next {
                    // walk_next adds one more entry to the path and the resulting walk is not
                    // yet complete. This means the entry was a directory, which means the
                    // present bit is set.
                    admit();
                    assert(walk2.path[i].0 != addr);
                } else {
                    assert(walk2.path[i].0 != addr);
                }
            };
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::WalkDone { walk } => {
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::Write => {
            let Lbl::Write(core, wraddr, value) = lbl else { arbitrary() };
            assume(forall|addr| #[trigger] post.mem_view_of_writer().read(addr) == if addr == wraddr { value } else { pre.mem_view_of_writer().read(addr) });
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::Writeback { core } => {
            broadcast use lemma_writeback_preserves_writer_mem;
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::Read => {
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c))
        },
        Step::Barrier => {
            let core = lbl->Barrier_0;
            //assume(pre.single_writer()); // prove this in separate invariant
            // TODO: Why do I have to manually call this lemma? Broadcast doesn't work even
            // though I mention all the triggers.
            //broadcast use lemma_writer_sbuf_empty_implies_writer_mem_equal;
            //lemma_writes_filter_empty_if_writer_core(pre, post);
            assert(pre.sbuf[core].len() == 0);
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
        },
        Step::Stutter => assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c)),
    }

}

proof fn next_step_preserves_inv_x(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_x(c),
        next_step(pre, post, c, step, lbl),
        post.happy,
    ensures post.inv_x(c)
{
    assume(pre.sbuf[pre.writes.core].len() == 0 ==> forall|core| c.valid_core(core) ==> pre.mem_view_of_core(core) == pre.mem_view_of_writer());
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            //assert(pre.sbuf[core].len() == 0);
            //lemma_writes_filter_empty_if_writer_core(pre, post);
            //assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            //assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.hist.pending_maps == if core == pre.writes.core { map![] } else { pre.hist.pending_maps });
            assert(post.inv_x(c));
        },
        Step::WalkInit { core, vaddr } => {
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.inv_x(c));
        },
        Step::WalkStep { core, walk } => {
            let walk_next = walk_next(pre.mem_view_of_core(core), walk);
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.inv_x(c));
        },
        Step::WalkDone { walk } => {
            assert(post.inv_x(c));
        },
        Step::Write => {
            let Lbl::Write(core, wraddr, value) = lbl else { arbitrary() };
            assume(forall|addr| #[trigger] post.mem_view_of_writer().read(addr) == if addr == wraddr { value } else { pre.mem_view_of_writer().read(addr) });
            broadcast use pt_mem::PTMem::lemma_pt_walk;
            admit();
            assert(post.inv_x(c));
        },
        Step::Writeback { core } => {
            broadcast use lemma_writeback_preserves_writer_mem;
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assume(post.inv_x(c));
        },
        Step::Read => {
            assert(post.inv_x(c))
        },
        Step::Barrier => {
            let core = lbl->Barrier_0;
            assert(post.hist.pending_maps == if core == pre.writes.core { map![] } else { pre.hist.pending_maps });
            assert(post.inv_x(c));
        },
        Step::Stutter => assert(post.inv_x(c)),
    }
}

proof fn next_step_preserves_inv_valid_is_valid(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_valid_is_valid(c),
        pre.inv_sbuf_facts(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_valid_is_valid(c)
{
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.inv_valid_is_valid(c));
        },
        Step::WalkInit { core, vaddr } => {
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.inv_valid_is_valid(c));
        },
        Step::WalkStep { core, walk } => {
            let walk_next = walk_next(pre.mem_view_of_core(core), walk);
            assert(post.mem_view_of_writer() == pre.mem_view_of_writer());
            assert(forall|core| c.valid_core(core) ==> post.mem_view_of_core(core) == pre.mem_view_of_core(core));
            assert(post.inv_valid_is_valid(c));
        },
        Step::WalkDone { walk } => {
            assert(post.inv_valid_is_valid(c));
        },
        Step::Write => {
            let Lbl::Write(core, wraddr, value) = lbl else { arbitrary() };
            assert(post.writes.core == core);
            assert forall|core2, addr: usize| c.valid_core(core2) && aligned(addr as nat, 8)
                    && core2 != core
                    && #[trigger] post.mem_view_of_core(core2).read(addr) & 1 == 1
                implies !post.sbuf[core].contains_addr(addr)
            by {
                assert(core != core2);
                assert(forall|b:u64| b & 1 == 0 || b & 1 == 1) by (bit_vector);
                assert(pre.mem_view_of_writer().read(wraddr) & 1 == 0);
                if core == pre.writes.core {
                    if addr == wraddr {
                        assert_by_contradiction!(!pre.sbuf[core].contains_addr(addr), {
                            let i = choose|i| 0 <= i < pre.sbuf[core].len() && #[trigger] pre.sbuf[core][i] == (addr, pre.sbuf[core][i].1);
                            let (addr2, value2) = pre.sbuf[core][i];
                            assert(post.sbuf[core][i] == (addr2, value2));
                            let j = pre.sbuf[core].len() as int;
                            assert(post.sbuf[core][pre.sbuf[core].len() as int] == (addr, value));
                        });
                        assert(pre.mem_view_of_writer().read(wraddr) & 1 != 1);

                        assert(false) by {
                            assert(pre.mem_view_of_core(core2) == pre.pt_mem);
                            assert(pre.pt_mem.read(addr) & 1 == 1);
                            assert(pre.mem_view_of_writer().read(addr) & 1 != 1);
                            assert(!pre.sbuf[core].contains_addr(addr));
                            broadcast use pt_mem::PTMem::lemma_write_seq_idle;
                            assert(pre.mem_view_of_writer().read(addr) == pre.pt_mem.read(addr));
                        };
                    } else {
                        assert(addr != wraddr);
                        assert(pre.mem_view_of_core(core2).read(addr) & 1 == 1);
                        assert(!post.sbuf[core].contains_addr(addr));
                    }
                } else {
                    assert(post.writer_sbuf_entries_are_unique());
                    assert(!post.sbuf[core].contains_addr(addr));
                }
            };
            assert(post.inv_valid_is_valid(c));
        },
        Step::Writeback { core } => {
            let (wraddr, value) = pre.sbuf[core][0];
            assert(core == post.writes.core);
            assert(post.writes.core == pre.writes.core);
            assert forall|core2, addr: usize| c.valid_core(core2) && aligned(addr as nat, 8)
                    && core2 != post.writes.core
                    && #[trigger] post.mem_view_of_core(core2).read(addr) & 1 == 1
                implies !post.sbuf[post.writes.core].contains_addr(addr)
            by {
                assert(core2 != core);
                if addr == wraddr {
                    assert(post.writer_sbuf_entries_are_unique());
                    assert(pre.sbuf[core].contains_addr(addr));
                    assert(pre.sbuf[core][0] == (addr, value));
                    assert(!post.sbuf[core].contains_addr(addr));
                } else { // addr != wraddr
                    assert(pre.sbuf[core2] === seq![]);
                    assert(post.sbuf[core2] === seq![]);
                    assert(post.pt_mem.read(addr) == pre.pt_mem.read(addr));
                    assert(pre.mem_view_of_core(core2).read(addr) & 1 == 1);
                }
                assert(!post.sbuf[post.writes.core].contains_addr(addr));
            };
            assert(post.inv_valid_is_valid(c));
        },
        Step::Read => {
            assert(post.inv_valid_is_valid(c))
        },
        Step::Barrier => {
            let core = lbl->Barrier_0;
            assert(post.inv_valid_is_valid(c));
        },
        Step::Stutter => assert(post.inv_valid_is_valid(c)),
    }
}

proof fn lemma_valid_equal_reads(state: State, c: Constants, core: Core, addr: usize)
    requires
        state.inv_sbuf_facts(c),
        state.inv_valid_is_valid(c),
        c.valid_core(core),
        core != state.writes.core,
        aligned(addr as nat, 8),
        state.mem_view_of_core(core).read(addr) & 1 == 1,
        state.mem_view_of_core(core).mem.contains_key(addr),
    ensures state.mem_view_of_core(core).read(addr) == state.mem_view_of_writer().read(addr)
{
    state.pt_mem.lemma_write_seq_idle(state.sbuf[state.writes.core], addr);
    assert(state.mem_view_of_core(core).read(addr) == state.pt_mem.read(addr));
    assert(state.mem_view_of_writer().read(addr) == state.pt_mem.read(addr));
}

proof fn lemma_valid_equal_walks(state: State, c: Constants, core: Core, va: usize)
    requires
        state.wf(c),
        state.inv_sbuf_facts(c),
        state.inv_valid_is_valid(c),
        c.valid_core(core),
        core != state.writes.core,
    ensures ({
        let core_walk = state.mem_view_of_core(core).pt_walk(va);
        let writer_walk = state.mem_view_of_writer().pt_walk(va);
        core_walk.result() is Valid ==> core_walk == writer_walk
    })
{
    assume(state.mem_view_of_core(core).pml4 == state.pt_mem.pml4);
    assume(state.mem_view_of_writer().pml4 == state.pt_mem.pml4);
    let core_mem = state.mem_view_of_core(core);
    let core_walk = core_mem.pt_walk(va);
    let writer_mem = state.mem_view_of_writer();
    let writer_walk = writer_mem.pt_walk(va);

    assert(bit!(0u64) == 1) by (bit_vector);
    assume(aligned(state.pt_mem.pml4 as nat, 8));
    assert(forall|a1, a2| aligned(a1, 8) && aligned(a2, 8) ==> #[trigger] aligned(a1 + a2, 8));

    if core_walk.result() is Valid {
        let l0_idx = (l0_bits!(va as u64) * WORD_SIZE) as usize;
        let l1_idx = (l1_bits!(va as u64) * WORD_SIZE) as usize;
        let l2_idx = (l2_bits!(va as u64) * WORD_SIZE) as usize;
        let l3_idx = (l3_bits!(va as u64) * WORD_SIZE) as usize;
        assume(core_mem.pml4 + l0_idx < u64::MAX);
        assume(aligned(l0_idx as nat, 8));
        assume(aligned(l1_idx as nat, 8));
        assume(aligned(l2_idx as nat, 8));
        assume(aligned(l3_idx as nat, 8));
        let l0_addr = add(core_mem.pml4, l0_idx);
        let l0e = PDE { entry: core_mem.read(l0_addr) as u64, layer: Ghost(0) };
        // XXX: follows from state.wf()
        assume(core_mem.mem.contains_key(l0_addr));
        match l0e@ {
            GPDE::Directory { addr: l1_daddr, .. } => {
                lemma_valid_equal_reads(state, c, core, l0_addr);
                assert(l0e == PDE { entry: writer_mem.read(l0_addr) as u64, layer: Ghost(0) });
                assume(l1_daddr + l1_idx < u64::MAX);
                assume(aligned(l1_daddr as nat, 8));
                let l1_addr = add(l1_daddr, l1_idx);
                let l1e = PDE { entry: core_mem.read(l1_addr) as u64, layer: Ghost(1) };
                // XXX: follows from state.wf()
                assume(core_mem.mem.contains_key(l1_addr));
                match l1e@ {
                    GPDE::Directory { addr: l2_daddr, .. } => {
                        lemma_valid_equal_reads(state, c, core, l1_addr);
                        assert(l1e == PDE { entry: writer_mem.read(l1_addr) as u64, layer: Ghost(1) });
                        assume(l2_daddr + l2_idx < u64::MAX);
                        assume(aligned(l2_daddr as nat, 8));
                        let l2_addr = add(l2_daddr, l2_idx);
                        let l2e = PDE { entry: core_mem.read(l2_addr) as u64, layer: Ghost(2) };
                        // XXX: follows from state.wf()
                        assume(core_mem.mem.contains_key(l2_addr));
                        match l2e@ {
                            GPDE::Directory { addr: l3_daddr, .. } => {
                                lemma_valid_equal_reads(state, c, core, l2_addr);
                                assert(l2e == PDE { entry: writer_mem.read(l2_addr) as u64, layer: Ghost(2) });
                                assume(l3_daddr + l3_idx < u64::MAX);
                                assume(aligned(l3_daddr as nat, 8));
                                let l3_addr = add(l3_daddr, l3_idx);
                                let l3e = PDE { entry: core_mem.read(l3_addr) as u64, layer: Ghost(3) };
                                // XXX: follows from state.wf()
                                assume(core_mem.mem.contains_key(l3_addr));
                                match l3e@ {
                                    GPDE::Directory { .. } => {
                                        assert(false);
                                    },
                                    GPDE::Page { .. } => {
                                        lemma_valid_equal_reads(state, c, core, l3_addr);
                                        assert(l3e == PDE { entry: writer_mem.read(l3_addr) as u64, layer: Ghost(3) });
                                    },
                                    GPDE::Empty => {},

                                }
                            },
                            GPDE::Page { .. } => {
                                lemma_valid_equal_reads(state, c, core, l2_addr);
                                assert(l2e == PDE { entry: writer_mem.read(l2_addr) as u64, layer: Ghost(2) });
                            },
                            GPDE::Empty => {},
                        }
                    },
                    GPDE::Page { .. } => {
                        lemma_valid_equal_reads(state, c, core, l1_addr);
                        assert(l1e == PDE { entry: writer_mem.read(l1_addr) as u64, layer: Ghost(1) });
                    },
                    GPDE::Empty => {},
                }
            },
            _ => {
                assert(core_walk.result() is Invalid);
            },
        }
        assert(core_walk == writer_walk);
    }
}


broadcast proof fn lemma_writeback_preserves_writer_mem(pre: State, post: State, c: Constants, core: Core, addr: usize, value: usize)
    requires
        #[trigger] c.valid_core(core),
        0 < pre.sbuf[core].len(),
        (addr, value) == pre.sbuf[core][0],
        post.pt_mem == #[trigger] pre.pt_mem.write(addr, value),
        post.sbuf   == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    ensures #[trigger] post.mem_view_of_writer() == pre.mem_view_of_writer()
{
    //broadcast use lemma_foo;
    //lemma_foo(pre.mem_view_of_writer(), pre.sbuf[core]);
    //assert(pre.mem_view_of_writer() == pre.sbuf[core]);
    admit();
}

broadcast proof fn lemma_foo(m: PTMem, writes: Seq<(usize, usize)>)
    requires writes.len() > 0,
    ensures m.write_seq(writes) == #[trigger] m.write(writes[0].0, writes[0].1).write_seq(writes.drop_first())
{
    admit();
}

pub open spec fn iter_walk(mem: PTMem, vaddr: usize) -> Walk {
    iter_walk_aux(mem, vaddr, 4)
}

pub open spec fn iter_walk_aux(mem: PTMem, vaddr: usize, steps: nat) -> Walk {
    let walk = Walk { vaddr, path: seq![], complete: false };
    if steps > 0 {
        let walk = rl3::walk_next(mem, walk);
        if !walk.complete && steps > 1 {
            let walk = rl3::walk_next(mem, walk);
            if !walk.complete && steps > 2 {
                let walk = rl3::walk_next(mem, walk);
                if !walk.complete && steps > 3 {
                    let walk = rl3::walk_next(mem, walk);
                    walk
                } else { walk }
            } else { walk }
        } else { walk }
    } else { walk }
}

broadcast proof fn lemma_iter_walk_equals_pt_walk(mem: PTMem, vaddr: usize)
    ensures #[trigger] iter_walk(mem, vaddr) == mem.pt_walk(vaddr)
{
    reveal(walk_next);
    let walk = Walk { vaddr, path: seq![], complete: false };
    let walk = rl3::walk_next(mem, walk);
    let l0_idx = (l0_bits!(vaddr as u64) * WORD_SIZE) as usize;
    let l1_idx = (l1_bits!(vaddr as u64) * WORD_SIZE) as usize;
    let l2_idx = (l2_bits!(vaddr as u64) * WORD_SIZE) as usize;
    let l3_idx = (l3_bits!(vaddr as u64) * WORD_SIZE) as usize;
    let l0_addr = add(mem.pml4, l0_idx);
    let l0e = PDE { entry: mem.read(l0_addr) as u64, layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let walk = rl3::walk_next(mem, walk);
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: mem.read(l1_addr) as u64, layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let walk = rl3::walk_next(mem, walk);
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: mem.read(l2_addr) as u64, layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let walk = rl3::walk_next(mem, walk);
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: mem.read(l3_addr) as u64, layer: Ghost(3) };
                            assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)]);
                        },
                        _ => {
                            assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)]);
                        },
                    }
                },
                _ => {
                    assert(walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@)]);
                },
            }
        },
        _ => {
            assert(walk.path == seq![(l0_addr, l0e@)]);
        },
    }
}

proof fn lemma_iter_walk_result_vbase_equal(mem: PTMem, vaddr: usize)
    ensures iter_walk(mem, vaddr).path == iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).path
{
    reveal(rl3::walk_next);
    broadcast use lemma_bits_align_to_usize;
}

broadcast proof fn lemma_bits_align_to_usize(vaddr: usize)
    ensures
        #![trigger align_to_usize(vaddr, L1_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L2_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L3_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, 8)]
        l0_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE) as u64) == l0_bits!(vaddr as u64),
        l1_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE) as u64) == l1_bits!(vaddr as u64),
        l0_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE) as u64) == l0_bits!(vaddr as u64),
        l1_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE) as u64) == l1_bits!(vaddr as u64),
        l2_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE) as u64) == l2_bits!(vaddr as u64),
        l0_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE) as u64) == l0_bits!(vaddr as u64),
        l1_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE) as u64) == l1_bits!(vaddr as u64),
        l2_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE) as u64) == l2_bits!(vaddr as u64),
        l3_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE) as u64) == l3_bits!(vaddr as u64),
        l0_bits!(align_to_usize(vaddr, 8) as u64) == l0_bits!(vaddr as u64),
        l1_bits!(align_to_usize(vaddr, 8) as u64) == l1_bits!(vaddr as u64),
        l2_bits!(align_to_usize(vaddr, 8) as u64) == l2_bits!(vaddr as u64),
        l3_bits!(align_to_usize(vaddr, 8) as u64) == l3_bits!(vaddr as u64),
{
    let vaddr = vaddr as u64;
    let l1_es = L1_ENTRY_SIZE as u64;
    let l2_es = L2_ENTRY_SIZE as u64;
    let l3_es = L3_ENTRY_SIZE as u64;
    assert(l0_bits!(sub(vaddr, vaddr % l1_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l1_es == 512 * 512 * 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l1_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l1_es == 512 * 512 * 4096;
    assert(l0_bits!(sub(vaddr, vaddr % l2_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l2_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l2_bits!(sub(vaddr, vaddr % l2_es)) == l2_bits!(vaddr)) by (bit_vector)
        requires l2_es == 512 * 4096;
    assert(l0_bits!(sub(vaddr, vaddr % l3_es)) == l0_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l1_bits!(sub(vaddr, vaddr % l3_es)) == l1_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l2_bits!(sub(vaddr, vaddr % l3_es)) == l2_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l3_bits!(sub(vaddr, vaddr % l3_es)) == l3_bits!(vaddr)) by (bit_vector)
        requires l3_es == 4096;
    assert(l0_bits!(sub(vaddr, vaddr % 8)) == l0_bits!(vaddr)) by (bit_vector);
    assert(l1_bits!(sub(vaddr, vaddr % 8)) == l1_bits!(vaddr)) by (bit_vector);
    assert(l2_bits!(sub(vaddr, vaddr % 8)) == l2_bits!(vaddr)) by (bit_vector);
    assert(l3_bits!(sub(vaddr, vaddr % 8)) == l3_bits!(vaddr)) by (bit_vector);
}

mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;
    use crate::definitions_t::{ aligned };

    impl rl3::State {
        pub open spec fn interp(self) -> rl2::State {
            rl2::State {
                happy: self.happy,
                pt_mem: self.mem_view_of_writer(),
                writes: self.writes,
                pending_maps: self.hist.pending_maps,
            }
        }
    }

    impl rl3::Step {
        pub open spec fn interp(self, pre: rl3::State, lbl: Lbl) -> rl2::Step {
            match self {
                rl3::Step::Invlpg => rl2::Step::Invlpg,
                rl3::Step::WalkInit { core, vaddr } => rl2::Step::Stutter,
                rl3::Step::WalkStep { core, walk } => rl2::Step::Stutter,
                rl3::Step::WalkDone { walk } => {
                    let Lbl::Walk(core, walk_na_res) = lbl else { arbitrary() };
                    if core == pre.writes.core {
                        rl2::Step::Walk { vaddr: walk.vaddr }
                    } else {
                        match walk_na_res {
                            WalkResult::Valid { vbase, pte } => {
                                rl2::Step::Walk { vaddr: walk.vaddr }
                            },
                            WalkResult::Invalid { vaddr } => {
                                //let walk_a = pre.mem_view_of_writer().pt_walk(walk.vaddr);
                                if pre.pending_map_for(walk.vaddr) {
                                    let vb = choose|vb| {
                                        &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
                                        &&& vb <= walk.vaddr < vb + pre.hist.pending_maps[vb].frame.size
                                    };
                                    rl2::Step::WalkNA { vb }
                                } else {
                                    rl2::Step::Walk { vaddr: walk.vaddr }
                                }
                            },
                        }
                    }
                }
                rl3::Step::Write => rl2::Step::Write,
                rl3::Step::Writeback { core } => rl2::Step::Stutter,
                rl3::Step::Read => rl2::Step::Read,
                rl3::Step::Barrier => rl2::Step::Barrier,
                rl3::Step::Stutter => rl2::Step::Stutter,
            }
        }
    }

    proof fn next_step_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
        requires
            pre.happy,
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        match step {
            rl3::Step::Invlpg => {
                assert(rl2::step_Invlpg(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::WalkInit { core, vaddr } => {
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::WalkStep { core, walk } => {
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::WalkDone { walk } => {
                next_step_WalkDone_refines(pre, post, c, step, lbl);
            },
            rl3::Step::Write => {
                // XXX: This doesn't refine in the case where (pre.happy && !post.happy)
                //      (Should be fairly simple fix, just add happy conditions to problematic
                //      update or something)
                admit();
                assert(rl2::step_Write(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Writeback { core } => {
                broadcast use super::lemma_writeback_preserves_writer_mem;
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Read => {
                admit(); // XXX
                assert(rl2::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Barrier => {
                assert(rl2::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::Stutter => {
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    #[verifier::spinoff_prover]
    proof fn next_step_WalkDone_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
        requires
            step is WalkDone,
            pre.happy,
            pre.inv(c),
            rl3::next_step(pre, post, c, step, lbl),
        ensures rl2::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        let rl3::Step::WalkDone { walk } = step else { arbitrary() };
        let Lbl::Walk(core, walk_na_res) = lbl else { arbitrary() };
        let mem_core = pre.mem_view_of_core(core);
        let mem_writer = pre.mem_view_of_writer();
        // We get a completed walk, `walk_na`, with the result `walk_na_res`
        let walk_na = rl3::walk_next(mem_core, walk);
        assert(walk_na.complete);
        assert(walk_na.result() == walk_na_res);
        assert(walk_na.path.len() == walk.path.len() + 1) by {
            reveal(rl3::walk_next);
        };
        assert(forall|i| 0 <= i < walk.path.len() ==> walk_na.path[i] == walk.path[i]) by {
            reveal(rl3::walk_next);
        };

        // STEP 1: This walk has the same result if done on the same core but atomically.
        let walk_a_same_core = rl3::iter_walk(mem_core, walk.vaddr);
        assert(walk_a_same_core == walk_na) by {
            //rl3::lemma_iter_walk_result_vbase_equal(mem_core, walk.vaddr);
            // XXX: Should follow from path prefix being same in memory and last read being
            // done on current state (pre). Non-trivial but shouldn't be too hard.
            // Maybe something like inv_walks_match_memory2 (not sure i want that invariant).
            assume(walk_na == rl3::iter_walk(mem_core, walk.vaddr));
            reveal(rl3::walk_next);
        };
        assert(walk_a_same_core.result() == walk_na_res);

        // STEP 2: The atomic walk on this core is the same as an atomic walk on the writer's view
        // of the memory. (Or if not, it's in a region in `pre.pending_maps`.)
        let walk_a_writer_core = rl3::iter_walk(mem_writer, walk.vaddr);

        rl3::lemma_iter_walk_equals_pt_walk(mem_core, walk.vaddr);
        rl3::lemma_iter_walk_equals_pt_walk(mem_writer, walk.vaddr);
        assert(walk_a_writer_core == mem_writer.pt_walk(walk.vaddr));

        if core == pre.writes.core {
            // If the walk happens on the writer core, the two atomic walks are done on the same
            // memory, i.e. are trivially equal.
            assert(walk_a_writer_core == walk_a_same_core);
            assert(rl2::step_Walk(pre.interp(), post.interp(), c, walk.vaddr, lbl));
        } else {
            assume(pre.inv_sbuf_facts(c));
            assume(pre.inv_valid_is_valid(c));
            super::lemma_valid_equal_walks(pre, c, core, walk.vaddr);
            assume(forall|va| mem_core.pt_walk(va).result() is Invalid && !pre.pending_map_for(va) ==> #[trigger] mem_core.pt_walk(va).result() == mem_writer.pt_walk(va).result());
            match walk_a_same_core.result() {
                WalkResult::Valid { vbase, pte } => {
                    assert(walk_a_same_core == walk_a_writer_core);
                    assert(rl2::step_Walk(pre.interp(), post.interp(), c, walk.vaddr, lbl));
                },
                WalkResult::Invalid { vaddr: vaddr_res } => {
                    if pre.pending_map_for(walk.vaddr) {
                        let vb = choose|vb| {
                            &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
                            &&& vb <= walk.vaddr < vb + pre.hist.pending_maps[vb].frame.size
                        };
                        assume(aligned(walk.vaddr as nat, 8));
                        assert(align_to_usize(walk.vaddr, 8) == walk.vaddr);
                        assert(rl2::step_WalkNA(pre.interp(), post.interp(), c, vb, lbl));
                    } else {
                        assert(walk_a_same_core.result() == walk_a_writer_core.result());
                        assert(rl2::step_Walk(pre.interp(), post.interp(), c, walk.vaddr, lbl));
                    }
                },
            }
        }
    }

    pub broadcast proof fn lemma_take_len<A>(s: Seq<A>)
        ensures #[trigger] s.take(s.len() as int) == s
        decreases s.len()
    {
        vstd::seq_lib::lemma_seq_properties::<A>();
        if s === seq![] {
        } else {
            lemma_take_len(s.drop_first());
        }
    }

    pub broadcast proof fn lemma_submap_of_trans<K,V>(m1: Map<K,V>, m2: Map<K,V>, m3: Map<K,V>)
        requires
            #[trigger] m1.submap_of(m2),
            m2.submap_of(m3),
        ensures #[trigger] m1.submap_of(m3)
    {
        assert forall|k: K| #[trigger]
            m1.dom().contains(k) implies #[trigger] m3.dom().contains(k) && m1[k] == m3[k]
        by { assert(m2.dom().contains(k)); };
    }


    proof fn lemma_mem_interp_is_submap_of_writer_mem_interp(state: rl3::State, c: Constants)
        requires state.inv_view_plus_sbuf_is_submap(c)
        ensures state.pt_mem@.submap_of(state.mem_view_of_writer()@)
    {
        lemma_take_len(state.sbuf[state.writes.core]);
        lemma_mem_interp_is_submap_of_writer_mem_interp_aux(state, c, state.sbuf[state.writes.core].len() as int);
    }

    proof fn lemma_mem_interp_is_submap_of_writer_mem_interp_aux(state: rl3::State, c: Constants, n: int)
        requires
            state.inv_view_plus_sbuf_is_submap(c),
            0 <= n <= state.sbuf[state.writes.core].len(),
        ensures state.pt_mem@.submap_of(state.writer_mem_prefix(n)@)
        decreases n
    {
        if n == 0 {
        } else {
            lemma_mem_interp_is_submap_of_writer_mem_interp_aux(state, c, n - 1);
            assert(state.pt_mem@.submap_of(state.writer_mem_prefix(n - 1)@));
            let (addr, value) = state.sbuf[state.writes.core][n - 1];
            assume(state.writer_mem_prefix(n) == state.writer_mem_prefix(n - 1).write(addr, value));
            broadcast use lemma_submap_of_trans;
            assert(state.writer_mem_prefix(n - 1)@.submap_of(state.writer_mem_prefix(n)@));
            assert(state.pt_mem@.submap_of(state.writer_mem_prefix(n)@));
        }
    }


    //proof fn next_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, lbl: Lbl)
    //    requires
    //        pre.inv(c),
    //        rl3::next(pre, post, c, lbl),
    //    ensures
    //        rl2::next(pre.interp(), post.interp(), c, lbl),
    //{
    //    if pre.happy {
    //        let step = choose|step: rl3::Step| rl3::next_step(pre, post, c, step, lbl);
    //        next_step_refines(pre, post, c, step, lbl);
    //    }
    //}


    //proof fn lemma_pt_mem_fold_writeback(pre: rl3::State, post: rl3::State, c: rl3::Constants, core: Core)
    //    requires
    //        pre.happy,
    //        pre.inv(c),
    //        c.valid_core(core),
    //        pre.sbuf[core].len() > 0,
    //        pre.no_other_writers(core),
    //        post.pt_mem == pre.pt_mem.write(pre.sbuf[core][0].0, pre.sbuf[core][0].1),
    //        post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first()),
    //    ensures
    //        post.sbuf[core].fold_left(pre.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    //            == pre.sbuf[core].fold_left(post.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    //{
    //    admit();
    //}
    //
    //proof fn lemma_rl3_read_from_mem_tso_conditions1(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
    //    requires
    //        state.happy,
    //        state.inv(c),
    //        !state.write_addrs().contains(addr),
    //        c.valid_core(core),
    //    ensures get_last(state.sbuf[core], addr) is None
    //{
    //    admit();
    //    assert(get_last(state.sbuf[core], addr) is None);
    //}
    //
    //proof fn lemma_rl3_read_from_mem_tso_conditions2(state: rl3::State, c: rl3::Constants, core: Core, addr: usize)
    //    requires
    //        state.happy,
    //        state.inv(c),
    //        state.no_other_writers(core),
    //        c.valid_core(core),
    //    ensures
    //        match get_last(state.sbuf[core], addr) {
    //            Some(v) => v,
    //            None    => state.pt_mem.read(addr),
    //        } == state.interp().pt_mem.read(addr)
    //{
    //    let wcore = state.writer_cores().choose();
    //    assume(wcore == core);
    //    assume(state.writer_cores().len() == 1);
    //    // Should follow trivially from previous two
    //    assume(state.interp().pt_mem == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1)));
    //    //match get_last(state.sbuf[core], addr) {
    //    //    Some(v) => v,
    //    //    None    => state.pt_mem[addr],
    //    //} == state.sbuf[core].fold_left(state.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))@[addr]
    //    admit();
    //    assert(get_last(state.sbuf[core], addr) is None);
    //}

}


} // verus!
