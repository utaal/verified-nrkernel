use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, Core };
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
    pub pending_maps: Set<(usize, PTE)>,
}


impl State {
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize) -> usize {
        let val = match get_last(self.sbuf[core], addr) {
            Some((_idx, v)) => v,
            None            => self.pt_mem.read(addr),
        };
        val
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn writer_sbuf(self) -> Seq<(usize, usize)> {
        self.sbuf[self.writes.core]
    }

    /// The view of the memory from the writer core's perspective.
    pub open spec fn writer_mem(self) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[self.writes.core])
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
        &&& self.writer_mem().is_nonneg_write(addr, value)
        //&&& !self.can_change_polarity(c) ==> {
        //    // If we're not at the start of an operation, the writer must stay the same
        //    &&& self.polarity.core() == core
        //    // and the polarity must match
        //    &&& if self.polarity is Pos { self.writer_mem().is_nonneg_write(addr) } else { self.writer_mem().is_neg_write(addr) }
        //}
        // The write must be to a location that's currently a leaf of the page table.
        // FIXME: i'm not sure this is doing what i want it to do.
        // TODO: maybe bad trigger
        //&&& exists|path, i| #![auto]
        //    self.writer_mem().page_table_paths().contains(path)
        //    && 0 <= i < path.len() && path[i].0 == addr
    }

    //pub open spec fn can_change_polarity(self, c: Constants) -> bool {
    //    &&& self.writes.all.is_empty()
    //    &&& forall|core| #![auto] c.valid_core(core) ==> self.writes.neg[core].is_empty()
    //}

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] self.walks.contains_key(core) ==> self.walks[core].finite()
        &&& forall|core| #[trigger] self.writes.neg.contains_key(core) ==> self.writes.neg[core].finite()
    }

    // Since we only have positive writes, all currently inflight walks are prefixes of existing
    // paths.
    //pub open spec fn inv_walks_are_prefixes(self, c: Constants) -> bool {
    //    forall|walk| self.walks.contains(walk) ==> ...
    //}

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
            &&& self.writer_mem().read(addr) & 1 == 0
            &&& self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> walk.path[i].0 != addr
    }

    pub open spec fn inv_walks_match_memory(self, c: Constants) -> bool {
        forall|core, walk, i| #![auto] {
            &&& c.valid_core(core)
            &&& self.walks[core].contains(walk)
            &&& 0 <= i < walk.path.len()
        } ==> walk.path[i] == self.writer_mem().pt_walk(walk.vaddr).path[i]
    }

    pub open spec fn inv_walks_match_memory2(self, c: Constants) -> bool {
        forall|core, walk, n| {
            &&& c.valid_core(core)
            &&& self.walks[core].contains(walk)
            &&& n == walk.path.len()
        } ==> walk == #[trigger] iter_walk_aux(self, core, walk.vaddr, n)
    }

    //pub open spec fn inv_walks_match_memory(self, c: Constants) -> bool {
    //    forall|core, walk, i| #![auto] {
    //        &&& c.valid_core(core)
    //        &&& self.walks[core].contains(walk)
    //        &&& 0 <= i < walk.path.len()
    //    } ==> PDE {
    //            entry: self.writer_mem().read(walk.path[i].0) as u64,
    //            layer: Ghost(i as nat)
    //        }@ == walk.path[i].1
    //}

    pub open spec fn inv_writer_sbuf(self, c: Constants) -> bool {
        forall|core| c.valid_core(core) && core != self.writes.core ==> (#[trigger] self.sbuf[core]).len() == 0
    }

    // I think this is strong enough to preserve during writeback and implies (mem@ is submap of writer_mem@)
    pub open spec fn inv_view_plus_sbuf_is_submap(self, c: Constants) -> bool {
        forall|n| 0 <= n < self.writer_sbuf().len()
            ==> (#[trigger] self.writer_mem_prefix(n))@.submap_of(self.writer_mem_prefix(n + 1)@)
    }

    pub open spec fn inv_1(self, c: Constants) -> bool {
        forall|vbase, pte| self.writer_mem()@.contains_pair(vbase, pte) && !self.pt_mem@.contains_pair(vbase, pte)
            ==> #[trigger] self.hist.pending_maps.contains((vbase, pte))
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

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.sbuf == pre.sbuf
    &&& post.writes.all === set![]
    &&& post.writes.neg == pre.writes.neg.insert(core, set![])
    &&& post.writes.core == pre.writes.core
    &&& post.hist.pending_maps === set![]
    //&&& post.polarity == pre.polarity
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

pub open spec fn walk_next(state: State, core: Core, walk: Walk) -> Walk {
    let vaddr = walk.vaddr; let path = walk.path;
    // TODO: do this better
    let addr = if path.len() == 0 {
        add(state.pt_mem.pml4, l0_bits!(vaddr as u64) as usize)
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, l1_bits!(vaddr as u64) as usize)
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, l2_bits!(vaddr as u64) as usize)
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, l3_bits!(vaddr as u64) as usize)
    } else { arbitrary() };
    let value = state.read_from_mem_tso(core, addr);

    let entry = PDE { entry: value as u64, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory)
    };
    walk
}

// TODO: might be easier to just spell out the whole thing and do case distinctions
// Or may want to generate the path prefix set...
pub open spec fn complete_walk(state: State, core: Core, walk: Walk) -> Walk
    recommends walk.path.len() < 4 && !walk.complete
    decreases 4 - walk.path.len()
{
    if walk.path.len() < 4 {
        if walk.complete {
            walk
        } else {
            complete_walk(state, core, walk_next(state, core, walk))
        }
    } else {
        arbitrary()
    }
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
    let walk_next = walk_next(pre, core, walk);
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
    value: usize,
    lbl: Lbl
    ) -> bool
{
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& {
    let walk_next = walk_next(pre, core, walk);
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
    &&& post.writes.neg == if !pre.writer_mem().is_nonneg_write(addr, value) {
            pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.writes.neg }
    &&& post.writes.core == core
    &&& post.hist.pending_maps == pre.hist.pending_maps.union(Set::new(|r:(_,_)|
            post.pt_mem@.contains_key(r.0)
            && !pre.pt_mem@.contains_key(r.0)
            && post.pt_mem@[r.0] == r.1
            ))
    // Whenever this causes polarity to change and happy isn't set to false, the
    // conditions for polarity to change are satisfied (`can_change_polarity`)
    //&&& post.polarity == if pre.writer_mem().is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
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

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    &&& post.writes.all === set![]
    &&& post.writes.neg == pre.writes.neg
    &&& post.writes.core == pre.writes.core
    &&& post.hist.pending_maps === set![]
    //&&& post.polarity == pre.polarity
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
    WalkStep { core: Core, walk: Walk, value: usize },
    WalkDone { walk: Walk, value: usize },
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                         => step_Invlpg(pre, post, c, lbl),
        Step::WalkInit { core, vaddr }       => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, value } => step_WalkStep(pre, post, c, core, walk, value, lbl),
        Step::WalkDone { walk, value }       => step_WalkDone(pre, post, c, walk, value, lbl),
        Step::Write                          => step_Write(pre, post, c, lbl),
        Step::Writeback { core }             => step_Writeback(pre, post, c, core, lbl),
        Step::Read                           => step_Read(pre, post, c, lbl),
        Step::Barrier                        => step_Barrier(pre, post, c, lbl),
        Step::Stutter                        => step_Stutter(pre, post, c, lbl),
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


proof fn next_step_preserves_inv_walks_disjoint_with_present_bit_0_addrs(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        pre.wf(c),
        pre.inv_walks_disjoint_with_present_bit_0_addrs(c),
        next_step(pre, post, c, step, lbl),
    ensures post.happy ==> post.inv_walks_disjoint_with_present_bit_0_addrs(c)
{
    if pre.happy {
        match step {
            Step::Invlpg => {
                let core = lbl->Invlpg_0;
                //assume(pre.single_writer()); // prove this in separate invariant
                // TODO: Why do I have to manually call this lemma? Broadcast doesn't work even
                // though I mention all the triggers.
                //broadcast use lemma_writer_sbuf_empty_implies_writer_mem_equal;
                assert(pre.sbuf[core].len() == 0);
                //lemma_writes_filter_empty_if_writer_core(pre, post);
                assert(post.writer_mem() == pre.writer_mem());
                assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
            },
            Step::WalkInit { core, vaddr } => {
                assert(post.writer_mem() == pre.writer_mem());
                assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
            },
            Step::WalkStep { core, walk, value } => {
                let walk_next = walk_next(pre, core, walk);
                assert(post.writer_mem() == pre.writer_mem());
                assert forall|core2, addr, walk2, i| #![auto] {
                    &&& c.valid_core(core2)
                    &&& post.writer_mem().read(addr) & 1 == 0
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
            Step::WalkDone { walk, value } => {
                assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
            },
            Step::Write => {
                let Lbl::Write(core, wraddr, value) = lbl else { arbitrary() };
                assume(forall|addr| #[trigger] post.writer_mem().read(addr) == if addr == wraddr { value } else { pre.writer_mem().read(addr) });
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
                assert(post.writer_mem() == pre.writer_mem());
                assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c));
            },
            Step::Stutter => assert(post.inv_walks_disjoint_with_present_bit_0_addrs(c)),
        }
    }
}

//broadcast proof fn lemma_writer_sbuf_empty_implies_writer_mem_equal(pre: State, post: State)
//    requires
//        pre.sbuf[pre.writes.core].len() == 0,
//        post.sbuf[post.writes.core].len() == 0,
//        post.pt_mem == pre.pt_mem,
//        post.writes.core == pre.writes.core 
//    ensures #[trigger] post.writer_mem() == #[trigger] pre.writer_mem()
//    //post.writes.all == if #[trigger] pre.is_writer_core(core) { set![] } else { pre.writes.all }
//{
//    assert(pre.sbuf[pre.writes.core].fold_left(pre.pt_mem, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1)) == pre.pt_mem);
//    assert(post.sbuf[post.writes.core].fold_left(post.pt_mem, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1)) == post.pt_mem);
//    //assert(pre.sbuf[core] =~= seq![]);
//}


broadcast proof fn lemma_writeback_preserves_writer_mem(pre: State, post: State, c: Constants, core: Core, addr: usize, value: usize)
    requires
        #[trigger] c.valid_core(core),
        0 < pre.sbuf[core].len(),
        (addr, value) == pre.sbuf[core][0],
        post.pt_mem == #[trigger] pre.pt_mem.write(addr, value),
        post.sbuf   == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    ensures #[trigger] post.writer_mem() == pre.writer_mem()
{
    //broadcast use lemma_foo;
    //lemma_foo(pre.writer_mem(), pre.sbuf[core]);
    //assert(pre.writer_mem() == pre.sbuf[core]);
    admit();
}

broadcast proof fn lemma_foo(m: PTMem, writes: Seq<(usize, usize)>)
    requires writes.len() > 0,
    ensures m.write_seq(writes) == #[trigger] m.write(writes[0].0, writes[0].1).write_seq(writes.drop_first())
{
    admit();
}

pub open spec fn iter_walk(state: rl3::State, core: Core, vaddr: usize) -> Walk {
    iter_walk_aux(state, core, vaddr, 4)
}

pub open spec fn iter_walk_aux(state: rl3::State, core: Core, vaddr: usize, steps: nat) -> Walk {
    let walk = Walk { vaddr, path: seq![], complete: false };
    if steps > 0 {
        let walk = rl3::walk_next(state, core, walk);
        if !walk.complete && steps > 1 {
            let walk = rl3::walk_next(state, core, walk);
            if !walk.complete && steps > 2 {
                let walk = rl3::walk_next(state, core, walk);
                if !walk.complete && steps > 3 {
                    let walk = rl3::walk_next(state, core, walk);
                    walk
                } else { walk }
            } else { walk }
        } else { walk }
    } else { walk }
}

broadcast proof fn lemma_iter_walk_next_equals_pt_walk_1(state: rl3::State, core: Core, vaddr: usize)
    requires core == state.writes.core
    ensures #[trigger] iter_walk(state, core, vaddr) == state.writer_mem().pt_walk(vaddr)
{
    assume(state.writer_mem().pml4 == state.pt_mem.pml4);
    let walk = Walk { vaddr, path: seq![], complete: false };
    let walk = rl3::walk_next(state, core, walk);
    let pt_mem = state.writer_mem();
    let l0_idx = l0_bits!(vaddr as u64) as usize;
    let l1_idx = l1_bits!(vaddr as u64) as usize;
    let l2_idx = l2_bits!(vaddr as u64) as usize;
    let l3_idx = l3_bits!(vaddr as u64) as usize;
    let l0_addr = add(pt_mem.pml4, l0_idx);
    assume(forall|a| state.read_from_mem_tso(core, a) == #[trigger] pt_mem.read(a));
    let l0e = PDE { entry: pt_mem.read(l0_addr) as u64, layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let walk = rl3::walk_next(state, core, walk);
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: pt_mem.read(l1_addr) as u64, layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let walk = rl3::walk_next(state, core, walk);
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: pt_mem.read(l2_addr) as u64, layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let walk = rl3::walk_next(state, core, walk);
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: pt_mem.read(l3_addr) as u64, layer: Ghost(3) };
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


// Behaves badly when broadcast (timeouts). 
proof fn lemma_iter_walk_result_vbase_equal(state: rl3::State, core: Core, vaddr: usize, vbase: usize)
    requires iter_walk(state, core, vaddr).result().vbase() == vbase
    ensures iter_walk(state, core, vaddr) == iter_walk(state, core, vbase)
{
    admit();
}

// TODO: This probably isn't useful for anything
broadcast proof fn lemma_iter_walk_next_equals_pt_walk_2(state: rl3::State, core: Core, vaddr: usize)
    requires core != state.writes.core
    ensures #[trigger] iter_walk(state, core, vaddr) == state.pt_mem.pt_walk(vaddr)
{
    let walk = Walk { vaddr, path: seq![], complete: false };
    let walk = rl3::walk_next(state, core, walk);
    let pt_mem = state.pt_mem;
    let l0_idx = l0_bits!(vaddr as u64) as usize;
    let l1_idx = l1_bits!(vaddr as u64) as usize;
    let l2_idx = l2_bits!(vaddr as u64) as usize;
    let l3_idx = l3_bits!(vaddr as u64) as usize;
    let l0_addr = add(pt_mem.pml4, l0_idx);
    assume(forall|a| state.read_from_mem_tso(core, a) == #[trigger] pt_mem.read(a));
    let l0e = PDE { entry: pt_mem.read(l0_addr) as u64, layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let walk = rl3::walk_next(state, core, walk);
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: pt_mem.read(l1_addr) as u64, layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let walk = rl3::walk_next(state, core, walk);
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: pt_mem.read(l2_addr) as u64, layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let walk = rl3::walk_next(state, core, walk);
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: pt_mem.read(l3_addr) as u64, layer: Ghost(3) };
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
        _ => { },
    }
}

mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;

    impl rl3::State {
        pub open spec fn interp(self) -> rl2::State {
            rl2::State {
                happy: self.happy,
                pt_mem: self.writer_mem(),
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
                rl3::Step::WalkStep { core, walk, value } => rl2::Step::Stutter,
                rl3::Step::WalkDone { walk, value } => {
                    let Lbl::Walk(core, walk_result) = lbl else { arbitrary() };
                    match walk_result {
                        WalkResult::Valid { vbase, pte } => {
                            rl2::Step::Walk
                        },
                        WalkResult::Invalid { vbase } => {
                            if exists|r| #[trigger]
                                pre.hist.pending_maps.contains(r)
                                && r.0 <= vbase < r.0 + r.1.frame.size
                            {
                                let r = choose|r| #[trigger] pre.hist.pending_maps.contains(r) && r.0 <= vbase < r.0 + r.1.frame.size;
                                rl2::Step::WalkNA { r }
                            } else {
                                rl2::Step::Walk
                            }
                        },
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
            rl3::Step::WalkStep { core, walk, value } => {
                assert(rl2::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl3::Step::WalkDone { walk, value } => {
                let Lbl::Walk(core, walk_result) = lbl else { arbitrary() };
                let walkn = rl3::walk_next(pre, core, walk);
                let vbase = walk_result.vbase();
                // XXX: Should follow from path prefix being same in memory and last read being
                // done on current state (pre). Non-trivial but shouldn't be too hard.
                assume(walkn == rl3::iter_walk(pre, core, walk.vaddr));
                rl3::lemma_iter_walk_result_vbase_equal(pre, core, walk.vaddr, vbase);
                assert(walkn == rl3::iter_walk(pre, core, vbase));
                let awalk = pre.writer_mem().pt_walk(vbase);
                assert(walkn.complete);
                assert(walkn.result() == walk_result);
                assume(pre.inv_walks_match_memory(c));
                assert(forall|i| 0 <= i < walk.path.len() ==> awalk.path[i] == walk.path[i]);
                //assume(pre.inv_view_plus_sbuf_is_submap(c));
                match walk_result {
                    WalkResult::Valid { vbase, pte } => {
                            //lemma_iter_walk_next_equals_pt_walk_2;
                        if core == pre.writes.core {
                            broadcast use rl3::lemma_iter_walk_next_equals_pt_walk_1;
                            //assert(walkn.path.last() == pre.writer_mem().pt_walk(vbase).path.last());
                            //assert(walkn.path =~= pre.writer_mem().pt_walk(vbase).path);
                            assert(rl2::step_Walk(pre.interp(), post.interp(), c, lbl));
                        } else {
                            // XXX: The walk result is Valid, so this entry (a Page mapping) has
                            //      P=1. We only allow positive writes, so the writer sbuf cannot
                            //      have another entry for this address.
                            //      Needs an invariant.
                            assume(pre.read_from_mem_tso(core, walkn.path.last().0) == pre.writer_mem().read(walkn.path.last().0));
                            //assert(walkn.path.last() == pre.writer_mem().pt_walk(vbase).path.last());
                            //assert(walkn.path =~= pre.writer_mem().pt_walk(vbase).path);
                            assert(rl2::step_Walk(pre.interp(), post.interp(), c, lbl));
                        }
                    },
                    WalkResult::Invalid { vbase } => {
                        if exists|r|
                            #[trigger] pre.hist.pending_maps.contains(r)
                            && r.0 <= vbase < r.0 + r.1.frame.size
                        {
                            let r = choose|r| #[trigger] pre.hist.pending_maps.contains(r) && r.0 <= vbase < r.0 + r.1.frame.size;
                            assert(rl2::step_WalkNA(pre.interp(), post.interp(), c, r, lbl));
                            //rl2::Step::WalkNA
                        } else {
                            assert(forall|r| #[trigger] pre.hist.pending_maps.contains(r)
                                    ==> !(r.0 <= vbase < r.0 + r.1.frame.size));
                            if core == pre.writes.core {
                                broadcast use rl3::lemma_iter_walk_next_equals_pt_walk_1;
                                assert(rl2::step_Walk(pre.interp(), post.interp(), c, lbl));
                            } else {
                                assume(pre.inv_1(c));
                                //forall|vbase, pte| self.writer_mem()@.contains_pair(vbase, pte) && !self.pt_mem@.contains_pair(vbase, pte)
                                //    ==> #[trigger] self.hist.pending_maps.contains((vbase, pte))
                                // XXX: Missing some kind of disjointness/no-overlap reasoning here
                                //      I think. I.e. When the walk for vbase returns invalid, all other
                                //      walks don't map regions that contain vbase.
                                //      XXX: No, this is wrong. I shouldn't need to reason about
                                //      this at all, I think. That probably means my if exists|..|
                                //      bla condition isn't the right thing yet
                                assume(forall|vb, pte| #[trigger] pre.pt_mem@.contains_pair(vb, pte)
                                        ==> !(vb <= vbase < vb + pte.frame.size));
                                admit();
                                assert(rl2::step_Walk(pre.interp(), post.interp(), c, lbl));
                            }
                        }
                    },
                }
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
