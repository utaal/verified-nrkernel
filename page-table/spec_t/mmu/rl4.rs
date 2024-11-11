use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::definitions_t::{ aligned, bit, Core };

verus! {

// TODO: Should prove some basic liveness stuff, like: We can always make progress on an inflight
// partial walk.
// (forall walk in pre.walks. exists post. step_WalkStep(pre, post, walk, ..)

pub const MASK_DIRTY_ACCESS: usize = (bit!(5) | bit!(6)) as usize;
pub const MASK_NEG_DIRTY_ACCESS: usize = !(bit!(5) | bit!(6)) as usize;

// This file contains refinement layer 4 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.

pub struct State {
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Translation caches
    pub cache: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    /// History variables. These are not allowed to influence transitions in any way. Neither in
    /// enabling conditions nor in how the state is updated.
    pub hist: History,
}

pub struct History {
    pub happy: bool,
    /// All partial walks since the last invlpg
    pub walks: Map<Core, Set<Walk>>,
    pub writes: Writes,
    ///// Current polarity: Are we doing only positive writes or only negative writes? Polarity can be
    ///// flipped when neg and writes are all empty.
    ///// A non-flipping write with the wrong polarity sets happy to false.
    ///// Additionally tracks the current writer core.
    ///// Technically we could probably infer the polarity from the write tracking but this is easier.
    //pub polarity: Polarity,
}

pub struct Writes {
    /// Tracks *all* writes. Gets cleared when the corresponding core drains its store buffer.
    /// These writes can cause TSO staleness.
    pub all: Set<(Core, usize)>,
    /// Tracks negative writes (to both page and directory mappings). Cleared for a particular core
    /// when it executes an invlpg.
    /// These writes can cause staleness due to partial translation caching or non-atomicity of
    /// walks.
    pub neg: Map<Core, Set<usize>>,
}

//pub enum Polarity {
//    Pos(Core),
//    Neg(Core),
//}
//
//impl Polarity {
//    pub open spec fn core(self) -> Core {
//        match self {
//            Polarity::Pos(c) => c,
//            Polarity::Neg(c) => c,
//        }
//    }
//}

impl State {
    /// FIXME: I changed this to always keep dirty/accessed bits nondeterministic rather than
    /// making it depend on `used_addrs`. If we keep the assumption that page table memory and user
    /// memory are disjoint, this is fine, otherwise we need to change it.
    /// Changing it shouldn't be too hard but it's probably worth first thinking a bit more about
    /// whether or not to give up that assumption. If we keep it, we need to discuss what exactly
    /// things mean. Currently the idea of the MMU state machines is that they model accesses to
    /// physical memory. We'd have to think about how to link different labels. (might not actually
    /// be an issue but should think it through)
    ///
    /// On later reflection: Ideally I wouldn't need to track `used_addrs` at all and could use
    /// `page_addrs` instead, which contains all addresses that might be used in a page table walk.
    /// But that's not true.............
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, r: usize) -> usize {
        let val = match get_first(self.sbuf[core], addr) {
            Some(v) => v,
            None    => self.pt_mem.read(addr),
        };
        val ^ (r & MASK_DIRTY_ACCESS)
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn is_writer_core(self, core: Core) -> bool {
        forall|c, a| #![auto] self.hist.writes.all.contains((c, a)) ==> c == core
    }

    pub open spec fn writer_core(self) -> Core {
        self.hist.writes.all.choose().0
    }

    /// The view of the memory from the writer core's perspective.
    pub open spec fn writer_mem(self) -> PTMem {
        let core = self.writer_core();
        self.sbuf[core].fold_left(self.pt_mem, |acc: PTMem, wr: (usize, usize)| acc.write(wr.0, wr.1))
    }

    // TODO: I may want/need to add these conditions as well:
    // - when unmapping directory, it must be empty
    // - the location corresponds to *exactly* one leaf entry in the page table
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, c: Constants) -> bool {
        &&& self.is_writer_core(core)
        &&& self.writer_mem().is_nonneg_write(addr)
        //&&& !self.can_change_polarity(c) ==> {
        //    // If we're not at the start of an operation, the writer must stay the same
        //    &&& self.hist.polarity.core() == core
        //    // and the polarity must match
        //    &&& if self.hist.polarity is Pos { self.writer_mem().is_nonneg_write(addr) } else { self.writer_mem().is_neg_write(addr) }
        //}
        //&&& if self.writer_mem().is_nonneg_write(addr)
        // The write must be to a location that's currently a leaf of the page table.
        // FIXME: i'm not sure this is doing what i want it to do.
        // TODO: maybe bad trigger
        //&&& exists|path, i| #![auto]
        //    self.writer_mem().page_table_paths().contains(path)
        //    && 0 <= i < path.len() && path[i].0 == addr
    }

    //pub open spec fn can_change_polarity(self, c: Constants) -> bool {
    //    &&& self.hist.writes.all.is_empty()
    //    &&& forall|core| #![auto] c.valid_core(core) ==> self.hist.writes.neg[core].is_empty()
    //}

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.cache.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].finite()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.cache[core].finite()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.walks[core].finite()
        &&& forall|core| #[trigger] c.valid_core(core) ==> self.hist.writes.neg[core].finite()
    }

    pub open spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].subset_of(self.hist.walks[core])
    }

    pub open spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core, walk|
            c.valid_core(core) && #[trigger] self.cache[core].contains(walk)
            ==> self.hist.walks[core].contains(walk)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.hist.happy ==> {
        &&& self.wf(c)
        &&& self.inv_walks_subset_of_hist_walks(c)
        &&& self.inv_cache_subset_of_hist_walks(c)
        }
    }
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0
    // .. evicts corresponding entries from the translation caches, ..
    // Note that per Intel Manual 3A, 4.10.4.1:
    // "INVLPG also invalidates all entries in all paging-structure caches associated with the
    // current PCID, regardless of the linear addresses to which they correspond."
    &&& pre.cache[core].is_empty()
    // .. and waits for inflight walks to complete.
    &&& pre.walks[core].is_empty()

    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks.insert(core, set![])
    &&& post.hist.writes.all === pre.hist.writes.all.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.writes.neg == pre.hist.writes.neg.insert(core, set![])
    //&&& post.hist.polarity == pre.hist.polarity
}


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].insert(walk))

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

pub open spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

pub open spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].remove(walk))
    &&& post.walks == pre.walks

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}


// ---- Non-atomic page table walks ----

// FIXME: this should make sure the alignment of va fits with the PTE
pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau

    &&& c.valid_core(core)
    //&&& aligned(vbase as nat, L3_ENTRY_SIZE as nat)
    // FIXME: What about bits in the virtual address above the indices? Do they need to be zero or
    // can we just ignore them?
    &&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk))
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

pub open spec fn walk_next(state: State, core: Core, walk: Walk, r: usize) -> Walk {
    let vaddr = walk.vaddr; let path = walk.path;
    // TODO: do this better
    let addr = if path.len() == 0 {
        add(state.pt_mem.pml4, l0_bits!(vaddr as u64) as usize)
    } else if path.len() == 1 {
        add(path.last().0, l1_bits!(vaddr as u64) as usize)
    } else if path.len() == 2 {
        add(path.last().0, l2_bits!(vaddr as u64) as usize)
    } else if path.len() == 3 {
        add(path.last().0, l3_bits!(vaddr as u64) as usize)
    } else { arbitrary() };
    let value = state.read_from_mem_tso(core, addr, r);

    let entry = PDE { entry: value as u64, layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory)
    };
    walk
}

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    value: usize,
    r: usize,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre, core, walk, r);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(walk_next))

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk_next))
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

/// Note: A valid walk's result is a region whose base and size depend on the path taken. E.g. a
/// huge page mapping results in a 2M-sized region. Invalid walks are always for a 4K-sized region.
pub open spec fn step_WalkDone(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    value: usize,
    r: usize,
    lbl: Lbl
    ) -> bool
{
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& {
    let walk_next = walk_next(pre, core, walk, r);
    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.result() == walk_result
    &&& walk_next.complete
    }

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    //&&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(res.walk()))
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.happy == pre.hist.happy && pre.is_this_write_happy(core, addr, c)
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all.insert((core, addr))
    &&& post.hist.writes.neg == if !pre.writer_mem().is_nonneg_write(addr) {
            pre.hist.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.hist.writes.neg }
    // Whenever this causes polarity to change and happy isn't set to false, the
    // conditions for polarity to change are satisfied (`can_change_polarity`)
    //&&& post.hist.polarity == if pre.writer_mem().is_neg_write(addr) { Polarity::Neg(core) } else { Polarity::Pos(core) }
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, r: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value == pre.read_from_mem_tso(core, addr, r)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.happy == pre.hist.happy
    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes.all === pre.hist.writes.all.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.writes.neg == pre.hist.writes.neg
    //&&& post.hist.polarity == pre.hist.polarity
}

/// Any transition that reads from memory takes an arbitrary usize `r`, which is used to
/// non-deterministically flip the accessed and dirty bits.
pub enum Step {
    // Mixed
    Invlpg,
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk, value: usize, r: usize },
    WalkDone { walk: Walk, value: usize, r: usize },
    // TSO
    Write,
    Writeback { core: Core },
    Read { r: usize },
    Barrier,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                            => step_Invlpg(pre, post, c, lbl),
        Step::CacheFill { core, walk }          => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }           => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, walk }         => step_CacheEvict(pre, post, c, core, walk, lbl),
        Step::WalkInit { core, vaddr }          => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, value, r } => step_WalkStep(pre, post, c, core, walk, value, r, lbl),
        Step::WalkDone { walk, value, r }       => step_WalkDone(pre, post, c, walk, value, r, lbl),
        Step::Write                             => step_Write(pre, post, c, lbl),
        Step::Writeback { core }                => step_Writeback(pre, post, c, core, lbl),
        Step::Read { r }                        => step_Read(pre, post, c, r, lbl),
        Step::Barrier                           => step_Barrier(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
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
    //if pre.hist.happy {
    //    match step {
    //        Step::Invlpg                            => assert(post.inv(c)),
    //        Step::CacheFill { core, walk }          => assert(post.inv(c)),
    //        Step::CacheUse { core, walk }           => assert(post.inv(c)),
    //        Step::CacheEvict { core, walk }         => assert(post.inv(c)),
    //        Step::WalkInit { core, vaddr }          => assert(post.inv(c)),
    //        Step::WalkStep { core, walk, value, r } => assert(post.inv(c)),
    //        Step::WalkDone { walk, value, r }       => assert(post.inv(c)),
    //        Step::Write                             => assert(post.inv(c)),
    //        Step::Writeback { core }                => assert(post.inv(c)),
    //        Step::Read { r }                        => assert(post.inv(c)),
    //        Step::Barrier                           => assert(post.inv(c)),
    //    }
    //}
}





mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl4;
    use crate::spec_t::mmu::rl4::bit;

    impl rl4::State {
        pub open spec fn interp(self) -> rl3::State {
            rl3::State {
                happy: self.hist.happy,
                pt_mem: self.pt_mem,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                writes: self.hist.writes,
                //polarity: self.hist.polarity,
            }
        }
    }

    impl rl4::Step {
        pub open spec fn interp(self) -> rl3::Step {
            match self {
                rl4::Step::Invlpg                            => rl3::Step::Invlpg,
                rl4::Step::CacheFill { core, walk }          => rl3::Step::Stutter,
                rl4::Step::CacheUse { core, walk }           => rl3::Step::Stutter,
                rl4::Step::CacheEvict { core, walk }         => rl3::Step::Stutter,
                rl4::Step::WalkInit { core, vaddr }          => rl3::Step::WalkInit { core, vaddr },
                rl4::Step::WalkStep { core, walk, value, r } => rl3::Step::WalkStep { core, walk, value },
                rl4::Step::WalkDone { walk, value, r }       => rl3::Step::WalkDone { walk, value },
                rl4::Step::Write                             => rl3::Step::Write,
                rl4::Step::Writeback { core }                => rl3::Step::Writeback { core },
                rl4::Step::Read { r }                        => rl3::Step::Read,
                rl4::Step::Barrier                           => rl3::Step::Barrier,
            }
        }
    }

    /// The value of r is irrelevant, so we can just ignore it.
    broadcast proof fn rl4_walk_next_is_rl3_walk_next(state: rl4::State, core: Core, walk: Walk, r: usize)
        ensures #[trigger] rl4::walk_next(state, core, walk, r) == rl3::walk_next(state.interp(), core, walk)
    {
        admit();
    }

    proof fn next_step_refines(pre: rl4::State, post: rl4::State, c: Constants, step: rl4::Step, lbl: Lbl)
        requires
            pre.hist.happy,
            pre.inv(c),
            rl4::next_step(pre, post, c, step, lbl),
        ensures rl3::next_step(pre.interp(), post.interp(), c, step.interp(), lbl)
    {
        match step {
            rl4::Step::Invlpg => {
                assert(rl3::step_Invlpg(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::CacheFill { core, walk }  => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::CacheUse { core, walk }      => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::CacheEvict { core, walk }    => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::WalkInit { core, vaddr } => {
                assert(rl3::step_WalkInit(pre.interp(), post.interp(), c, core, vaddr, lbl))
            },
            rl4::Step::WalkStep { core, walk, value, r } => {
                rl4_walk_next_is_rl3_walk_next(pre, core, walk, r);
                assert(rl3::step_WalkStep(pre.interp(), post.interp(), c, core, walk, value, lbl));
            },
            rl4::Step::WalkDone { walk, value, r } => {
                let core = lbl->Walk_0;
                rl4_walk_next_is_rl3_walk_next(pre, core, walk, r);
                assert(rl3::step_WalkDone(pre.interp(), post.interp(), c, walk, value, lbl));
            },
            rl4::Step::Write => {
                assert(rl3::step_Write(pre.interp(), post.interp(), c, lbl));
                //let core = lbl->Write_0;
                //if pre.no_other_writers(core) {
                //    assert(pre.interp().no_other_writers(core));
                //    assert(rl3::step_Write(pre.interp(), post.interp(), c, lbl));
                //} else {
                //    assert(rl3::step_Write(pre.interp(), post.interp(), c, lbl));
                //}
            },
            rl4::Step::Writeback { core }        => {
                assert(rl3::step_Writeback(pre.interp(), post.interp(), c, core, lbl));
            },
            rl4::Step::Read { r }                => {
                //let core = lbl->Read_0;
                //let addr = lbl->Read_1;
                //let value = lbl->Read_2;
                //let val = match rl4::get_first(pre.sbuf[core], addr) {
                //    Some(v) => v,
                //    None    => pre.pt_mem.read(addr),
                //};
                //assert(val == pre.interp().read_from_mem_tso(core, addr));
                //assert(value == val ^ (r & rl4::MASK_DIRTY_ACCESS));

                assert(forall|val: usize, r: usize| #![auto]
                    (val ^ (r & rl4::MASK_DIRTY_ACCESS)) & rl4::MASK_NEG_DIRTY_ACCESS
                        == val & rl4::MASK_NEG_DIRTY_ACCESS)
                by {
                    assert(forall|val: usize, r: usize| #![auto]
                        (val ^ (r & ((bit!(5) | bit!(6)) as usize))) & (!(bit!(5) | bit!(6)) as usize)
                            == val & (!(bit!(5) | bit!(6)) as usize)) by (bit_vector);
                };
                assert(rl3::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::Barrier                   => {
                assert(rl3::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    proof fn next_refines(pre: rl4::State, post: rl4::State, c: Constants, lbl: Lbl)
        requires
            pre.inv(c),
            rl4::next(pre, post, c, lbl),
        ensures
            rl3::next(pre.interp(), post.interp(), c, lbl),
    {
        if pre.hist.happy {
            let step = choose|step: rl4::Step| rl4::next_step(pre, post, c, step, lbl);
            next_step_refines(pre, post, c, step, lbl);
        }
    }
}


} // verus!
