use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::definitions_t::{ aligned, bit, Core };

verus! {

// TODO: Should prove some basic liveness stuff, like: We can always make progress on an inflight
// partial walk.
// (forall walk in pre.walks. exists post. step_WalkStep(pre, post, walk, ..)

/// Bits 5 and 6 (dirty, access) set to 1
pub const MASK_DIRTY_ACCESS: usize = (bit!(5) | bit!(6)) as usize;

// This file contains refinement layer 4 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.

pub struct State {
    pub happy: bool,
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
    /// All partial walks since the last invlpg
    pub walks: Map<Core, Set<Walk>>,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    pub neg_writes: Map<Core, Set<usize>>,
}


impl State {
    /// This predicate is true whenever `value` is a value that might be read from the address
    /// `addr` on core `core`.
    ///
    /// We write this as a predicate rather than a function to specify the nondeterministic choice
    /// of the dirty and accessed bits. We could make an arbitrary choice for the bits in this
    /// function but that approach causes problems with the refinement, since the arbitrary choice
    /// must depend on the state, address and core.
    ///
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

    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores().subset_of(set![core])
        //self.writer_cores() === set![] || self.writer_cores() === set![core] 
        //forall|core2| #[trigger] c.valid_core(core2) && self.sbuf[core2].len() > 0 ==> core2 == core1
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.hist.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn is_neg_write(self, addr: usize) -> bool {
        &&& self.pt_mem.page_addrs().contains_key(addr)
        &&& !(self.pt_mem.page_addrs()[addr] is Empty)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.cache.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.hist.walks.contains_key(core)
    }

    pub open spec fn inv_walks_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) ==> self.walks[core].subset_of(self.hist.walks[core])
    }

    pub open spec fn inv_cache_subset_of_hist_walks(self, c: Constants) -> bool {
        forall|core,walk| c.valid_core(core) ==> #[trigger] self.cache[core].contains(walk) ==> self.hist.walks[core].contains(walk)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        // TODO:
        // invariant on walks and cache:
        // - The PDEs stored in `Partial` walks are always directories
        // - Length of paths in `Partial` walks in `walks` is always 1, 2 or 3
        // - Length of paths in `Valid` walks in `walks` is always 2, 3 or 4
        // - `Valid` walks always have a path made of directories, with a final page entry
        // - Length of paths in cache entries in `cache` is always 1, 2 or 3
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

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache

    &&& post.hist.walks == pre.hist.walks.insert(core, set![])
    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.neg_writes == pre.hist.neg_writes.insert(core, set![])
}


// ---- Translation caching ----

pub open spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].insert(walk))

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.cache[core].contains(walk)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache.insert(core, pre.cache[core].remove(walk))
    &&& post.walks == pre.walks

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
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
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(walk))
    &&& post.hist.writes === pre.hist.writes
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
    let (res, addr) = walk.next(pre.pt_mem.pml4(), value);
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& res is Incomplete

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk).insert(res.walk()))

    &&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(res.walk()))
    &&& post.hist.writes === pre.hist.writes
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
    let (res, addr) = walk.next(pre.pt_mem.pml4(), value);
    &&& lbl matches Lbl::Walk(core, walk_result)

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    //&&& walk.va == va
    &&& walk.pte() == walk_result
    &&& pre.read_from_mem_tso(core, addr, value)
    &&& !(res is Incomplete)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks.insert(core, pre.walks[core].remove(walk))

    &&& post.hist.walks == pre.hist.walks
    //&&& post.hist.walks == pre.hist.walks.insert(core, pre.hist.walks[core].insert(res.walk()))
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
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
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes.insert((core, addr))
    &&& post.hist.neg_writes == if pre.is_neg_write(addr) {
            pre.hist.neg_writes.map_values(|ws:Set<_>| ws.insert(addr))
        } else { pre.hist.neg_writes }
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.sbuf == pre.sbuf
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes
    &&& post.hist.neg_writes == pre.hist.neg_writes
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
    &&& post.cache == pre.cache
    &&& post.walks == pre.walks

    &&& post.hist.walks == pre.hist.walks
    &&& post.hist.writes === pre.hist.writes.filter(|e:(Core, usize)| e.0 != core)
    &&& post.hist.neg_writes == pre.hist.neg_writes
}

pub enum Step {
    // Mixed
    Invlpg,
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, va: usize },
    WalkStep { core: Core, walk: Walk, value: usize },
    WalkDone { walk: Walk, value: usize },
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                         => step_Invlpg(pre, post, c, lbl),
        Step::CacheFill { core, walk }       => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }        => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, walk }      => step_CacheEvict(pre, post, c, core, walk, lbl),
        Step::WalkInit { core, va }          => step_WalkInit(pre, post, c, core, va, lbl),
        Step::WalkStep { core, walk, value } => step_WalkStep(pre, post, c, core, walk, value, lbl),
        Step::WalkDone { walk, value }       => step_WalkDone(pre, post, c, walk, value, lbl),
        Step::Write                          => step_Write(pre, post, c, lbl),
        Step::Writeback { core }             => step_Writeback(pre, post, c, core, lbl),
        Step::Read                           => step_Read(pre, post, c, lbl),
        Step::Barrier                        => step_Barrier(pre, post, c, lbl),
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
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            assert(c.valid_core(core));
            assert(post.walks[core].is_empty());
            // TODO: Verus sets have some serious problems. How do I not know that a set with len 0
            // is the empty set..?
            // Really don't want to add finiteness invariants everywhere.
            assume(post.walks[core].finite());
            assume(post.cache[core].finite());
            assert(post.walks[core] === set![]);
            assert(post.hist.walks[core] =~= set![]);
            assert(post.inv(c))
        },
        Step::CacheFill { core, walk } => assert(post.inv(c)),
        Step::CacheUse { core, walk } => {
            assume(post.walks[core].finite());
            assert(post.inv(c))
        },
        Step::CacheEvict { core, walk } => assert(post.inv(c)),
        Step::WalkInit { core, va } => assert(post.inv(c)),
        Step::WalkStep { core, walk, value } => assert(post.inv(c)),
        Step::WalkDone { walk, value } => assert(post.inv(c)),
        Step::Write                      => assert(post.inv(c)),
        Step::Writeback { core }         => assert(post.inv(c)),
        Step::Read                       => assert(post.inv(c)),
        Step::Barrier                    => assert(post.inv(c)),
    }
}





mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl4;

    impl rl4::State {
        pub open spec fn interp(self) -> rl3::State {
            rl3::State {
                happy: self.happy,
                pt_mem: self.pt_mem,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                hist: rl3::History { writes: self.hist.writes, neg_writes: self.hist.neg_writes },
            }
        }
    }

    impl rl4::Step {
        pub open spec fn interp(self) -> rl3::Step {
            match self {
                rl4::Step::Invlpg                         => rl3::Step::Invlpg,
                rl4::Step::CacheFill { core, walk }       => rl3::Step::Stutter,
                rl4::Step::CacheUse { core, walk }        => rl3::Step::Stutter,
                rl4::Step::CacheEvict { core, walk }      => rl3::Step::Stutter,
                rl4::Step::WalkInit { core, va }          => rl3::Step::WalkInit { core, va },
                rl4::Step::WalkStep { core, walk, value } => rl3::Step::WalkStep { core, walk, value },
                rl4::Step::WalkDone { walk, value }       => rl3::Step::WalkDone { walk, value },
                rl4::Step::Write                          => rl3::Step::Write,
                rl4::Step::Writeback { core }             => rl3::Step::Writeback { core },
                rl4::Step::Read                           => rl3::Step::Read,
                rl4::Step::Barrier                        => rl3::Step::Barrier,
            }
        }
    }

    proof fn next_step_refines(pre: rl4::State, post: rl4::State, c: rl4::Constants, step: rl4::Step, lbl: Lbl)
        requires
            pre.happy,
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
            rl4::Step::WalkInit { core, va } => {
                assert(rl3::step_WalkInit(pre.interp(), post.interp(), c, core, va, lbl))
            },
            rl4::Step::WalkStep { core, walk, value } => {
                assert(rl3::step_WalkStep(pre.interp(), post.interp(), c, core, walk, value, lbl));
            },
            rl4::Step::WalkDone { walk, value } => {
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
            rl4::Step::Read                      => {
                assert(rl3::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl4::Step::Barrier                   => {
                assert(rl3::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    proof fn next_refines(pre: rl4::State, post: rl4::State, c: rl4::Constants)
        requires
            pre.inv(c),
            rl4::next(pre, post, c),
        ensures
            rl3::next(pre.interp(), post.interp(), c),
    {
        if pre.happy {
            // TODO: ...
            assume(exists|x:(rl4::Step, Lbl)| #[trigger] rl4::next_step(pre, post, c, x.0, x.1));
            let (step, lbl) = choose|x:(rl4::Step, Lbl)| #[trigger] rl4::next_step(pre, post, c, x.0, x.1);
            next_step_refines(pre, post, c, step, lbl);
        }
    }
}



pub open spec fn get_first_aux<A,B>(s: Seq<(A, B)>, i: int, a: A) -> Option<B>
    decreases s.len() - i
{
    if i >= s.len() {
        None
    } else {
        if s[i].0 == a {
            Some(s[i].1)
        } else {
            get_first_aux(s, i + 1, a)
        }
    }
}

pub open spec fn get_first<A,B>(s: Seq<(A, B)>, a: A) -> Option<B> {
    get_first_aux(s, 0, a)
}

} // verus!
