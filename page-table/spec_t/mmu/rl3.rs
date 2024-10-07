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
    /// Page table memory
    pub pt_mem: PTMem,
    /// In-progress page table walks
    pub walks: Map<Core, Set<PTWalk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    /// Addresses that have been used in a page table walk
    /// TODO: This can probably be at least partially reset in invlpg.
    pub used_addrs: Set<usize>,
    /// History variables.
    pub hist: History,
}

pub struct History {
    /// All writes that happened since the most recent invlpg.
    pub writes: Set<usize>,
}

impl State {
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

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
    }

    pub open spec fn inv_unchanged_walks_match_memory(self, c: Constants) -> bool {
        forall|addr, value, walk, core1, core2|
               c.valid_core(core1)
            && c.valid_core(core2)
            && #[trigger] self.walks[core1].contains(walk)
            && walk.path().to_set().contains((addr, value))
            && !self.hist.writes.contains(addr)
                ==> #[trigger] self.read_from_mem_tso(core2, addr, value.entry as usize)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.wf(c)
        &&& self.inv_unchanged_walks_match_memory(c)
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

    // .. and cancels inflight walks.
    &&& post.walks == pre.walks.insert(core, set![])
    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes === set![]
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(new_walk))
    &&& post.used_addrs == pre.used_addrs.insert(addr)

    &&& post.hist.writes == pre.hist.writes
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
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
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes.insert(addr)
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem@ == pre.pt_mem@.insert(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks
    &&& post.used_addrs == pre.used_addrs

    &&& post.hist.writes == pre.hist.writes
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
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
    match step {
        rl3::Step::Invlpg => {
            assert(forall|addr| !post.hist.writes.contains(addr));
            assert forall|addr, value, walk, core1, core2|
                   c.valid_core(core1)
                && c.valid_core(core2)
                && #[trigger] post.walks[core1].contains(walk)
                && walk.path().to_set().contains((addr, value))
                && !post.hist.writes.contains(addr)
                    implies #[trigger] post.read_from_mem_tso(core2, addr, value.entry as usize)
            by {
                assert(c.valid_core(core1));
                assert(c.valid_core(core2));
                assert(pre.walks[core1].contains(walk));
                assert(walk.path().to_set().contains((addr, value)));
                // FIXME: this is not true and the invariant is wrong. Invariant needs to be
                // specialized to cores, I think.
                assume(!pre.hist.writes.contains(addr));
                assert(pre.read_from_mem_tso(core2, addr, value.entry as usize));
            };
            //assert(c.valid_core(core1
            //lemma_read_from_mem_tso(pre, post, core2,
            assert(post.inv(c));
        },
        rl3::Step::Walk1 { core, va, l0ev }   => assume(post.inv(c)),
        rl3::Step::Walk2 { core, walk, l1ev } => assume(post.inv(c)),
        rl3::Step::Walk3 { core, walk, l2ev } => assume(post.inv(c)),
        rl3::Step::Walk4 { core, walk, l3ev } => assume(post.inv(c)),
        rl3::Step::Walk { path } => {
            assume(post.inv(c));
        },
        rl3::Step::Write => {
            assume(post.inv(c))
        },
        rl3::Step::Writeback { core } => {
            assume(post.inv(c));
        },
        rl3::Step::Read => {
            assert(post.inv(c));
        },
        rl3::Step::Barrier => {
            assert(post.inv(c));
        },
        rl3::Step::Stutter => {
            assert(post.inv(c));
        },
    }
}

//proof fn lemma_read_from_mem_tso_empty_sbuf(s1: State, s2: State, core1: Core, core2: Core, addr: usize, value: usize)
//    requires
//        s1.read_from_mem_tso(core1, addr, value),
//        s2.pt_mem@ == s1.pt_mem@,
//        s2.sbuf[core1] == s1.sbuf[core],
//    ensures s2.read_from_mem_tso(core2, addr, value)
//{
//}

proof fn lemma_read_from_mem_tso(s1: State, s2: State, core: Core, addr: usize, value: usize)
    requires
        s1.read_from_mem_tso(core, addr, value),
        s2.pt_mem@ == s1.pt_mem@,
        s2.sbuf[core] == s1.sbuf[core],
    ensures s2.read_from_mem_tso(core, addr, value)
{
}




mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl3;
    use crate::spec_t::mmu::rl4;

    impl rl4::State {
        pub open spec fn interp(self) -> rl3::State {
            rl3::State {
                pt_mem: self.pt_mem,
                walks: self.hist.walks,
                sbuf: self.sbuf,
                used_addrs: self.used_addrs,
                hist: rl3::History { writes: self.hist.writes },
            }
        }
    }

    impl rl4::Constants {
        pub open spec fn interp(self) -> rl3::Constants {
            rl3::Constants {
                cores: self.cores,
            }
        }
    }

    impl rl4::Step {
        pub open spec fn interp(self) -> rl3::Step {
            match self {
                rl4::Step::Invlpg                     => rl3::Step::Invlpg,
                rl4::Step::CacheFill { core, walk }   => rl3::Step::Stutter,
                rl4::Step::CacheUse { core, e }       => rl3::Step::Stutter,
                rl4::Step::CacheEvict { core, e }     => rl3::Step::Stutter,
                rl4::Step::Walk1 { core, va, l0ev }   => rl3::Step::Walk1 { core, va, l0ev },
                rl4::Step::Walk2 { core, walk, l1ev } => rl3::Step::Walk2 { core, walk, l1ev },
                rl4::Step::Walk3 { core, walk, l2ev } => rl3::Step::Walk3 { core, walk, l2ev },
                rl4::Step::Walk4 { core, walk, l3ev } => rl3::Step::Walk4 { core, walk, l3ev },
                rl4::Step::WalkCancel { core, walk }  => rl3::Step::Stutter,
                rl4::Step::Walk { path }              => rl3::Step::Walk { path },
                rl4::Step::Write                      => rl3::Step::Write,
                rl4::Step::Writeback { core }         => rl3::Step::Writeback { core },
                rl4::Step::Read                       => rl3::Step::Read,
                rl4::Step::Barrier                    => rl3::Step::Barrier,
            }
        }
    }

    proof fn next_refines(pre: rl4::State, post: rl4::State, c: rl4::Constants, step: rl4::Step, lbl: Lbl)
        requires
            pre.inv(c),
            rl4::next_step(pre, post, c, step, lbl),
        ensures rl3::next_step(pre.interp(), post.interp(), c.interp(), step.interp(), lbl)
    {
        match step {
            rl4::Step::Invlpg => {
                assert(rl3::step_Invlpg(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheFill { core, walk }  => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheUse { core, e }      => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::CacheEvict { core, e }    => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::Walk1 { core, va, l0ev }        => {
                assert(rl3::step_Walk1(pre.interp(), post.interp(), c.interp(), core, va, l0ev, lbl));
            },
            rl4::Step::Walk2 { core, walk, l1ev }      => {
                assert(c.valid_core(core));
                assert(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk2(pre.interp(), post.interp(), c.interp(), core, walk, l1ev, lbl));
            },
            rl4::Step::Walk3 { core, walk, l2ev }      => {
                assume(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk3(pre.interp(), post.interp(), c.interp(), core, walk, l2ev, lbl));
            },
            rl4::Step::Walk4 { core, walk, l3ev }      => {
                assume(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk4(pre.interp(), post.interp(), c.interp(), core, walk, l3ev, lbl));
            },
            rl4::Step::WalkCancel { core, walk } => {
                assert(rl3::step_Stutter(pre.interp(), post.interp(), c.interp(), lbl));

            },
            rl4::Step::Walk { path } => {
                let core = lbl->Walk_0;
                assume(pre.walks[core].subset_of(pre.hist.walks[core]));
                assert(rl3::step_Walk(pre.interp(), post.interp(), c.interp(), path, lbl));
            },
            rl4::Step::Write                     => {
                assert(rl3::step_Write(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::Writeback { core }        => {
                assert(rl3::step_Writeback(pre.interp(), post.interp(), c.interp(), core, lbl));
            },
            rl4::Step::Read                      => {
                assert(rl3::step_Read(pre.interp(), post.interp(), c.interp(), lbl));
            },
            rl4::Step::Barrier                   => {
                assert(rl3::step_Barrier(pre.interp(), post.interp(), c.interp(), lbl));
            },
        }
    }
}

} // verus!
