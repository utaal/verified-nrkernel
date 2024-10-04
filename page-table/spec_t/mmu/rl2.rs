use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ get_first, MASK_DIRTY_ACCESS };
use crate::spec_t::mmu::pt_mem::{ PTMem };
use crate::spec_t::hardware::{ Core, PageDirectoryEntry, GhostPageDirectoryEntry, l0_bits, l1_bits, l2_bits, l3_bits };
//use crate::spec_t::hardware::{ Core };
use crate::definitions_t::{ aligned, bitmask_inc };
//use crate::definitions_t::{ aligned };

verus! {

// This file contains refinement layer 2 of the MMU, which defines an atomic semantics for page
// table walks.

pub struct State {
    /// Page table memory
    pub pt_mem: PTMem,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    /// Addresses that have been used in a page table walk
    /// TODO: This can probably be at least partially reset in invlpg.
    pub used_addrs: Set<usize>,
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
}

// ---- Mixed (relevant to multiple of TSO/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    // Invlpg is a serializing instruction, ..
    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
    // TODO: This only works if invlpg in fact cancels all inflight walks. Otherwise we have to
    // take into account that writes stay relevant for certain pt walk translations but not others,
    // which may be very annoying to specify.
    &&& post.writes === set![]
}


// ---- Atomic page table walks ----

// FIXME: probably take a `path` argument instead of all this
pub open spec fn valid_walk(
    state: State,
    core: Core,
    va: usize,
    pte: Option<PageTableEntry>,
    l0addr: usize,
    l0ev: usize,
    l1addr: usize,
    l1ev: usize,
    l2addr: usize,
    l2ev: usize,
    l3addr: usize,
    l3ev: usize,
    ) -> bool
{
    let l0e = (l0addr, PageDirectoryEntry { entry: l0ev as u64, layer: Ghost(0) });
    &&& l0addr == add(state.pt_mem.pml4(), l0_bits!(va as u64) as usize)
    &&& state.read_from_mem_tso(core, l0addr, l0ev)
    &&& match l0e.1@ {
        GhostPageDirectoryEntry::Directory { addr, .. } => {
            let l1e = (l1addr, PageDirectoryEntry { entry: l1ev as u64, layer: Ghost(1) });
            &&& l1addr == add(addr, l1_bits!(va as u64) as usize)
            &&& state.read_from_mem_tso(core, l1addr, l1ev)
            &&& match l1e.1@ {
                GhostPageDirectoryEntry::Directory { addr, .. } => {
                    let l2e = (l2addr, PageDirectoryEntry { entry: l2ev as u64, layer: Ghost(2) });
                    &&& l2addr == add(addr, l2_bits!(va as u64) as usize)
                    &&& state.read_from_mem_tso(core, l2addr, l2ev)
                    &&& match l2e.1@ {
                        GhostPageDirectoryEntry::Directory { addr, .. } => {
                            let l3e = (l3addr, PageDirectoryEntry { entry: l3ev as u64, layer: Ghost(3) });
                            &&& l3addr == add(addr, l3_bits!(va as u64) as usize)
                            &&& state.read_from_mem_tso(core, l3addr, l3ev)
                            &&& match l3e.1@ {
                                GhostPageDirectoryEntry::Page { addr, .. } => {
                                    &&& aligned(va as nat, L3_ENTRY_SIZE as nat)
                                    &&& pte == Some(PTWalk::Valid { va, path: seq![l0e, l1e, l2e, l3e] }.pte())
                                },
                                GhostPageDirectoryEntry::Directory { .. }
                                | GhostPageDirectoryEntry::Empty => pte is None,
                            }
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => {
                            &&& aligned(va as nat, L2_ENTRY_SIZE as nat)
                            &&& pte == Some(PTWalk::Valid { va, path: seq![l0e, l1e, l2e] }.pte())
                        },
                        GhostPageDirectoryEntry::Empty => pte is None,
                    }
                },
                GhostPageDirectoryEntry::Page { addr, .. } => {
                    &&& aligned(va as nat, L1_ENTRY_SIZE as nat)
                    &&& pte == Some(PTWalk::Valid { va, path: seq![l0e, l1e] }.pte())
                },
                GhostPageDirectoryEntry::Empty => pte is None,
            }
        },
        GhostPageDirectoryEntry::Empty => pte is None,
        GhostPageDirectoryEntry::Page { .. } => arbitrary(), // No page mappings here
    }
}

pub open spec fn step_Walk(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, va, pte)

    //  (walk doesn't access any addresses in pre.writes) implies (pte can be determined atomically from TSO reads)

    //&&& arbitrary() ==> pte == arbitrary()

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
}


// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
// TODO: we don't model atomics, so technically the user-space threads cannot synchronize
// TODO: max physical size?
/// Write to core's local store buffer.
pub open spec fn step_Write(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& aligned(addr as nat, 8)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.used_addrs == pre.used_addrs
    &&& post.writes == pre.writes.insert(addr)
}

pub open spec fn step_Writeback(pre: State, post: State, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem@ == pre.pt_mem@.insert(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.used_addrs == pre.used_addrs
}

pub open spec fn step_Read(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
}

pub open spec fn step_Stutter(pre: State, post: State, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Atomic page table walks
    Walk,
    // TSO
    Write,
    Writeback { core: Core },
    Read,
    Barrier,
    Stutter,
}

pub open spec fn next_step(pre: State, post: State, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg             => step_Invlpg(pre, post, lbl),
        Step::Walk               => step_Walk(pre, post, lbl),
        Step::Write              => step_Write(pre, post, lbl),
        Step::Writeback { core } => step_Writeback(pre, post, core, lbl),
        Step::Read               => step_Read(pre, post, lbl),
        Step::Barrier            => step_Barrier(pre, post, lbl),
        Step::Stutter            => step_Stutter(pre, post, lbl),
    }
}

pub open spec fn next(pre: State, post: State, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, step, lbl)
}


mod refinement {
    //use crate::spec_t::mmu::*;
    //use crate::spec_t::mmu::rl3;
    //use crate::spec_t::mmu::rl4;
    //
    //impl rl4::State {
    //    pub open spec fn interp(self) -> rl3::State {
    //        rl3::State {
    //            pt_mem: self.pt_mem,
    //            walks: self.hist.walks,
    //            sbuf: self.sbuf,
    //            used_addrs: self.used_addrs,
    //        }
    //    }
    //}
    //
    //impl rl4::Step {
    //    pub open spec fn interp(self) -> rl3::Step {
    //        match self {
    //            rl4::Step::Invlpg                     => rl3::Step::Invlpg,
    //            rl4::Step::CacheFill { core, walk }   => rl3::Step::Stutter,
    //            rl4::Step::CacheUse { core, e }       => rl3::Step::Stutter,
    //            rl4::Step::CacheEvict { core, e }     => rl3::Step::Stutter,
    //            rl4::Step::Walk1 { core, va, l0ev }   => rl3::Step::Walk1 { core, va, l0ev },
    //            rl4::Step::Walk2 { core, walk, l1ev } => rl3::Step::Walk2 { core, walk, l1ev },
    //            rl4::Step::Walk3 { core, walk, l2ev } => rl3::Step::Walk3 { core, walk, l2ev },
    //            rl4::Step::Walk4 { core, walk, l3ev } => rl3::Step::Walk4 { core, walk, l3ev },
    //            rl4::Step::WalkCancel { core, walk }  => rl3::Step::Stutter,
    //            rl4::Step::Walk { path }              => rl3::Step::Walk { path },
    //            rl4::Step::Write                      => rl3::Step::Write,
    //            rl4::Step::Writeback { core }         => rl3::Step::Writeback { core },
    //            rl4::Step::Read                       => rl3::Step::Read,
    //            rl4::Step::Barrier                    => rl3::Step::Barrier,
    //        }
    //    }
    //}
    //
    //proof fn next_refines(pre: rl4::State, post: rl4::State, step: rl4::Step, lbl: Lbl)
    //    requires rl4::next_step(pre, post, step, lbl)
    //    ensures rl3::next_step(pre.interp(), post.interp(), step.interp(), lbl)
    //{
    //    match step {
    //        rl4::Step::Invlpg => {
    //            assert(rl3::step_Invlpg(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::CacheFill { core, walk }  => {
    //            assert(rl3::step_Stutter(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::CacheUse { core, e }      => {
    //            assert(rl3::step_Stutter(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::CacheEvict { core, e }    => {
    //            assert(rl3::step_Stutter(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::Walk1 { core, va, l0ev }        => {
    //            assert(rl3::step_Walk1(pre.interp(), post.interp(), core, va, l0ev, lbl));
    //        },
    //        rl4::Step::Walk2 { core, walk, l1ev }      => {
    //            assume(pre.walks[core].subset_of(pre.hist.walks[core]));
    //            assert(rl3::step_Walk2(pre.interp(), post.interp(), core, walk, l1ev, lbl));
    //        },
    //        rl4::Step::Walk3 { core, walk, l2ev }      => {
    //            assume(pre.walks[core].subset_of(pre.hist.walks[core]));
    //            assert(rl3::step_Walk3(pre.interp(), post.interp(), core, walk, l2ev, lbl));
    //        },
    //        rl4::Step::Walk4 { core, walk, l3ev }      => {
    //            assume(pre.walks[core].subset_of(pre.hist.walks[core]));
    //            assert(rl3::step_Walk4(pre.interp(), post.interp(), core, walk, l3ev, lbl));
    //        },
    //        rl4::Step::WalkCancel { core, walk } => {
    //            assert(rl3::step_Stutter(pre.interp(), post.interp(), lbl));
    //
    //        },
    //        rl4::Step::Walk { path } => {
    //            let core = lbl->Walk_0;
    //            //assume(pre.walks.contains_key(core));
    //            assume(pre.walks[core].subset_of(pre.hist.walks[core]));
    //            assert(rl3::step_Walk(pre.interp(), post.interp(), path, lbl));
    //        },
    //        rl4::Step::Write                     => {
    //            assert(rl3::step_Write(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::Writeback { core }        => {
    //            assert(rl3::step_Writeback(pre.interp(), post.interp(), core, lbl));
    //        },
    //        rl4::Step::Read                      => {
    //            assert(rl3::step_Read(pre.interp(), post.interp(), lbl));
    //        },
    //        rl4::Step::Barrier                   => {
    //            assert(rl3::step_Barrier(pre.interp(), post.interp(), lbl));
    //        },
    //    }
    //}
}

} // verus!
