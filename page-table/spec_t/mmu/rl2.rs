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

pub struct Constants {
    pub cores: Set<Core>,
}

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

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.wf(c)
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

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
    // TODO: This only works if invlpg in fact cancels all inflight walks. Otherwise we have to
    // take into account that writes stay relevant for certain pt walk translations but not others,
    // which may be very annoying to specify.
    &&& post.writes === set![]
}


// ---- Atomic page table walks ----

pub open spec fn valid_walk(
    state: State,
    core: Core,
    va: usize,
    pte: Option<PageTableEntry>,
    path: Seq<(usize, PageDirectoryEntry)>,
    ) -> bool
{
    let (l0addr, l0e) = path[0];
    &&& path.len() >= 1
    &&& l0e.layer@ == 0
    &&& l0addr == add(state.pt_mem.pml4(), l0_bits!(va as u64) as usize)
    &&& state.read_from_mem_tso(core, l0addr, l0e.entry as usize)
    &&& match l0e@ {
        GhostPageDirectoryEntry::Directory { addr, .. } => {
            let (l1addr, l1e) = path[1];
            &&& path.len() >= 2
            &&& l1e.layer@ == 1
            &&& l1addr == add(addr, l1_bits!(va as u64) as usize)
            &&& state.read_from_mem_tso(core, l1addr, l1e.entry as usize)
            &&& match l1e@ {
                GhostPageDirectoryEntry::Directory { addr, .. } => {
                    let (l2addr, l2e) = path[2];
                    &&& path.len() >= 3
                    &&& l2e.layer@ == 2
                    &&& l2addr == add(addr, l2_bits!(va as u64) as usize)
                    &&& state.read_from_mem_tso(core, l2addr, l2e.entry as usize)
                    &&& match l2e@ {
                        GhostPageDirectoryEntry::Directory { addr, .. } => {
                            let (l3addr, l3e) = path[3];
                            &&& path.len() == 4
                            &&& l3e.layer@ == 3
                            &&& l3addr == add(addr, l3_bits!(va as u64) as usize)
                            &&& state.read_from_mem_tso(core, l3addr, l3e.entry as usize)
                            &&& match l3e@ {
                                GhostPageDirectoryEntry::Page { addr, .. } => {
                                    &&& aligned(va as nat, L3_ENTRY_SIZE as nat)
                                    &&& pte == Some(PTWalk::Valid { va, path }.pte())
                                },
                                GhostPageDirectoryEntry::Directory { .. }
                                | GhostPageDirectoryEntry::Empty => pte is None,
                            }
                        },
                        GhostPageDirectoryEntry::Page { addr, .. } => {
                            &&& aligned(va as nat, L2_ENTRY_SIZE as nat)
                            &&& path.len() == 3
                            &&& pte == Some(PTWalk::Valid { va, path }.pte())
                        },
                        GhostPageDirectoryEntry::Empty => {
                            &&& path.len() == 3
                            &&& pte is None
                        },
                    }
                },
                GhostPageDirectoryEntry::Page { addr, .. } => {
                    &&& aligned(va as nat, L1_ENTRY_SIZE as nat)
                    &&& path.len() == 2
                    &&& pte == Some(PTWalk::Valid { va, path }.pte())
                },
                GhostPageDirectoryEntry::Empty => {
                    &&& path.len() == 2
                    &&& pte is None
                },
            }
        },
        GhostPageDirectoryEntry::Empty => {
            &&& path.len() == 2
            &&& pte is None
        },
        GhostPageDirectoryEntry::Page { .. } => false, // No page mappings here
    }
}

pub open spec fn step_Walk(pre: State, post: State, c: Constants, path: Seq<(usize, PageDirectoryEntry)>, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& c.valid_core(core)
    //  (walk doesn't use any addresses in pre.writes) implies (pte can be determined atomically from TSO reads)
    &&& path.to_set().map(|e:(usize,PageDirectoryEntry)| e.0).disjoint(pre.writes) ==> valid_walk(pre, core, va, pte, path)

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
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.used_addrs == pre.used_addrs
    &&& post.writes == pre.writes.insert(addr)
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.pt_mem@ == pre.pt_mem@.insert(addr, value)
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.used_addrs == pre.used_addrs
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post.pt_mem == pre.pt_mem
    &&& post.sbuf == pre.sbuf
    &&& post.used_addrs == pre.used_addrs
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub enum Step {
    // Mixed
    Invlpg,
    // Atomic page table walks
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
        Step::Invlpg             => step_Invlpg(pre, post, c, lbl),
        Step::Walk { path }      => step_Walk(pre, post, c, path, lbl),
        Step::Write              => step_Write(pre, post, c, lbl),
        Step::Writeback { core } => step_Writeback(pre, post, c, core, lbl),
        Step::Read               => step_Read(pre, post, c, lbl),
        Step::Barrier            => step_Barrier(pre, post, c, lbl),
        Step::Stutter            => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}


mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl2;
    use crate::spec_t::mmu::rl3;

    impl rl3::State {
        pub open spec fn interp(self) -> rl2::State {
            rl2::State {
                pt_mem: self.pt_mem,
                sbuf: self.sbuf,
                used_addrs: self.used_addrs,
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
                rl3::Step::Walk1 { core, va, l0ev }   => rl2::Step::Stutter,
                rl3::Step::Walk2 { core, walk, l1ev } => rl2::Step::Stutter,
                rl3::Step::Walk3 { core, walk, l2ev } => rl2::Step::Stutter,
                rl3::Step::Walk4 { core, walk, l3ev } => rl2::Step::Stutter,
                rl3::Step::Walk { path }              => {
                    //let path = path.map_values(|e:(usize, PageDirectoryEntry)| (e.0, e.1.entry as usize));
                    rl2::Step::Walk { path }
                },
                rl3::Step::Write                      => rl2::Step::Write,
                rl3::Step::Writeback { core }         => rl2::Step::Writeback { core },
                rl3::Step::Read                       => rl2::Step::Read,
                rl3::Step::Barrier                    => rl2::Step::Barrier,
                rl3::Step::Stutter                    => rl2::Step::Stutter,
            }
        }
    }

    proof fn next_refines(pre: rl3::State, post: rl3::State, c: rl3::Constants, step: rl3::Step, lbl: Lbl)
        requires rl3::next_step(pre, post, c, step, lbl)
        ensures rl2::next_step(pre.interp(), post.interp(), c.interp(), step.interp(), lbl)
    {
        // TODO:
        // - probably need some sort of history variable for used_addrs to prove the WalkN steps
        //   - i might actually need more than that, maybe a phantom walk transition or something
        //     that can add "eligible" addresses to `used_addrs`
        let pre_i = pre.interp();
        let post_i = post.interp();
        let c_i = c.interp();
        match step {
            rl3::Step::Invlpg => {
                assert(rl2::step_Invlpg(pre_i, post_i, c_i, lbl));
            },
            rl3::Step::Walk1 { core, va, l0ev }   => assume(rl2::step_Stutter(pre_i, post_i, c_i, lbl)),
            rl3::Step::Walk2 { core, walk, l1ev } => assume(rl2::step_Stutter(pre_i, post_i, c_i, lbl)),
            rl3::Step::Walk3 { core, walk, l2ev } => assume(rl2::step_Stutter(pre_i, post_i, c_i, lbl)),
            rl3::Step::Walk4 { core, walk, l3ev } => assume(rl2::step_Stutter(pre_i, post_i, c_i, lbl)),
            rl3::Step::Walk { path }              => {
                //let path = path.map_values(|e:(usize, PageDirectoryEntry)| (e.0, e.1.entry as usize));
                assume(rl2::step_Walk(pre_i, post_i, c_i, path, lbl));
            },
            rl3::Step::Write => {
                assert(rl2::step_Write(pre_i, post_i, c_i, lbl));
            },
            rl3::Step::Writeback { core } => {
                assert(rl2::step_Writeback(pre_i, post_i, c_i, core, lbl));
            },
            rl3::Step::Read => {
                assert(rl2::step_Read(pre_i, post_i, c_i, lbl));
            },
            rl3::Step::Barrier => {
                assert(rl2::step_Barrier(pre_i, post_i, c_i, lbl));
            },
            rl3::Step::Stutter => {
                assert(rl2::step_Stutter(pre_i, post_i, c_i, lbl));
            },
        }
    }
}

} // verus!
