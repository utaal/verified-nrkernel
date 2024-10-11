use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::rl4::{ MASK_DIRTY_ACCESS };
use crate::spec_t::mmu::pt_mem::{ PTMem };
//use crate::spec_t::hardware::{ Core, PageDirectoryEntry, GhostPageDirectoryEntry, l0_bits, l1_bits, l2_bits, l3_bits };
//use crate::definitions_t::{ aligned, bitmask_inc };
use crate::spec_t::hardware::{ Core, PageDirectoryEntry };
use crate::definitions_t::{ aligned };

verus! {

// This file contains refinement layer 1 of the MMU, which expresses page table walks as atomic
// operations on the global memory.

pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    ///// History variables.
    //pub hist: History,
}

pub struct History { }

impl State {
    pub open spec fn stutter(pre: State, post: State) -> bool {
        let State { happy, pt_mem, writes } = post;
        &&& happy == pre.happy
        &&& pt_mem@ == pre.pt_mem@
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

    pub open spec fn wf(self, c: Constants) -> bool {
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
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)
}


// ---- Atomic page table walks ----

pub open spec fn valid_walk(
    state: State,
    c: Constants,
    core: Core,
    va: usize,
    pte: Option<PageTableEntry>,
    path: Seq<(usize, PageDirectoryEntry)>,
    ) -> bool
{
    arbitrary()
    //let (l0addr, l0e) = path[0];
    //&&& path.len() >= 1
    //&&& l0e.layer@ == 0
    //&&& l0addr == add(state.pt_mem.pml4(), l0_bits!(va as u64) as usize)
    //&&& state.read_from_mem_tso(c, core, l0addr, l0e.entry as usize)
    //&&& match l0e@ {
    //    GhostPageDirectoryEntry::Directory { addr, .. } => {
    //        let (l1addr, l1e) = path[1];
    //        &&& path.len() >= 2
    //        &&& l1e.layer@ == 1
    //        &&& l1addr == add(addr, l1_bits!(va as u64) as usize)
    //        &&& state.read_from_mem_tso(c, core, l1addr, l1e.entry as usize)
    //        &&& match l1e@ {
    //            GhostPageDirectoryEntry::Directory { addr, .. } => {
    //                let (l2addr, l2e) = path[2];
    //                &&& path.len() >= 3
    //                &&& l2e.layer@ == 2
    //                &&& l2addr == add(addr, l2_bits!(va as u64) as usize)
    //                &&& state.read_from_mem_tso(c, core, l2addr, l2e.entry as usize)
    //                &&& match l2e@ {
    //                    GhostPageDirectoryEntry::Directory { addr, .. } => {
    //                        let (l3addr, l3e) = path[3];
    //                        &&& path.len() == 4
    //                        &&& l3e.layer@ == 3
    //                        &&& l3addr == add(addr, l3_bits!(va as u64) as usize)
    //                        &&& state.read_from_mem_tso(c, core, l3addr, l3e.entry as usize)
    //                        &&& match l3e@ {
    //                            GhostPageDirectoryEntry::Page { addr, .. } => {
    //                                &&& aligned(va as nat, L3_ENTRY_SIZE as nat)
    //                                &&& pte == Some(Walk { va, path }.pte())
    //                            },
    //                            GhostPageDirectoryEntry::Directory { .. }
    //                            | GhostPageDirectoryEntry::Empty => pte is None,
    //                        }
    //                    },
    //                    GhostPageDirectoryEntry::Page { addr, .. } => {
    //                        &&& aligned(va as nat, L2_ENTRY_SIZE as nat)
    //                        &&& path.len() == 3
    //                        &&& pte == Some(Walk { va, path }.pte())
    //                    },
    //                    GhostPageDirectoryEntry::Empty => {
    //                        &&& path.len() == 3
    //                        &&& pte is None
    //                    },
    //                }
    //            },
    //            GhostPageDirectoryEntry::Page { addr, .. } => {
    //                &&& aligned(va as nat, L1_ENTRY_SIZE as nat)
    //                &&& path.len() == 2
    //                &&& pte == Some(Walk { va, path }.pte())
    //            },
    //            GhostPageDirectoryEntry::Empty => {
    //                &&& path.len() == 2
    //                &&& pte is None
    //            },
    //        }
    //    },
    //    GhostPageDirectoryEntry::Empty => {
    //        &&& path.len() == 2
    //        &&& pte is None
    //    },
    //    GhostPageDirectoryEntry::Page { .. } => false, // No page mappings here
    //}
}

pub open spec fn step_Walk(pre: State, post: State, c: Constants, path: Seq<(usize, PageDirectoryEntry)>, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Walk(core, va, pte)

    &&& c.valid_core(core)
    //  (walk doesn't use any addresses in pre.writes) implies (pte can be determined atomically from TSO reads)
    //&&& pre.is_walk_atomic(path) ==> valid_walk(pre, core, va, pte, path)

    &&& post.pt_mem == pre.pt_mem
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
    &&& post.writes == pre.writes.insert((core, addr))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(c, core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.writes == pre.writes
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& State::stutter(pre, post)
}

pub enum Step {
    // Mixed
    Invlpg,
    // Atomic page table walks
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
