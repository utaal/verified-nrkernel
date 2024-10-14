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
//
// Under which circumstances can we know that the result of a page table walk is the same as if it
// had happened atomically on the global memory?
//
// There are two sources of non-atomicity:
// 1. TSO.
//    If the walk uses an address, whose value is (on the core doing the walk) non-deterministic
//    because another core has written to it, then we can't say for sure what the result of the
//    walk is. The write first goes to the store buffer and then gets written back. We don't know
//    if the walk used the old or new value. In particular, it may have used the old value and then
//    the writeback happens, meaning it doesn't appear to be atomic. (Technically, we can drop this
//    condition if it's the last read of the walk, as it appears atomic then. But it wouldn't be
//    useful because we still don't know if the walk used the old or new value.)
//
//    A serializing instruction on the core that executed the write(s) guarantees that for
//    subsequent walks using the written-to address(es), this is not a problem. I.e. after a map or
//    unmap we need a serializing instruction on the core that did the operation.
//
//    **Note that here the non-determinism originates from things happening on the writer core
//    (store buffering) and an action (serializing instruction) needs to be executed by that core
//    to restore deterministic semantics for all other cores in the system.**
//
// 2. Translation caches and non-atomicity.
//    Even when TSO is not a problem, a core's inflight page table walk may have read an old value
//    before the newly written value was guaranteed to be visible.
//
//    **Unlike with TSO, the non-determinism here is caused by actions of the cores reading the
//    addresses to which another core is writing. Consequently, ensuring the absence of this type
//    of non-determinism can't be done by the writer core, only by actions on each reader core
//    (specifically, executing invlpg).**
//
//    However, we can differentiate between different kinds of writes. Only some of them induce
//    non-determinism in page table walks. Consider the set of all addresses reachable from the
//    page table's root address.
//    E.g. define S inductively. For root address `pml4`: (Implemented in function `page_addrs`)
//
//    1. {pml4, pml4 + 8, .., pml4 + 4088} subset S
//    2. If S contains `addr` and the value stored at `addr` is a valid entry pointing to a
//       directory stored at `addr2` then:
//       {addr2, addr2 + 8, .., addr2 + 4088} subset S
//
//    Whenever a write to some `addr` happens, there are three possibilities:
//    1. `addr` is not reachable from PML4
//       --> Neither caching nor non-atomicity could cause a page walk to depend on the current value
//           stored at `addr`. No non-determinism/non-atomicity is introduced (except through TSO
//           combined with a later write that would make `addr` reachable.).
//
//    2. `addr` is reachable from PML4. The old value stored at `addr` has P=0, i.e. is not a valid
//       paging entry.
//       --> Whenever a page walk encounters this entry, it terminates immediately. I.e. no
//           inflight walks rely on the old value. The entry also cannot be cached. No
//           non-determinism/non-atomicity.
//
//    3. `addr` is reachable from PML4. The old value stored at `addr` has P=1, i.e. is a valid entry
//       --> Any subsequent page table walk completions using `addr` have non-atomic semantics, as
//           they may depend on the old value. Executing an invlpg restores atomic semantics on
//           the core executing it.
//
//
//  Very interesting thing I just realized:
//  If a page table implementation doesn't reclaim directories eagerly when unmapping, it may see
//  the following situation: When mapping a huge page entry, it encounters an empty directory,
//  reclaims it and maps the huge page instead. After this, a shootdown is necessary. Otherwise
//  page table walks may still use the empty directory, causing a page fault rather than a
//  successful translation. Only caused by non-atomicity though. Translation caches cannot cache
//  prefixes of invalid walks. This may technically be a bug in NrOS.



pub struct State {
    pub happy: bool,
    /// Page table memory
    pub pt_mem: PTMem,
    /// All writes that may still be in store buffers. Gets reset for the executing core on invlpg
    /// and barrier.
    pub writes: Set<(Core, usize)>,
    /// "Negative writes" (P=1)->(P=?)
    /// Maps each core to a set of addresses. Each of the addresses was written to while reachable
    /// from PML4 with P=1 and the core did not yet execute an invlpg since that write.
    /// I.e. the old value at that address may still affect the results of future page table walks,
    /// through non-atomicity and partial translation caching.
    ///
    /// Note that `neg_writes` doesn't map each core to a set of writes executed *by that core* but
    /// to a set of writes whose effect this core may or may not yet observe.
    pub neg_writes: Map<Core, Set<usize>>,
    ///// "Positive writes" (P=0)->(P=1)
    ///// Maps each core to a set of addresses. Each of the addresses was written to while reachable
    ///// from PML4 with P=0.
    ///// The old value was invalid, thus cannot be present in any non-atomic or partially cached
    ///// translations.
    //pub pos_writes: Map<Core, Set<usize>>,
    ///// History variables.
    //pub hist: History,
}

pub struct History { }

impl State {
    pub open spec fn stutter(pre: State, post: State) -> bool {
        let State { happy, pt_mem, writes, neg_writes } = post;
        &&& happy == pre.happy
        &&& pt_mem@ == pre.pt_mem@
        &&& writes == pre.writes
    }

    pub open spec fn init(self) -> bool {
        arbitrary()
    }

    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize, value: usize) -> bool {
        self.is_tso_read_deterministic(core, addr)
            ==> value & MASK_DIRTY_ACCESS == self.pt_mem@[addr] & MASK_DIRTY_ACCESS
    }

    /// For the active writer core, the memory always behaves like a Map. For other cores this is
    /// only true for addresses that haven't been written to.
    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        ||| self.no_other_writers(core)
        ||| !self.write_addrs().contains(addr)
    }

    pub open spec fn is_walk_atomic(self, core: Core, path: Seq<(usize, PageDirectoryEntry)>) -> bool {
        let addrs = path.to_set().map(|x:(_,_)| x.0);
        forall|addr| #[trigger] addrs.contains(addr) ==> {
            // No TSO non-determinism:
            &&& self.is_tso_read_deterministic(core, addr)
            // No cache/partial-walk non-determinism:
            &&& !self.neg_writes[core].contains(addr)
        }
    }

    /// Is true if only this core's store buffer is non-empty.
    pub open spec fn no_other_writers(self, core: Core) -> bool {
        self.writer_cores().subset_of(set![core])
    }

    pub open spec fn writer_cores(self) -> Set<Core> {
        self.writes.map(|x:(_,_)| x.0)
    }

    pub open spec fn write_addrs(self) -> Set<usize> {
        self.writes.map(|x:(_,_)| x.1)
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& forall|core,value| #[trigger] self.writes.contains((core,value)) ==> c.valid_core(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.neg_writes.contains_key(core)
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
    &&& post.neg_writes == pre.neg_writes.insert(core, set![])
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
    //&&& state.read_from_mem_tso(core, l0addr, l0e.entry as usize)
    //&&& match l0e@ {
    //    GhostPageDirectoryEntry::Directory { addr, .. } => {
    //        let (l1addr, l1e) = path[1];
    //        &&& path.len() >= 2
    //        &&& l1e.layer@ == 1
    //        &&& l1addr == add(addr, l1_bits!(va as u64) as usize)
    //        &&& state.read_from_mem_tso(core, l1addr, l1e.entry as usize)
    //        &&& match l1e@ {
    //            GhostPageDirectoryEntry::Directory { addr, .. } => {
    //                let (l2addr, l2e) = path[2];
    //                &&& path.len() >= 3
    //                &&& l2e.layer@ == 2
    //                &&& l2addr == add(addr, l2_bits!(va as u64) as usize)
    //                &&& state.read_from_mem_tso(core, l2addr, l2e.entry as usize)
    //                &&& match l2e@ {
    //                    GhostPageDirectoryEntry::Directory { addr, .. } => {
    //                        let (l3addr, l3e) = path[3];
    //                        &&& path.len() == 4
    //                        &&& l3e.layer@ == 3
    //                        &&& l3addr == add(addr, l3_bits!(va as u64) as usize)
    //                        &&& state.read_from_mem_tso(core, l3addr, l3e.entry as usize)
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
    &&& pre.is_walk_atomic(core, path) ==> valid_walk(pre, c, core, va, pte, path)

    &&& post.pt_mem == pre.pt_mem
    &&& post.writes == pre.writes
    &&& post.neg_writes == pre.neg_writes
}


// ---- TSO ----

pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)

    &&& post.happy == pre.happy && pre.no_other_writers(core)
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.writes == pre.writes.insert((core, addr))
    &&& post.neg_writes ==
        if pre.pt_mem.page_addrs().contains_key(addr)
            && !(pre.pt_mem.page_addrs()[addr] is Empty)
        { pre.neg_writes.map_values(|ws:Set<_>| ws.insert(addr)) }
        else { pre.neg_writes }
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.read_from_mem_tso(core, addr, value)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.writes == pre.writes
    &&& post.neg_writes == pre.neg_writes
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& c.valid_core(core)

    &&& post.happy == pre.happy
    &&& post.pt_mem@ == pre.pt_mem@
    &&& post.writes === pre.writes.filter(|e:(Core, usize)| e.0 != core)
    &&& post.neg_writes == pre.neg_writes
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& State::stutter(pre, post)
}

pub enum Step {
    Invlpg,
    // TODO: maybe just make path part of the label
    Walk { path: Seq<(usize, PageDirectoryEntry)> },
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
