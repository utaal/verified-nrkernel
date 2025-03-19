use vstd::prelude::*;
use vstd::assert_by_contradiction;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    aligned, bit, WORD_SIZE, MAX_PHYADDR_WIDTH, axiom_max_phyaddr_width_facts, MemOp,
    LoadResult, update_range };
use crate::spec_t::mmu::defs::{ Core, PTE };
use crate::spec_t::mmu::rl3::{ Writes };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 2 of the MMU. Compared to layer 3, it expresses translation
// caching and non-atomic walks as a single concept, and replaces the explicit havoc-ing of
// dirty/accessed bits with underspecified reads.

pub struct State {
    pub happy: bool,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    pub writes: Writes,
    pub polarity: Polarity,
    pub hist: History,
}

pub struct History {
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
}

pub enum Step {
    Invlpg,
    // Faulting memory op due to failed translation
    MemOpNoTr { walk: Walk },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk },
    TLBFill { core: Core, walk: Walk },
    TLBEvict { core: Core, tlb_va: usize },
    // TSO
    WriteNonneg,
    WriteNonpos,
    Writeback { core: Core },
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}


impl State {
    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize) -> usize {
        self.core_mem(core).read(addr)
    }

    #[verifier(inline)]
    pub open spec fn writer_sbuf(self) -> Seq<(usize, usize)> {
        self.sbuf[self.writes.core]
    }

    /// The memory as seen by the given core. I.e. taking into consideration the core's store
    /// buffers.
    pub open spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    /// The view of the memory from the writer core's perspective.
    #[verifier(inline)]
    pub open spec fn writer_mem(self) -> PTMem {
        self.core_mem(self.writes.core)
    }

    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize, pol: Polarity) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& if pol is Mapping {
                self.writer_mem().is_nonneg_write(addr, value)
            } else {
                self.writer_mem().is_nonpos_write(addr, value)
            }
    }

    pub open spec fn can_flip_polarity(self) -> bool {
        &&& self.happy
        &&& self.hist.pending_maps === map![]
        &&& self.hist.pending_unmaps === map![]
        &&& self.writes.tso === set![]
    }

    pub open spec fn pending_unmap_for(self, va: usize) -> bool {
        exists|vb| {
        &&& #[trigger] self.hist.pending_unmaps.contains_key(vb)
        &&& vb <= va < vb + self.hist.pending_unmaps[vb].frame.size
        }
    }

    pub open spec fn pending_map_for(self, va: usize) -> bool {
        exists|vb| {
        &&& #[trigger] self.hist.pending_maps.contains_key(vb)
        &&& vb <= va < vb + self.hist.pending_maps[vb].frame.size
        }
    }

    //pub open spec fn can_change_polarity(self, c: Constants) -> bool {
    //    &&& self.writes.tso.is_empty()
    //    &&& forall|core| #![auto] c.valid_core(core) ==> self.writes.neg[core].is_empty()
    //}
}



// State machine transitions

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)
    &&& pre.happy

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        walks: pre.walks.insert(core, set![]),
        writes: Writes {
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            //neg: pre.writes.neg.insert(core, set![]),
            core: pre.writes.core,
        },
        hist: if core == pre.writes.core { History { pending_maps: map![], ..pre.hist } } else { pre.hist },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& {
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& !memop.crosses_qword_boundary(memop_vaddr as nat)
    &&& pre.walks[core].contains(walk)
    &&& walk.vaddr == memop_vaddr
    &&& walk_next.complete
    &&& walk_next.result() is Invalid
    &&& memop.is_pagefault()
    }

    &&& post == pre
}

pub open spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& !memop.crosses_qword_boundary(memop_vaddr as nat)
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& {
    let pte = pre.tlbs[core][tlb_va];
    let paddr = pte.frame.base + (memop_vaddr - tlb_va);
    &&& tlb_va <= memop_vaddr < tlb_va + pte.frame.size
    &&& match memop {
        MemOp::Store { new_value, result } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                &&& result is Ok
                &&& post.phys_mem === update_range(pre.phys_mem, paddr, new_value)
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
        MemOp::Load { is_exec, result, .. } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                &&& result == LoadResult::Value(pre.phys_mem.subrange(paddr, paddr + memop.op_size()))
                &&& post.phys_mem === pre.phys_mem
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
    }
    }

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist == pre.hist
}


// ---- Non-atomic page table walks ----

pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(vaddr as nat, 8)
    //&&& arbitrary() // TODO: conditions on va? max vaddr?

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

// This thing has to be opaque because the iterated if makes Z3 explode, especially but not only
// with how we use this function in `iter_walk`.
#[verifier(opaque)]
pub open spec fn walk_next(mem: PTMem, walk: Walk) -> Walk {
    let Walk { vaddr, path, .. } = walk;
    let addr = if path.len() == 0 {
        add(mem.pml4, mul(l0_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
    } else { arbitrary() };

    let entry = PDE { entry: mem.read(addr), layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory),
    };
    walk
}

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk_next))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.complete
    &&& walk_next.result() matches WalkResult::Valid { vbase, pte }

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vbase, pte)),
        ..pre
    }
}

pub open spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.tlbs[core].contains_key(tlb_va)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].remove(tlb_va)),
        ..pre
    }
}



// ---- TSO ----

/// Write to core's local store buffer.
pub open spec fn step_WriteNonneg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value, Polarity::Mapping)
    &&& pre.polarity is Mapping || pre.can_flip_polarity()

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.tso === pre.writes.tso.insert(addr)
    //&&& post.writes.neg == if !pre.writer_mem().is_nonneg_write(addr, value) {
    //        pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
    //    } else { pre.writes.neg }
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Mapping
    &&& post.hist.pending_maps == pre.hist.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.writer_mem()@.contains_key(vbase) && !pre.writer_mem()@.contains_key(vbase),
            |vbase| post.writer_mem()@[vbase]
        ))
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.writer_mem()@.contains_key(vbase) && !post.writer_mem()@.contains_key(vbase),
            |vbase| pre.writer_mem()@[vbase]
        ))
}

/// Write to core's local store buffer.
pub open spec fn step_WriteNonpos(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value, Polarity::Unmapping)
    &&& pre.polarity is Unmapping || pre.can_flip_polarity()

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.tso === pre.writes.tso.insert(addr)
    //&&& post.writes.neg == if !pre.writer_mem().is_nonneg_write(addr, value) {
    //        pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
    //    } else { pre.writes.neg }
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Unmapping
    &&& post.hist.pending_maps == pre.hist.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.writer_mem()@.contains_key(vbase) && !pre.writer_mem()@.contains_key(vbase),
            |vbase| post.writer_mem()@[vbase]
        ))
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.writer_mem()@.contains_key(vbase) && !post.writer_mem()@.contains_key(vbase),
            |vbase| pre.writer_mem()@[vbase]
        ))
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
    //&&& post.polarity == pre.polarity
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& value & MASK_NEG_DIRTY_ACCESS == pre.read_from_mem_tso(core, addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        writes: Writes {
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            ..pre.writes
        },
        hist: if core == pre.writes.core { History { pending_maps: map![], ..pre.hist } } else { pre.hist },
        ..pre
    }
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& {
    let polarity = if value & 1 == 1 { Polarity::Mapping } else { Polarity::Unmapping };
    &&& !pre.is_this_write_happy(core, addr, value, polarity)
    &&& !post.happy
    }
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                    => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr { walk }        => step_MemOpNoTr(pre, post, c, walk, lbl),
        Step::MemOpTLB { tlb_va }       => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::WalkInit { core, vaddr }  => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk }   => step_WalkStep(pre, post, c, core, walk, lbl),
        Step::TLBFill { core, walk }    => step_TLBFill(pre, post, c, core, walk, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::WriteNonneg               => step_WriteNonneg(pre, post, c, lbl),
        Step::WriteNonpos               => step_WriteNonpos(pre, post, c, lbl),
        Step::Writeback { core }        => step_Writeback(pre, post, c, core, lbl),
        Step::Read                      => step_Read(pre, post, c, lbl),
        Step::Barrier                   => step_Barrier(pre, post, c, lbl),
        Step::SadWrite                  => step_SadWrite(pre, post, c, lbl),
        Step::Sadness                   => step_Sadness(pre, post, c, lbl),
        Step::Stutter                   => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    //&&& pre.pt_mem == ..
    &&& pre.tlbs  === Map::new(|core| c.valid_core(core), |core| Map::empty())
    &&& pre.walks === Map::new(|core| c.valid_core(core), |core| set![])
    &&& pre.sbuf  === Map::new(|core| c.valid_core(core), |core| seq![])
    &&& pre.happy == true
    //&&& pre.writes.core == ..
    &&& pre.writes.tso === set![]
    &&& pre.hist.pending_maps === map![]
    &&& pre.hist.pending_unmaps === map![]
    &&& pre.polarity === Polarity::Mapping

    &&& c.valid_core(pre.writes.core)
    &&& forall|va| aligned(va as nat, 8) ==> #[trigger] pre.pt_mem.mem.contains_key(va)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& pre.pt_mem.pml4 <= u64::MAX - 4096
}






// Invariants for this state machine

impl State {
    pub open spec fn wf(self, c: Constants) -> bool {
        &&& c.valid_core(self.writes.core)
        &&& self.writes.tso.finite()
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        //&&& forall|core| #[trigger] c.valid_core(core) <==> self.writes.neg.contains_key(core)
        &&& forall|core| #[trigger] self.walks.contains_key(core) ==> self.walks[core].finite()
        //&&& forall|core| #[trigger] self.writes.neg.contains_key(core) ==> self.writes.neg[core].finite()
        &&& forall|va| aligned(va as nat, 8) ==> #[trigger] self.pt_mem.mem.contains_key(va)
        &&& aligned(self.pt_mem.pml4 as nat, 4096)
        &&& self.pt_mem.pml4 <= u64::MAX - 4096
    }

    pub open spec fn non_writer_sbufs_are_empty(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) && core != self.writes.core
            ==> self.sbuf[core] === seq![]
    }

    pub open spec fn writer_sbuf_entries_are_unique(self) -> bool {
        forall|i1, i2| #![auto]
               0 <= i1 < self.writer_sbuf().len()
            && 0 <= i2 < self.writer_sbuf().len()
            && i1 != i2
                ==> self.writer_sbuf()[i2].0 != self.writer_sbuf()[i1].0
    }

    pub open spec fn writer_sbuf_entries_have_P_bit_1(self) -> bool {
        forall|i| #![auto] 0 <= i < self.writer_sbuf().len() ==> self.writer_sbuf()[i].1 & 1 == 1
    }

    pub open spec fn writer_sbuf_entries_have_P_bit_0(self) -> bool {
        forall|i| #![auto] 0 <= i < self.writer_sbuf().len() ==> self.writer_sbuf()[i].1 & 1 == 0
    }

    pub open spec fn writer_sbuf_subset_all_writes(self) -> bool {
        forall|a| self.writer_sbuf().contains_fst(a) ==> #[trigger] self.writes.tso.contains(a)
        //self.writer_sbuf().to_set().map(|x:(_,_)| x.0).subset_of(self.writes.tso)
    }

    pub open spec fn inv_sbuf_facts(self, c: Constants) -> bool {
        &&& self.non_writer_sbufs_are_empty(c)
        &&& self.writer_sbuf_entries_are_unique()
        &&& self.writer_sbuf_subset_all_writes()
    }

    pub open spec fn inv_unmapping__inflight_walks(self, c: Constants) -> bool {
        forall|core, walk| c.valid_core(core) && #[trigger] self.walks[core].contains(walk) ==> {
            let walk_na = finish_iter_walk(self.core_mem(core), walk);
            let walk_a  = self.core_mem(core).pt_walk(walk.vaddr);
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            // TODO:
            // Needs decision:
            // Either enforce that unmapping happens bottom-to-top or need to modify this:
            // - If we unmap a directory that still has children, we could have inflight walks
            //   "caching" that part of the path. I.e. they may still complete successfully, so we
            //   have staleness due to non-atomicity/translation caching, not just TSO.
            // - Enforcing bottom-to-top might be tricky and add complexity to impl VCs
            //
            // Enforcing bottom-to-top:
            // - Have to be able to differentiate removal of a page mapping vs directory mapping
            // - When we explicitly do separate memory ranges I could use the address to
            //   distinguish whether we're unmapping a page mapping or a directory mapping
            // - But this may not work generally with huge page mappings?
            // - Doing this in a context-free way is very hard or impossible?
            //
            // Without bottom-to-top:
            // - We can now have in-flight walks that will complete successfully but don't satisfy
            //   is_iter_walk_prefix
            // - Specifically: If we remove a non-empty directory, walks using that directory may
            //   be in-progress and eventually complete successfully
            &&& (if walk_a.result() is Invalid {
                     walk_na.result() matches WalkResult::Valid { vbase, pte }
                         ==> self.hist.pending_unmaps.contains_pair(vbase, pte)
                 } else {
                     is_iter_walk_prefix(self.core_mem(core), walk)
                 })
        }
    }

    // (write mem read = core mem read) || write mem read has P=0 and core mem read has P=1



    //pub open spec fn inv_unmapping__pending_unmap_is_invalid(self, c: Constants) -> bool {
    //    forall|va| #![auto] self.hist.pending_unmaps.contains_key(va) ==> self.writer_mem().pt_walk(va).result() is Invalid
    //}

    //pub open spec fn inv_unmapping__valid_pending_unmap(self, c: Constants) -> bool {
    //    forall|core, va| #![trigger self.core_mem(core).pt_walk(va).result()] {
    //        let vbase = self.core_mem(core).pt_walk(va).result()->Valid_vbase;
    //        let pte = self.core_mem(core).pt_walk(va).result()->Valid_pte;
    //           self.core_mem(core).pt_walk(va).result() is Valid
    //        && c.valid_core(core)
    //        && self.hist.pending_unmaps.contains_key(vbase)
    //        ==> self.hist.pending_unmaps[vbase] == pte
    //    }
    //}

    pub open spec fn inv_unmapping__valid_walk(self, c: Constants) -> bool {
        forall|va, core| #![auto] c.valid_core(core) && self.core_mem(core).pt_walk(va).result() is Valid ==> {
            let core_walk = self.core_mem(core).pt_walk(va);
            let vbase = core_walk.result()->Valid_vbase;
            let pte = core_walk.result()->Valid_pte;
            let writer_walk = self.writer_mem().pt_walk(va);
            if self.hist.pending_unmaps.contains_key(vbase) {
                pte == self.hist.pending_unmaps[vbase]
            } else {
                core_walk == writer_walk
            }
        }
    }

    pub open spec fn inv_unmapping__invalid_walk(self, c: Constants) -> bool {
        forall|va, core| #![auto]
            c.valid_core(core) && self.core_mem(core).pt_walk(va).result() is Invalid
                ==> self.writer_mem().pt_walk(va).result() is Invalid
    }

    //pub open spec fn inv_unmapping__mismatched_walks(self, c: Constants) -> bool {
    //    forall|va, core| c.valid_core(core) && self.writer_mem().pt_walk(va) != #[trigger] self.core_mem(core).pt_walk(va)
    //        ==> {
    //            let writer_walk = self.writer_mem().pt_walk(va);
    //            let core_walk = self.core_mem(core).pt_walk(va);
    //            &&& writer_walk.result() is Invalid
    //            &&& core_walk.result() matches WalkResult::Valid { pte, vbase }
    //                    ==> self.hist.pending_unmaps.contains_pair(vbase, pte)
    //        }
    //}

    pub open spec fn inv_mapping__inflight_walks(self, c: Constants) -> bool {
        forall|core, walk| c.valid_core(core) && #[trigger] self.walks[core].contains(walk) ==> {
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            &&& is_iter_walk_prefix(self.core_mem(core), walk)
        }
    }

    /// If any non-writer core reads a value that has the P bit set, we know that no write for that address is
    /// in the writer's store buffer.
    pub open spec fn inv_mapping__valid_is_not_in_sbuf(self, c: Constants) -> bool {
        forall|core, addr: usize|
            c.valid_core(core) && aligned(addr as nat, 8) &&
            core != self.writes.core &&
            #[trigger] self.core_mem(core).read(addr) & 1 == 1
                ==> !self.writer_sbuf().contains_fst(addr)
    }

    /// If a ptwalk is successful on the writer core and not tracked by `pending_maps`, then its
    /// locations are not in the store buffer.
    pub open spec fn inv_mapping__valid_not_pending_is_not_in_sbuf(self, c: Constants) -> bool {
        forall|va:usize,a|
            #![trigger self.writer_mem().pt_walk(va), self.writer_sbuf().contains_fst(a)]
        {
            let walk = self.writer_mem().pt_walk(va);
            walk.result() is Valid && !self.pending_map_for(va) && walk.path.contains_fst(a)
                ==> !self.writer_sbuf().contains_fst(a)
        }
    }

    pub open spec fn inv_mapping__pending_map_is_base_walk(self, c: Constants) -> bool {
        forall|va| #![auto] self.hist.pending_maps.contains_key(va) ==> self.writer_mem().is_base_pt_walk(va)
    }

    pub open spec fn inv_mapping(self, c: Constants) -> bool {
        &&& self.writer_sbuf_entries_have_P_bit_1()
        &&& self.inv_mapping__valid_is_not_in_sbuf(c)
        &&& self.inv_mapping__valid_not_pending_is_not_in_sbuf(c)
        &&& self.inv_mapping__inflight_walks(c)
        &&& self.inv_mapping__pending_map_is_base_walk(c)
        &&& self.hist.pending_unmaps === map![]
    }

    pub open spec fn inv_unmapping(self, c: Constants) -> bool {
        &&& self.writer_sbuf_entries_have_P_bit_0()
        &&& self.inv_unmapping__inflight_walks(c)
        //&&& self.inv_unmapping__pending_unmap_is_invalid(c)
        &&& self.inv_unmapping__valid_walk(c)
        //&&& self.inv_unmapping__mismatched_walks(c)
        &&& self.hist.pending_maps === map![]
    }

    /// Stuff that's true when we're not currently mapping or unmapping anything. (I.e. when we
    /// could flip the polarity.)
    pub open spec fn inv_between(self, c: Constants) -> bool {
        &&& self.inv_mapping__inflight_walks(c)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        &&& self.inv_sbuf_facts(c)
        &&& self.can_flip_polarity() ==> self.inv_between(c)
        &&& self.polarity is Mapping ==> self.inv_mapping(c)
        &&& self.polarity is Unmapping ==> self.inv_unmapping(c)
        }
    }
}


pub proof fn init_implies_inv(pre: State, c: Constants)
    requires init(pre, c)
    ensures pre.inv(c)
{}

pub proof fn next_preserves_inv(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.inv(c),
        next(pre, post, c, lbl),
    ensures post.inv(c)
{
    let step = choose|step| next_step(pre, post, c, step, lbl);
    next_step_preserves_inv(pre, post, c, step, lbl);
}

proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv(c)
{
    if pre.happy && post.happy {
        next_step_preserves_wf(pre, post, c, step, lbl);
        next_step_preserves_inv_sbuf_facts(pre, post, c, step, lbl);
        if post.polarity is Mapping {
            if pre.polarity is Unmapping { // Flipped polarity in this transition
                broadcast use lemma_writes_tso_empty_implies_sbuf_empty;
                assert(pre.inv_mapping__inflight_walks(c));
            }
            // TODO: Need an argument here that we only add things (pre is submap of post)
            // (already have this somewhere?)
            // Note: We could just sidestep this by making the writes constrained based on the
            // interp exactly the way we use it in the impl.
            assume(pre.writer_mem()@.submap_of(post.writer_mem()@));
            assert(post.hist.pending_unmaps =~= map![]);
            next_step_preserves_inv_mapping__inflight_walks(pre, post, c, step, lbl);
            next_step_preserves_inv_mapping__pending_map_is_base_walk(pre, post, c, step, lbl);
            next_step_preserves_inv_mapping__valid_not_pending_is_not_in_sbuf(pre, post, c, step, lbl);
            next_step_preserves_inv_mapping__valid_is_not_in_sbuf(pre, post, c, step, lbl);
        } else {
            next_step_preserves_inv_unmapping(pre, post, c, step, lbl);
        }
        if post.can_flip_polarity() {
            next_step_preserves_inv_between(pre, post, c, step, lbl);
        }
    }
}

proof fn next_step_preserves_inv_between(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        post.can_flip_polarity(),
        pre.happy,
        post.happy,
        pre.inv(c),
        post.wf(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_between(c)
{
    // TODO: I think to prove this from unmapping polarity, I'll also have to track which cores
    // have not yet executed an invlpg since the last write
    // (what i had the writes.neg for, but it could probably be less fine grained, just a flag per core)
    admit();
}

proof fn next_step_preserves_inv_unmapping(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.inv(c),
        post.wf(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_unmapping(c)
{
    assume(post.writer_mem()@.submap_of(pre.writer_mem()@));
    assert(post.hist.pending_maps =~= map![]);
    if pre.polarity is Mapping { // Flipped polarity in this transition
        broadcast use lemma_writes_tso_empty_implies_sbuf_empty;
        assert(pre.writer_sbuf_entries_have_P_bit_0());
    }
    assert(post.writer_sbuf_entries_have_P_bit_0());

    if pre.polarity is Mapping {
        // TODO: Have to prove this explicitly from inv_between
        assume(pre.inv_unmapping__inflight_walks(c));
    }
    assert(post.inv_unmapping__inflight_walks(c)) by {
        next_step_preserves_inv_unmapping__inflight_walks(pre, post, c, step, lbl);
    };
    assert(post.inv_unmapping__valid_walk(c)) by {
        next_step_preserves_inv_unmapping__valid_walk(pre, post, c, step, lbl);
    };
}

// unstable
proof fn next_step_preserves_inv_unmapping__valid_walk(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.inv_sbuf_facts(c),
        pre.inv_unmapping(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_unmapping__valid_walk(c)
{
    broadcast use
        group_ambient,
        lemma_step_core_mem;
    assert(pre.inv_unmapping__valid_walk(c));
    match step {
        Step::WalkStep { core, walk } => {
            reveal(rl2::walk_next);
            assert(post.inv_unmapping__valid_walk(c));
        },
        Step::WriteNonpos => {
            let (wrcore, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert forall|va, core| #![auto]
                c.valid_core(core) && post.core_mem(core).pt_walk(va).result() is Valid implies {
                    let core_walk = post.core_mem(core).pt_walk(va);
                    let vbase = core_walk.result()->Valid_vbase;
                    let pte = core_walk.result()->Valid_pte;
                    let writer_walk = post.writer_mem().pt_walk(va);
                    if post.hist.pending_unmaps.contains_key(vbase) {
                        post.hist.pending_unmaps[vbase] == pte
                    } else {
                        core_walk == writer_walk
                    }
                }
            by {
                lemma_pt_walk_result_vbase_equal(pre.writer_mem(), va);
                broadcast use lemma_unmapping__pt_walk_valid_in_post_unchanged;
                reveal(pt_mem::PTMem::view);
                //lemma_pt_walk_result_vbase_equal(post.writer_mem(), va);
                //lemma_mem_view_after_step_write(pre, post, c, lbl);

                let core_walk = post.core_mem(core).pt_walk(va);
                let writer_walk = post.writer_mem().pt_walk(va);
                let vbase = core_walk.result()->Valid_vbase;
                let pte = core_walk.result()->Valid_pte;
                if wrcore == core {
                    //lemma_unmapping__pt_walk_valid_in_post_unchanged(pre, post, c, step, lbl, va);
                    pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), va);
                    //if post.hist.pending_unmaps.contains_key(vbase) {
                    //    if pre.hist.pending_unmaps.contains_key(vbase) {
                    //        assume(pre.inv_unmapping__pending_unmap_is_invalid(c));
                    //        assert(pre.writer_mem().pt_walk(vbase).result() is Invalid);
                    //    } else {
                    //        reveal(pt_mem::PTMem::view);
                    //    }
                    //} else {
                    //    let writer_walk = post.writer_mem().pt_walk(va);
                    //    assert(core_walk == writer_walk);
                    //}
                } else {
                    //reveal(pt_mem::PTMem::view);
                    assert(core_walk == pre.core_mem(core).pt_walk(va));
                    //if post.hist.pending_unmaps.contains_key(vbase) {
                    //    if pre.hist.pending_unmaps.contains_key(vbase) {
                    //        assert(post.hist.pending_unmaps[vbase] == pre.hist.pending_unmaps[vbase]);
                    //    } else {
                    //    }
                    //} else {
                    //    assert(post.writer_mem().pt_walk(vbase).result() is Valid);
                    //    lemma_unmapping__pt_walk_valid_in_post_unchanged(pre, post, c, step, lbl, vbase);
                    //    assert(core_walk == writer_walk);
                    //}
                }
            };
            assert(post.inv_unmapping__valid_walk(c));
        },
        Step::Writeback { core } => {
            assert(bit!(0usize) == 1) by (bit_vector);
            lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
            assert(post.inv_unmapping__valid_walk(c));
        },
        _ => assert(post.inv_unmapping__valid_walk(c)),
    }
}

broadcast proof fn lemma_unmapping__pt_walk_valid_in_post_unchanged(pre: State, post: State, c: Constants, step: Step, lbl: Lbl, va: usize)
    requires
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        #[trigger] post.writer_mem().pt_walk(va).result() is Valid,
        #[trigger] next_step(pre, post, c, step, lbl),
    ensures
        post.writer_mem().pt_walk(va) == pre.writer_mem().pt_walk(va)
{
    broadcast use group_ambient;
    reveal(pt_mem::PTMem::view);
    match step {
        rl2::Step::WriteNonpos => {
            lemma_mem_view_after_step_write(pre, post, c, lbl);
        },
        rl2::Step::Writeback { core } => {
            lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
        },
        _ => {},
    }
    assert(bit!(0usize) == 1) by (bit_vector);
}

proof fn next_step_preserves_inv_unmapping__inflight_walks(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.inv_sbuf_facts(c),
        pre.inv_unmapping(c),
        post.inv_sbuf_facts(c),
        //pre.inv_mapping__valid_is_not_in_sbuf(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_unmapping__inflight_walks(c)
{
    broadcast use
        group_ambient,
        lemma_step_core_mem;
    match step {
        Step::WalkStep { core, walk } => {
            reveal(rl2::walk_next);
            assert(post.inv_unmapping__inflight_walks(c));
        },
        Step::WriteNonpos => {
            let (wrcore, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert forall|va| #![auto] pre.hist.pending_unmaps.contains_key(va)
                implies post.hist.pending_unmaps.contains_pair(va, pre.hist.pending_unmaps[va])
            by {
                assume(post.writer_mem()@.submap_of(pre.writer_mem()@));
                reveal(PTMem::view);
            };
            assert forall|core, walk|
                c.valid_core(core) && #[trigger] post.walks[core].contains(walk) implies {
                    let walk_na = finish_iter_walk(post.core_mem(core), walk);
                    let walk_a  = post.core_mem(core).pt_walk(walk.vaddr);
                    &&& aligned(walk.vaddr as nat, 8)
                    &&& walk.path.len() <= 3
                    &&& !walk.complete
                    &&& (if walk_a.result() is Invalid {
                             walk_na.result() matches WalkResult::Valid { vbase, pte }
                                 ==> post.hist.pending_unmaps.contains_pair(vbase, pte)
                         } else {
                             is_iter_walk_prefix(post.core_mem(core), walk)
                         })
            } by {
                let pre_walk_na = finish_iter_walk(pre.core_mem(core), walk);
                let pre_walk_a  = pre.core_mem(core).pt_walk(walk.vaddr);
                let post_walk_na = finish_iter_walk(post.core_mem(core), walk);
                let post_walk_a  = post.core_mem(core).pt_walk(walk.vaddr);
                //lemma_iter_walk_equals_pt_walk(pre.core_mem(core), walk.vaddr);
                //lemma_iter_walk_equals_pt_walk(post.core_mem(core), walk.vaddr);
                if wrcore == core {
                    assert(pre.walks[core].contains(walk));
                    lemma_mem_view_after_step_write(pre, post, c, lbl);
                    pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                    assert(post.core_mem(core) == post.writer_mem());
                    assert(pre.core_mem(core) == pre.writer_mem()) by {
                        if post.writes.core == pre.writes.core {
                        } else {
                            assert(pre.sbuf[pre.writes.core] =~= seq![]);
                        }
                    };

                    if pre_walk_a.result() is Invalid {
                        reveal(rl2::walk_next);
                        // TODO: easy
                        assume(post_walk_a.result() is Invalid);
                        if pre_walk_na.result() is Valid {
                            if exists|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr {
                                // The write was to a location that the completion of the
                                // non-atomic walk depends on. We'll reason about the first such
                                // location on the path.
                                //
                                // A location appearing on the path more than once would mean
                                // there's a cycle. This usually shouldn't happen but it's hard to
                                // state that as an assumption (and then prove it in the impl).
                                let i = choose|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr
                                            && (forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                                assert(pre_walk_na.path[i].0 == wraddr);
                                assert(forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                                // TODO: fairly easy?
                                assume(post_walk_na.result() is Invalid);
                            } else {
                            }
                        } else {
                            // TODO: easy: A walk cannot become more valid after a nonpositive write
                            assume(post_walk_na.result() is Invalid);
                        }
                    } else {
                        assert(pre_walk_a == pre_walk_na) by {
                            assert(is_iter_walk_prefix(pre.core_mem(core), walk));
                            broadcast use
                                lemma_finish_iter_walk_prefix_matches_iter_walk,
                                lemma_iter_walk_equals_pt_walk;
                        };
                        if exists|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr {
                            // The write was to a location that the completion of the non-atomic
                            // walk depends on.
                            reveal(rl2::walk_next);
                            // TODO: easy
                            assume(post_walk_a.result() is Invalid);
                            // We reason about the least i where the address matches the write
                            // address.
                            let i = choose|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr
                                        && (forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                            assert(pre_walk_na.path[i].0 == wraddr);
                            assert(forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                            // TODO: fairly easy?
                            assume(post_walk_na.result() is Invalid);
                        } else {
                            // The write didn't modify the locations the non-atomic walk will still
                            // visit, so the walk after completion is unchanged.
                            // TODO: easy
                            assume(post_walk_na == pre_walk_na);
                            if exists|i| #![auto] 0 <= i < walk.path.len() && walk.path[i].0 == wraddr {
                                // The write was to a location that was used in the prefix
                                // `walk.path` that we already computed so far. I.e. the atomic
                                // walk becomes invalid due to this write.
                                assume(post_walk_a.result() is Invalid);
                                let vbase = pre_walk_a.result()->Valid_vbase;
                                let pte = pre_walk_a.result()->Valid_pte;
                                reveal(PTMem::view);
                                lemma_pt_walk_result_vbase_equal(pre.core_mem(core), walk.vaddr);
                                //lemma_pt_walk_result_vbase_equal(post.core_mem(core), walk.vaddr);
                                //lemma_iter_walk_equals_pt_walk(pre.core_mem(core), vbase);
                                //lemma_iter_walk_equals_pt_walk(post.core_mem(core), vbase);
                                assert(pre.writer_mem().is_base_pt_walk(vbase));
                                assert(pre.writer_mem()@.contains_key(vbase));
                                assert(post.writer_mem().pt_walk(walk.vaddr).result() is Invalid);
                                // TODO: This might be non-trivial. Check what I did with map.
                                // The issue is that lemma_pt_walk_result_vbase_equal doesn't work
                                // on the post state because the walk is now invalid so we don't
                                // have the base address. It's still true because we're using the
                                // same bits to index on vbase and walk.vaddr, so it will follow
                                // the same path.
                                assume(post.writer_mem().pt_walk(vbase).result() is Invalid);
                                assert(!post.writer_mem()@.contains_key(vbase));
                                assert(post.hist.pending_unmaps.contains_pair(vbase, pte));
                                //assume(forall|i| 0 <= i < walk.path.len() ==> walk.path[i] == pre_walk_na.path[i]);
                            } else {
                                reveal(rl2::walk_next);
                                // TODO: easy
                                assume(post_walk_a == pre_walk_a);
                            }
                        }
                    }
                }
            };
            assert(post.inv_unmapping__inflight_walks(c));
        },
        Step::Writeback { core: wrcore } => {
            let wraddr = pre.writer_sbuf()[0].0;
            let value = pre.writer_sbuf()[0].1;
            assert(wrcore == pre.writes.core);
            assert(wrcore == post.writes.core);
            assert forall|core, walk|
                c.valid_core(core) && #[trigger] post.walks[core].contains(walk) implies {
                    let walk_na = finish_iter_walk(post.core_mem(core), walk);
                    let walk_a  = post.core_mem(core).pt_walk(walk.vaddr);
                    &&& aligned(walk.vaddr as nat, 8)
                    &&& walk.path.len() <= 3
                    &&& !walk.complete
                    &&& (if walk_a.result() is Invalid {
                             walk_na.result() matches WalkResult::Valid { vbase, pte }
                                 ==> post.hist.pending_unmaps.contains_pair(vbase, pte)
                         } else {
                             is_iter_walk_prefix(post.core_mem(core), walk)
                         })
            } by {
                admit();
                //let pre_walk_na = finish_iter_walk(pre.core_mem(core), walk);
                //let pre_walk_a  = pre.core_mem(core).pt_walk(walk.vaddr);
                //let post_walk_na = finish_iter_walk(post.core_mem(core), walk);
                //let post_walk_a  = post.core_mem(core).pt_walk(walk.vaddr);
                ////lemma_iter_walk_equals_pt_walk(pre.core_mem(core), walk.vaddr);
                ////lemma_iter_walk_equals_pt_walk(post.core_mem(core), walk.vaddr);
                //if wrcore == core {
                //    lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
                //} else {
                //    //pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
                //    //post.pt_mem.lemma_write_seq(post.writer_sbuf());
                //    //assert(bit!(0usize) == 1) by (bit_vector);
                //    //assert(pre.core_mem(core) == pre.pt_mem);
                //    //assert(post.core_mem(core) == post.pt_mem);
                //    //assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> aligned(walk.path[i].0 as nat, 8)) by {
                //    //    broadcast use PDE::lemma_view_addr_aligned;
                //    //    crate::spec_t::mmu::translation::lemma_bit_indices_less_512(walk.vaddr);
                //    //};
                //    assert(pre.walks[core].contains(walk));
                //    lemma_mem_view_after_step_write(pre, post, c, lbl);
                //    pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                //    assert(post.core_mem(core) == post.writer_mem());
                //    assert(pre.core_mem(core) == pre.writer_mem()) by {
                //        if post.writes.core == pre.writes.core {
                //        } else {
                //            assert(pre.sbuf[pre.writes.core] =~= seq![]);
                //        }
                //    };
                //
                //    if pre_walk_a.result() is Invalid {
                //        reveal(rl2::walk_next);
                //        // TODO: easy
                //        assume(post_walk_a.result() is Invalid);
                //        if pre_walk_na.result() is Valid {
                //            if exists|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr {
                //                // The write was to a location that the completion of the
                //                // non-atomic walk depends on. We'll reason about the first such
                //                // location on the path.
                //                //
                //                // A location appearing on the path more than once would mean
                //                // there's a cycle. This usually shouldn't happen but it's hard to
                //                // state that as an assumption (and then prove it in the impl).
                //                let i = choose|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr
                //                            && (forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                //                assert(pre_walk_na.path[i].0 == wraddr);
                //                assert(forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                //                // TODO: fairly easy?
                //                assume(post_walk_na.result() is Invalid);
                //            } else {
                //            }
                //        } else {
                //            // TODO: easy: A walk cannot become more valid after a nonpositive write
                //            assume(post_walk_na.result() is Invalid);
                //        }
                //    } else {
                //        assert(pre_walk_a == pre_walk_na) by {
                //            assert(is_iter_walk_prefix(pre.core_mem(core), walk));
                //            broadcast use
                //                lemma_finish_iter_walk_prefix_matches_iter_walk,
                //                lemma_iter_walk_equals_pt_walk;
                //        };
                //        if exists|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr {
                //            // The write was to a location that the completion of the non-atomic
                //            // walk depends on.
                //            reveal(rl2::walk_next);
                //            // TODO: easy
                //            assume(post_walk_a.result() is Invalid);
                //            // We reason about the least i where the address matches the write
                //            // address.
                //            let i = choose|i| #![auto] walk.path.len() <= i < pre_walk_na.path.len() && pre_walk_na.path[i].0 == wraddr
                //                        && (forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                //            assert(pre_walk_na.path[i].0 == wraddr);
                //            assert(forall|j| #![auto] walk.path.len() <= j < i ==> pre_walk_na.path[j].0 != wraddr);
                //            // TODO: fairly easy?
                //            assume(post_walk_na.result() is Invalid);
                //        } else {
                //            // The write didn't modify the locations the non-atomic walk will still
                //            // visit, so the walk after completion is unchanged.
                //            // TODO: easy
                //            assume(post_walk_na == pre_walk_na);
                //            if exists|i| #![auto] 0 <= i < walk.path.len() && walk.path[i].0 == wraddr {
                //                // The write was to a location that was used in the prefix
                //                // `walk.path` that we already computed so far. I.e. the atomic
                //                // walk becomes invalid due to this write.
                //                assume(post_walk_a.result() is Invalid);
                //                let vbase = pre_walk_a.result()->Valid_vbase;
                //                let pte = pre_walk_a.result()->Valid_pte;
                //                reveal(PTMem::view);
                //                lemma_pt_walk_result_vbase_equal(pre.core_mem(core), walk.vaddr);
                //                //lemma_pt_walk_result_vbase_equal(post.core_mem(core), walk.vaddr);
                //                //lemma_iter_walk_equals_pt_walk(pre.core_mem(core), vbase);
                //                //lemma_iter_walk_equals_pt_walk(post.core_mem(core), vbase);
                //                assert(pre.writer_mem().is_base_pt_walk(vbase));
                //                assert(pre.writer_mem()@.contains_key(vbase));
                //                assert(post.writer_mem().pt_walk(walk.vaddr).result() is Invalid);
                //                // TODO: This might be non-trivial. Check what I did with map.
                //                // The issue is that lemma_pt_walk_result_vbase_equal doesn't work
                //                // on the post state because the walk is now invalid so we don't
                //                // have the base address. It's still true because we're using the
                //                // same bits to index on vbase and walk.vaddr, so it will follow
                //                // the same path.
                //                assume(post.writer_mem().pt_walk(vbase).result() is Invalid);
                //                assert(!post.writer_mem()@.contains_key(vbase));
                //                assert(post.hist.pending_unmaps.contains_pair(vbase, pte));
                //                //assume(forall|i| 0 <= i < walk.path.len() ==> walk.path[i] == pre_walk_na.path[i]);
                //            } else {
                //                reveal(rl2::walk_next);
                //                // TODO: easy
                //                assume(post_walk_a == pre_walk_a);
                //            }
                //        }
                //    }
                //}
            };
            assert(post.inv_unmapping__inflight_walks(c));
        },
        Step::WalkInit { core, vaddr } => {
            broadcast use
                lemma_finish_iter_walk_prefix_matches_iter_walk,
                lemma_iter_walk_equals_pt_walk;
            assert(post.inv_unmapping__inflight_walks(c));
        },
        _ => {
            assert(post.inv_unmapping__inflight_walks(c));
        },
    }
}

broadcast proof fn lemma_finish_iter_walk_prefix_matches_iter_walk(pre: State, core: Core, walk: Walk)
    requires
        is_iter_walk_prefix(pre.core_mem(core), walk),
    ensures
        #[trigger] finish_iter_walk(pre.core_mem(core), walk) == iter_walk(pre.core_mem(core), walk.vaddr),
{
    reveal(walk_next);
}

proof fn next_step_preserves_inv_unmapping__invalid_walk(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.inv_sbuf_facts(c),
        pre.inv_unmapping(c),
        post.inv_sbuf_facts(c),
        pre.inv_unmapping__invalid_walk(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_unmapping__invalid_walk(c)
{
    broadcast use
        group_ambient,
        lemma_step_core_mem;
    match step {
        Step::WriteNonpos => {
            let (wrcore, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert(bit!(0usize) == 1) by (bit_vector);
            assert forall|va, core| #![auto]
                    c.valid_core(core) && post.core_mem(core).pt_walk(va).result() is Invalid
                implies
                    post.writer_mem().pt_walk(va).result() is Invalid
            by {
                if wrcore != core {
                    assert(post.core_mem(core).pt_walk(va) == pre.core_mem(core).pt_walk(va));
                    // TODO: This should be fairly easy. Lhs of implication stays the same and it
                    // can only make the rhs true not false.
                    admit();
                }
            };
            assert(post.inv_unmapping__invalid_walk(c));
        },
        Step::Writeback { core: wrcore } => {
            let wraddr = pre.writer_sbuf()[0].0;
            let value = pre.writer_sbuf()[0].1;
            assert(wrcore == pre.writes.core);
            assert(wrcore == post.writes.core);
            assert(bit!(0usize) == 1) by (bit_vector);
            lemma_writeback_preserves_writer_mem(pre, post, c, wrcore, lbl);
            assert forall|va, core| #![auto]
                    c.valid_core(core) && post.core_mem(core).pt_walk(va).result() is Invalid
                implies
                    post.writer_mem().pt_walk(va).result() is Invalid
            by {
                if wrcore != core {
                    assert(post.writer_mem().pt_walk(va) == pre.writer_mem().pt_walk(va));
                    // TODO: This one is trickier because we may invalidate a walk in core_mem and
                    // have to prove that the walk is already invalid in writer_mem.
                    //
                    // Can I somehow use inv_unmapping__inflight_walks? Obvious issue is I'd need
                    // to transfer that statement from inflight walks to completed walks. (I.e. a
                    // very similar but separate invariant that could probably be proved the same
                    // way.)
                    admit();
                }
            };
            assert(post.inv_unmapping__invalid_walk(c));
        },
        _ => assert(post.inv_unmapping__invalid_walk(c)),
    }
}

proof fn next_step_preserves_wf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        post.happy,
        next_step(pre, post, c, step, lbl),
    ensures post.wf(c)
{}

// unstable?
proof fn next_step_preserves_inv_mapping__inflight_walks(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.wf(c),
        pre.happy,
        post.happy,
        post.polarity is Mapping,
        pre.inv_sbuf_facts(c),
        post.inv_sbuf_facts(c),
        pre.inv_mapping__valid_is_not_in_sbuf(c),
        pre.inv_mapping__inflight_walks(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_mapping__inflight_walks(c)
{
    broadcast use
        group_ambient,
        lemma_step_core_mem;
    match step {
        Step::WalkStep { core, walk } => {
            reveal(rl2::walk_next);
            assert(post.inv_mapping__inflight_walks(c));
        },
        Step::WriteNonneg => {
            let (wrcore, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert(post.inv_mapping__inflight_walks(c)) by {
                assert forall|core, walk|
                    c.valid_core(core) && #[trigger] post.walks[core].contains(walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        // TODO: can probably extract some of these things into a lemma that
                        // collects facts about step_Write. Using very similar assertions in
                        // other proofs.
                        reveal(rl2::walk_next);
                        lemma_mem_view_after_step_write(pre, post, c, lbl);
                        pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                        assert(post.core_mem(core) == post.writer_mem());
                        if post.writes.core == pre.writes.core {
                        } else {
                            assert(pre.core_mem(core) == pre.writer_mem());
                        }
                    }
                };
            };
        },
        Step::Writeback { core: wrcore } => {
            let wraddr = pre.writer_sbuf()[0].0;
            let value = pre.writer_sbuf()[0].1;
            assert(wrcore == pre.writes.core);
            assert(wrcore == post.writes.core);
            assert(post.inv_mapping__inflight_walks(c)) by {
                assert forall|core, walk|
                    c.valid_core(core) && #[trigger] post.walks[core].contains(walk)
                implies is_iter_walk_prefix(post.core_mem(core), walk) by {
                    if wrcore == core {
                        lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
                    } else {
                        // TODO: Kind of unstable and really ugly proof
                        let pre_walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
                        let pre_walkp1 = walk_next(pre.core_mem(core), pre_walkp0);
                        let pre_walkp2 = walk_next(pre.core_mem(core), pre_walkp1);
                        let pre_walkp3 = walk_next(pre.core_mem(core), pre_walkp2);
                        let pre_walkp4 = walk_next(pre.core_mem(core), pre_walkp3);
                        let post_walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
                        let post_walkp1 = walk_next(post.core_mem(core), post_walkp0);
                        let post_walkp2 = walk_next(post.core_mem(core), post_walkp1);
                        let post_walkp3 = walk_next(post.core_mem(core), post_walkp2);
                        let post_walkp4 = walk_next(post.core_mem(core), post_walkp3);
                        reveal(rl2::walk_next);
                        //lemma_mem_view_after_step_write(pre, post, c, lbl);
                        //pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), walk.vaddr);
                        pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
                        post.pt_mem.lemma_write_seq(post.writer_sbuf());
                        assert(bit!(0usize) == 1) by (bit_vector);
                        assert(pre.core_mem(core) == pre.pt_mem);
                        assert(post.core_mem(core) == post.pt_mem);
                        // TODO: extract to lemma, also used in lemma_valid_not_pending_implies_equal
                        assert(forall|i| #![auto] 0 <= i < walk.path.len() ==> aligned(walk.path[i].0 as nat, 8)) by {
                            broadcast use PDE::lemma_view_addr_aligned;
                            crate::spec_t::mmu::translation::lemma_bit_indices_less_512(walk.vaddr);
                        };
                        if walk.path.len() == 0 {
                            assert(walk == pre_walkp0);
                        } else if walk.path.len() == 1 {
                            assert(walk == pre_walkp1);

                            assert(post_walkp1.path[0] == pre_walkp1.path[0]);
                        } else if walk.path.len() == 2 {
                            assert(walk == pre_walkp2);
                            assert(!pre_walkp1.complete);

                            assert(post_walkp2.path.len() == pre_walkp2.path.len());
                            assert(post_walkp2.path[0] == pre_walkp2.path[0]);
                            assert(post_walkp2.path[1] == pre_walkp2.path[1]);
                        } else if walk.path.len() == 3 {
                            assert(walk == pre_walkp3);
                            assert(!pre_walkp1.complete);
                            assert(!pre_walkp2.complete);

                            assert(post_walkp3.path.len() == pre_walkp3.path.len());
                            assert(post_walkp3.path[0] == pre_walkp3.path[0]);
                            assert(post_walkp3.path[1] == pre_walkp3.path[1]);
                            //assert(post_walkp3.path[2] == pre_walkp3.path[2]);
                        } else {
                            assert(false);
                        }
                    }
                };
            };
        },
        _ => assert(post.inv_mapping__inflight_walks(c)),
    }
}


proof fn next_step_preserves_inv_sbuf_facts(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_sbuf_facts(c)
{
    if post.happy {
        match step {
            Step::WriteNonneg => {
                let core = lbl->Write_0;
                if core == pre.writes.core {
                    assert(post.writer_sbuf_entries_are_unique()) by {
                        broadcast use
                            lemma_writes_tso_empty_implies_sbuf_empty,
                            lemma_writer_read_from_sbuf;
                    };
                } else {
                    assert_by_contradiction!(pre.writer_sbuf() =~= seq![], {
                        assert(pre.writes.tso.contains(pre.writer_sbuf()[0].0));
                    });
                    assert(post.non_writer_sbufs_are_empty(c));
                }
                assert(post.inv_sbuf_facts(c));
            },
            Step::WriteNonpos => {
                let core = lbl->Write_0;
                if core == pre.writes.core {
                    assert(post.writer_sbuf_entries_are_unique()) by {
                        broadcast use
                            lemma_writes_tso_empty_implies_sbuf_empty,
                            lemma_writer_read_from_sbuf;
                    };
                } else {
                    assert_by_contradiction!(pre.writer_sbuf() =~= seq![], {
                        assert(pre.writes.tso.contains(pre.writer_sbuf()[0].0));
                    });
                    assert(post.non_writer_sbufs_are_empty(c));
                }
                assert(post.inv_sbuf_facts(c));
            },
            _ => assert(post.inv_sbuf_facts(c)),
        }
    }
}

broadcast proof fn lemma_writer_read_from_sbuf(state: State, c: Constants, i: int)
    requires
        state.wf(c),
        #[trigger] state.inv_sbuf_facts(c),
        0 <= i < state.writer_sbuf().len(),
    ensures
        state.writer_mem().read(state.writer_sbuf()[i].0) == (#[trigger] state.writer_sbuf()[i]).1
{
    state.pt_mem.lemma_write_seq_read(state.writer_sbuf(), i);
}

broadcast proof fn lemma_core_mem_pml4(state: State, c: Constants, core: Core)
    requires
        #[trigger] c.valid_core(core),
    ensures
        (#[trigger] state.core_mem(core)).pml4 == state.pt_mem.pml4,
{
    state.pt_mem.lemma_write_seq(state.sbuf[core])
}

proof fn next_step_preserves_inv_mapping__pending_map_is_base_walk(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        post.polarity is Mapping,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        pre.inv_mapping__pending_map_is_base_walk(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_mapping__pending_map_is_base_walk(c)
{
    reveal(PTMem::view);
    match step {
        Step::WriteNonneg => {
            broadcast use lemma_step_writenonneg_valid_walk_unchanged;
            assert(post.inv_mapping__pending_map_is_base_walk(c));
        },
        Step::Writeback { core } => {
            lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
            assert(post.inv_mapping__pending_map_is_base_walk(c));
        },
        _ => assert(post.inv_mapping__pending_map_is_base_walk(c)),
    }
}

broadcast proof fn lemma_step_core_mem(pre: State, post: State, c: Constants, step: Step, lbl: Lbl, core: Core)
    requires
        pre.happy,
        post.happy,
        #[trigger] next_step(pre, post, c, step, lbl),
        !(step is WriteNonneg),
        !(step is WriteNonpos),
        !(step is Writeback),
    ensures
        #[trigger] post.core_mem(core) == pre.core_mem(core)
{}

proof fn lemma_mem_view_after_step_write(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        step_WriteNonneg(pre, post, c, lbl) || step_WriteNonpos(pre, post, c, lbl),
    ensures
        post.writer_mem().pml4 == pre.pt_mem.pml4,
        post.writer_mem().mem  == pre.writer_mem().mem.insert(lbl->Write_1, lbl->Write_2),
{
    let (core, wraddr, value) =
        if let Lbl::Write(core, addr, value) = lbl {
            (core, addr, value)
        } else { arbitrary() };
    reveal_with_fuel(vstd::seq::Seq::fold_left, 5);
    if post.writes.core == pre.writes.core {
        pre.pt_mem.lemma_write_seq_push(pre.writer_sbuf(), wraddr, value);
    } else {
        assert_by_contradiction!(pre.writer_sbuf() =~= seq![], {
            assert(pre.writes.tso.contains(pre.writer_sbuf()[0].0));
        });
    }
}

broadcast proof fn lemma_step_writenonneg_valid_walk_unchanged(pre: State, post: State, c: Constants, lbl: Lbl, va: usize)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        #[trigger] step_WriteNonneg(pre, post, c, lbl),
        pre.writer_mem().pt_walk(va).result() is Valid,
    ensures
        #[trigger] post.writer_mem().pt_walk(va) == pre.writer_mem().pt_walk(va)
{
    let (core, wraddr, value) =
        if let Lbl::Write(core, addr, value) = lbl {
            (core, addr, value)
        } else { arbitrary() };
    assert(bit!(0usize) == 1) by (bit_vector);
    pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
    post.pt_mem.lemma_write_seq(post.writer_sbuf());
    lemma_mem_view_after_step_write(pre, post, c, lbl);
}

proof fn lemma_step_writenonneg_path_addrs_match(pre: State, post: State, c: Constants, lbl: Lbl, va: usize)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        step_WriteNonneg(pre, post, c, lbl),
    ensures
        forall|i| #![auto]
            0 <= i < pre.writer_mem().pt_walk(va).path.len()
                ==> post.writer_mem().pt_walk(va).path[i].0
                  == pre.writer_mem().pt_walk(va).path[i].0
{
    lemma_mem_view_after_step_write(pre, post, c, lbl);
    pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), va);
    pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
    post.pt_mem.lemma_write_seq(post.writer_sbuf());
}

proof fn lemma_step_writenonneg_new_walk_has_pending_map(pre: State, post: State, c: Constants, lbl: Lbl, va: usize)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        step_WriteNonneg(pre, post, c, lbl),
        pre.writer_mem().pt_walk(va).result() is Invalid,
        post.writer_mem().pt_walk(va).result() is Valid,
    ensures
        post.pending_map_for(va)
{
    reveal(PTMem::view);
    let pre_mem = pre.writer_mem();
    let post_mem = post.writer_mem();
    assert(pre_mem.pt_walk(va).result() is Invalid);
    assert(post_mem.pt_walk(va).result() is Valid);
    let vbase = post_mem.pt_walk(va).result()->vbase;

    lemma_pt_walk_result_vbase_equal(post_mem, va);
    assert(post_mem.pt_walk(vbase).result() is Valid);
    assert(post_mem.is_base_pt_walk(vbase));
    assert(post.writer_mem()@.contains_key(vbase));

    assert(!pre_mem.is_base_pt_walk(vbase)) by {
        assert(pre_mem.pt_walk(vbase).path == pre_mem.pt_walk(va).path) by {
            lemma_step_writenonneg_path_addrs_match(pre, post, c, lbl, va);
            lemma_step_writenonneg_path_addrs_match(pre, post, c, lbl, vbase);
        };
        assert(pre_mem.pt_walk(vbase).result() is Valid ==> pre_mem.pt_walk(va).result() is Valid);
        lemma_pt_walk_result_vbase_equal(pre_mem, vbase);
        assert(pre_mem.pt_walk(vbase).result() is Invalid);
    };
    assert(!pre.writer_mem()@.contains_key(vbase));

    assert(post.hist.pending_maps.contains_key(vbase));
    assert(vbase <= va < vbase + post.hist.pending_maps[vbase].frame.size);
}

proof fn next_step_preserves_inv_mapping__valid_not_pending_is_not_in_sbuf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        post.polarity is Mapping,
        pre.wf(c),
        pre.inv_mapping__valid_not_pending_is_not_in_sbuf(c),
        pre.inv_sbuf_facts(c),
        pre.inv_mapping__pending_map_is_base_walk(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_mapping__valid_not_pending_is_not_in_sbuf(c)
{
    reveal(PTMem::view);
    match step {
        Step::Invlpg => {
            let core = lbl->Invlpg_0;
            assert(core != pre.writes.core ==> post.hist.pending_maps === pre.hist.pending_maps);
            assert(post.inv_mapping__valid_not_pending_is_not_in_sbuf(c));
        },
        Step::WriteNonneg => {
            let (core, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert forall|va:usize,addr|
                    post.writer_mem().pt_walk(va).result() is Valid
                    && !post.pending_map_for(va)
                    && post.writer_mem().pt_walk(va).path.contains_fst(addr)
                implies !post.writer_sbuf().contains_fst(addr)
            by {
                let pre_walk  = pre.writer_mem().pt_walk(va);
                let post_walk = post.writer_mem().pt_walk(va);
                assert(pre.hist.pending_maps.dom().subset_of(post.hist.pending_maps.dom()));
                assert(pre.hist.pending_maps.submap_of(post.hist.pending_maps));
                assert_by_contradiction!(!pre.pending_map_for(va), {
                    let vb = choose|vb| {
                                &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
                                &&& vb <= va < vb + pre.hist.pending_maps[vb].frame.size
                                };
                    assert(post.hist.pending_maps.contains_key(vb));
                    assert(vb <= va < vb + post.hist.pending_maps[vb].frame.size);
                    assert(post.pending_map_for(va));
                });
                // If the walk had only become valid during this transition, it would have been
                // added to pending_maps. So it must have been valid already.
                assert_by_contradiction!(pre_walk.result() is Valid, {
                    assert(pre_walk.result() is Invalid);
                    assert(post_walk.result() is Valid);
                    lemma_step_writenonneg_new_walk_has_pending_map(pre, post, c, lbl, va);
                });
                // And if the walk was valid, its path hasn't changed.
                assert(post.writer_mem().pt_walk(va).path == pre_walk.path) by {
                    lemma_step_writenonneg_valid_walk_unchanged(pre, post, c, lbl, va);
                };
                assert(pre.writer_mem().read(addr) & 1 == 1) by {
                    pt_mem::PTMem::lemma_pt_walk(pre.writer_mem(), va);
                };
                assert(!pre.writer_sbuf().contains_fst(addr));
                assert(addr != wraddr);
            };
            assert(post.inv_mapping__valid_not_pending_is_not_in_sbuf(c));
        },
        Step::WriteNonpos => {},
        Step::Writeback { core } => {
            lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
            assert(forall|a| post.writer_sbuf().contains_fst(a)
                    ==> pre.writer_sbuf().contains_fst(a));
            assert(post.inv_mapping__valid_not_pending_is_not_in_sbuf(c));
        },
        _ => assert(post.inv_mapping__valid_not_pending_is_not_in_sbuf(c)),
    }
}

proof fn next_step_preserves_inv_mapping__valid_is_not_in_sbuf(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_mapping__valid_is_not_in_sbuf(c),
        pre.inv_sbuf_facts(c),
        post.inv_sbuf_facts(c),
        next_step(pre, post, c, step, lbl),
        post.polarity is Mapping,
    ensures post.inv_mapping__valid_is_not_in_sbuf(c)
{
    broadcast use lemma_step_core_mem;
    match step {
        Step::WriteNonneg => {
            let (core, wraddr, value) =
                if let Lbl::Write(core, addr, value) = lbl {
                    (core, addr, value)
                } else { arbitrary() };
            assert(post.writes.core == core);
            assert forall|core2, addr: usize| c.valid_core(core2) && aligned(addr as nat, 8)
                    && core2 != core
                    && #[trigger] post.core_mem(core2).read(addr) & 1 == 1
                implies !post.sbuf[core].contains_fst(addr)
            by {
                assert(core != core2);
                assert(forall|b:u64| b & 1 == 0 || b & 1 == 1) by (bit_vector);
                assert(pre.writer_mem().read(wraddr) & 1 == 0);
                if core == pre.writes.core {
                    if addr == wraddr {
                        assert_by_contradiction!(!pre.sbuf[core].contains_fst(addr), {
                            let i = choose|i| 0 <= i < pre.sbuf[core].len() && #[trigger] pre.sbuf[core][i] == (addr, pre.sbuf[core][i].1);
                            let (addr2, value2) = pre.sbuf[core][i];
                            assert(post.sbuf[core][i] == (addr2, value2));
                            let j = pre.sbuf[core].len() as int;
                            assert(post.sbuf[core][pre.sbuf[core].len() as int] == (addr, value));
                        });
                        assert(pre.writer_mem().read(wraddr) & 1 != 1);

                        assert(false) by {
                            assert(pre.core_mem(core2) == pre.pt_mem);
                            assert(pre.pt_mem.read(addr) & 1 == 1);
                            assert(pre.writer_mem().read(addr) & 1 != 1);
                            assert(!pre.sbuf[core].contains_fst(addr));
                            broadcast use pt_mem::PTMem::lemma_write_seq_idle;
                            assert(pre.writer_mem().read(addr) == pre.pt_mem.read(addr));
                        };
                    } else {
                        assert(pre.core_mem(core2).read(addr) & 1 == 1);
                        assert(!post.sbuf[core].contains_fst(addr));
                    }
                } else {
                    assert(post.writer_sbuf_entries_are_unique());
                    assert(!post.sbuf[core].contains_fst(addr));
                }
            };
            assert(post.inv_mapping__valid_is_not_in_sbuf(c));
        },
        Step::WriteNonpos => {},
        Step::Writeback { core } => {
            let (wraddr, value) = pre.sbuf[core][0];
            assert(core == post.writes.core);
            assert(post.writes.core == pre.writes.core);
            assert forall|core2, addr: usize| c.valid_core(core2) && aligned(addr as nat, 8)
                    && core2 != post.writes.core
                    && #[trigger] post.core_mem(core2).read(addr) & 1 == 1
                implies !post.writer_sbuf().contains_fst(addr)
            by {
                assert(core2 != core);
                if addr == wraddr {
                    assert(post.writer_sbuf_entries_are_unique());
                    assert(pre.sbuf[core].contains_fst(addr));
                    assert(pre.sbuf[core][0] == (addr, value));
                    assert(!post.sbuf[core].contains_fst(addr));
                } else { // addr != wraddr
                    assert(pre.sbuf[core2] === seq![]);
                    assert(post.sbuf[core2] === seq![]);
                    assert(post.pt_mem.read(addr) == pre.pt_mem.read(addr));
                    assert(pre.core_mem(core2).read(addr) & 1 == 1);
                }
                assert(!post.writer_sbuf().contains_fst(addr));
            };
            assert(post.inv_mapping__valid_is_not_in_sbuf(c));
        },
        Step::SadWrite => assert(false),
        Step::Sadness => assert(false),
        _ => assert(post.inv_mapping__valid_is_not_in_sbuf(c)),
    }
}

broadcast proof fn lemma_valid_implies_equal_reads(state: State, c: Constants, core: Core, addr: usize)
    requires
        state.inv_sbuf_facts(c),
        state.inv_mapping__valid_is_not_in_sbuf(c),
        c.valid_core(core),
        core != state.writes.core,
        aligned(addr as nat, 8),
        state.core_mem(core).read(addr) & 1 == 1,
        state.core_mem(core).mem.contains_key(addr),
    ensures #![auto] state.core_mem(core).read(addr) == state.writer_mem().read(addr)
{
    state.pt_mem.lemma_write_seq_idle(state.writer_sbuf(), addr);
    assert(state.core_mem(core).read(addr) == state.pt_mem.read(addr));
    assert(state.writer_mem().read(addr) == state.pt_mem.read(addr));
}

proof fn lemma_valid_implies_equal_walks(state: State, c: Constants, core: Core, va: usize)
    requires
        state.wf(c),
        state.inv_sbuf_facts(c),
        state.inv_mapping__valid_is_not_in_sbuf(c),
        c.valid_core(core),
        core != state.writes.core,
    ensures ({
        let core_walk = state.core_mem(core).pt_walk(va);
        let writer_walk = state.writer_mem().pt_walk(va);
        core_walk.result() is Valid ==> core_walk == writer_walk
    })
{
    state.pt_mem.lemma_write_seq(state.writer_sbuf());
    assert(bit!(0usize) == 1) by (bit_vector);
    axiom_max_phyaddr_width_facts();
    let mw = MAX_PHYADDR_WIDTH;
    assert(forall|v: usize| (v & bitmask_inc!(12usize, sub(mw, 1))) % 4096 == 0) by (bit_vector)
        requires 32 <= mw <= 52;
    crate::spec_t::mmu::translation::lemma_bit_indices_less_512(va);
    broadcast use lemma_valid_implies_equal_reads;
}

// unstable
proof fn lemma_valid_not_pending_implies_equal(state: State, c: Constants, core: Core, va: usize)
    requires
        state.wf(c),
        state.inv_sbuf_facts(c),
        state.inv_mapping__valid_not_pending_is_not_in_sbuf(c),
        state.writer_mem().pt_walk(va).result() is Valid,
        !state.pending_map_for(va),
        c.valid_core(core),
    ensures
        state.core_mem(core).pt_walk(va) == state.writer_mem().pt_walk(va)
{
    state.pt_mem.lemma_write_seq(state.writer_sbuf());
    let path = state.writer_mem().pt_walk(va).path;
    assert(forall|i| #![auto] 0 <= i < path.len() ==> aligned(path[i].0 as nat, 8)) by {
        broadcast use PDE::lemma_view_addr_aligned;
        crate::spec_t::mmu::translation::lemma_bit_indices_less_512(va);
    };
    assert(forall|i,a,v:GPDE| #![auto] 0 <= i < path.len() && path[i] == (a, v)
        ==> !state.writer_sbuf().contains_fst(a));
    assert forall|i,a,v:GPDE| #![auto] 0 <= i < path.len() && path[i] == (a, v)
        implies state.writer_mem().read(a) == state.core_mem(core).read(a)
    by { broadcast use pt_mem::PTMem::lemma_write_seq_idle; };
}



proof fn lemma_writeback_preserves_writer_mem(pre: State, post: State, c: Constants, core: Core, lbl: Lbl)
    requires
        pre.inv_sbuf_facts(c),
        step_Writeback(pre, post, c, core, lbl),
    ensures post.writer_mem() == pre.writer_mem()
{
    assert(post.writes.core == core);
    pt_mem::PTMem::lemma_write_seq_first(pre.pt_mem, pre.sbuf[core]);
}

broadcast proof fn lemma_writes_tso_empty_implies_sbuf_empty(pre: State, c: Constants, core: Core)
    requires
        pre.inv_sbuf_facts(c),
        pre.writes.tso === set![],
        #[trigger] c.valid_core(core),
    ensures
        #[trigger] pre.sbuf[core] === seq![]
{
    if core == pre.writes.core {
        assert forall|a| pre.sbuf[core].contains(a) implies false by {
            assert(pre.writes.tso.contains(a.0));
        };
        assert_by_contradiction!(pre.sbuf[core] =~= seq![], {
            assert(pre.sbuf[core].contains(pre.sbuf[core][0]));
        });
    }
}


pub open spec fn is_invalid_walk_and_atomic_is_invalid(mem: PTMem, walk: Walk) -> bool {
    let walk_na = finish_iter_walk(mem, walk);
    let walk_a  = iter_walk(mem, walk.vaddr);
    &&& walk_na.result() is Invalid
    &&& walk_a.result() is Invalid
}

// MB: Ideally this would be some one liner `walk.path.is_prefix_of(..)`. But that doesn't seem to work well.
pub open spec fn is_iter_walk_prefix(mem: PTMem, walk: Walk) -> bool {
    let walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
    let walkp1 = walk_next(mem, walkp0);
    let walkp2 = walk_next(mem, walkp1);
    let walkp3 = walk_next(mem, walkp2);
    let walkp4 = walk_next(mem, walkp3);
    if walk.path.len() == 0 {
        walk == walkp0
    } else if walk.path.len() == 1 {
        walk == walkp1
    } else if walk.path.len() == 2 {
        &&& walk == walkp2
        &&& !walkp1.complete
    } else if walk.path.len() == 3 {
        &&& walk == walkp3
        &&& !walkp1.complete
        &&& !walkp2.complete
    } else if walk.path.len() == 4 {
        &&& walk == walkp4
        &&& !walkp1.complete
        &&& !walkp2.complete
        &&& !walkp3.complete
    } else {
        false
    }
}

pub open spec fn finish_iter_walk(mem: PTMem, walk: Walk) -> Walk {
    if walk.complete { walk } else {
        let walk = rl2::walk_next(mem, walk);
        if walk.complete { walk } else {
            let walk = rl2::walk_next(mem, walk);
            if walk.complete { walk } else {
                let walk = rl2::walk_next(mem, walk);
                if walk.complete { walk } else {
                    rl2::walk_next(mem, walk)
                }
            }
        }
    }
}

pub open spec fn iter_walk(mem: PTMem, vaddr: usize) -> Walk {
    let walk = rl2::walk_next(mem, Walk { vaddr, path: seq![], complete: false });
    if walk.complete { walk } else {
        let walk = rl2::walk_next(mem, walk);
        if walk.complete { walk } else {
            let walk = rl2::walk_next(mem, walk);
            if walk.complete { walk } else {
                rl2::walk_next(mem, walk)
            }
        }
    }
}

broadcast proof fn lemma_iter_walk_equals_pt_walk(mem: PTMem, vaddr: usize)
    ensures #[trigger] iter_walk(mem, vaddr) == mem.pt_walk(vaddr)
{
    reveal(walk_next);
    let walk = Walk { vaddr, path: seq![], complete: false };
    let walk = rl2::walk_next(mem, walk);
    let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
    let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
    let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
    let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
    let l0_addr = add(mem.pml4, l0_idx);
    let l0e = PDE { entry: mem.read(l0_addr), layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let walk = rl2::walk_next(mem, walk);
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: mem.read(l1_addr), layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let walk = rl2::walk_next(mem, walk);
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: mem.read(l2_addr), layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let walk = rl2::walk_next(mem, walk);
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: mem.read(l3_addr), layer: Ghost(3) };
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
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).path == iter_walk(mem, vaddr).path,
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).result().vaddr() == iter_walk(mem, vaddr).result().vaddr(),
{
    lemma_iter_walk_result_vbase_equal_aux1(mem, vaddr);
    lemma_iter_walk_result_vbase_equal_aux2(mem, vaddr);
}

proof fn lemma_iter_walk_result_vbase_equal_aux1(mem: PTMem, vaddr: usize)
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).path == iter_walk(mem, vaddr).path,
{
    reveal(rl2::walk_next);
    broadcast use lemma_bits_align_to_usize;
}

// unstable
proof fn lemma_iter_walk_result_vbase_equal_aux2(mem: PTMem, vaddr: usize)
    ensures
        iter_walk(mem, iter_walk(mem, vaddr).result().vaddr()).result().vaddr() == iter_walk(mem, vaddr).result().vaddr(),
{
    reveal(rl2::walk_next);
    broadcast use lemma_bits_align_to_usize;
}

proof fn lemma_pt_walk_result_vbase_equal(mem: PTMem, vaddr: usize)
    ensures
        mem.pt_walk(mem.pt_walk(vaddr).result().vaddr()).path     == mem.pt_walk(vaddr).path,
        mem.pt_walk(mem.pt_walk(vaddr).result().vaddr()).result() == mem.pt_walk(vaddr).result(),
        //mem.pt_walk(mem.pt_walk(vaddr).result().vaddr()).result().vaddr() == vaddr,
{
    broadcast use lemma_iter_walk_equals_pt_walk;
    lemma_iter_walk_result_vbase_equal(mem, mem.pt_walk(vaddr).result().vaddr());
    lemma_iter_walk_result_vbase_equal(mem, vaddr);
}

broadcast proof fn lemma_bits_align_to_usize(vaddr: usize)
    ensures
        #![trigger align_to_usize(vaddr, L1_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L2_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, L3_ENTRY_SIZE)]
        #![trigger align_to_usize(vaddr, 8)]
        l0_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L1_ENTRY_SIZE)) == l1_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, L2_ENTRY_SIZE)) == l2_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l2_bits!(vaddr),
        l3_bits!(align_to_usize(vaddr, L3_ENTRY_SIZE)) == l3_bits!(vaddr),
        l0_bits!(align_to_usize(vaddr, 8)) == l0_bits!(vaddr),
        l1_bits!(align_to_usize(vaddr, 8)) == l1_bits!(vaddr),
        l2_bits!(align_to_usize(vaddr, 8)) == l2_bits!(vaddr),
        l3_bits!(align_to_usize(vaddr, 8)) == l3_bits!(vaddr),
{
    let l1_es = L1_ENTRY_SIZE;
    let l2_es = L2_ENTRY_SIZE;
    let l3_es = L3_ENTRY_SIZE;
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

broadcast group group_ambient {
    lemma_core_mem_pml4
}

pub mod refinement {
    use crate::spec_t::mmu::*;
    use crate::spec_t::mmu::rl1;
    use crate::spec_t::mmu::rl2;
    //use crate::definitions_t::{ WORD_SIZE };

    impl rl2::State {
        pub open spec fn interp(self) -> rl1::State {
            rl1::State {
                happy: self.happy,
                pt_mem: self.writer_mem(),
                phys_mem: self.phys_mem,
                tlbs: self.tlbs,
                writes: self.writes,
                pending_maps: self.hist.pending_maps,
                pending_unmaps: self.hist.pending_unmaps,
                polarity: self.polarity,
            }
        }
    }

    impl rl2::Step {
        pub open spec fn interp(self, pre: rl2::State, lbl: Lbl) -> rl1::Step {
            match self {
                rl2::Step::Invlpg => rl1::Step::Invlpg,
                rl2::Step::WalkInit { core, vaddr } => rl1::Step::Stutter,
                rl2::Step::WalkStep { core, walk } => rl1::Step::Stutter,
                rl2::Step::MemOpNoTr { walk } => {
                    let (core, memop_vaddr, memop) =
                        if let Lbl::MemOp(core, vaddr, memop) = lbl {
                            (core, vaddr, memop)
                        } else { arbitrary() };
                    let walk_na_res = rl2::walk_next(pre.core_mem(core), walk).result();
                    if pre.pending_map_for(memop_vaddr) {
                        let vb = choose|vb| {
                            &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
                            &&& vb <= memop_vaddr < vb + pre.hist.pending_maps[vb].frame.size
                        };
                        rl1::Step::MemOpNoTrNA { vbase: vb }
                    } else {
                        rl1::Step::MemOpNoTr
                    }
                },
                rl2::Step::MemOpTLB { tlb_va } => rl1::Step::MemOpTLB { tlb_va },
                rl2::Step::TLBFill { core, walk } => {
                    let walk_na_res = rl2::walk_next(pre.core_mem(core), walk).result();
                    let vaddr = walk_na_res->Valid_vbase;
                    //let pte = walk_na_res->Valid_pte;
                    if pre.hist.pending_unmaps.contains_key(vaddr) {
                        rl1::Step::TLBFillNA { core, vaddr }
                    } else {
                        rl1::Step::TLBFill { core, vaddr }
                    }
                },
                rl2::Step::TLBEvict { core, tlb_va } => rl1::Step::TLBEvict { core, tlb_va },
                rl2::Step::WriteNonneg => rl1::Step::WriteNonneg,
                rl2::Step::WriteNonpos => rl1::Step::WriteNonpos,
                rl2::Step::Writeback { core } => rl1::Step::Stutter,
                rl2::Step::Read => rl1::Step::Read,
                rl2::Step::Barrier => rl1::Step::Barrier,
                rl2::Step::SadWrite => rl1::Step::SadWrite,
                rl2::Step::Sadness => rl1::Step::Sadness,
                rl2::Step::Stutter => rl1::Step::Stutter,
            }
        }
    }

    proof fn next_step_refines(pre: rl2::State, post: rl2::State, c: rl2::Constants, step: rl2::Step, lbl: Lbl)
        requires
            pre.inv(c),
            rl2::next_step(pre, post, c, step, lbl),
        ensures rl1::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        match step {
            rl2::Step::Invlpg => {
                assert(rl1::step_Invlpg(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::MemOpNoTr { walk } => {
                next_step_MemOpNoTr_refines(pre, post, c, step, lbl);
                assert(rl1::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl));
            },
            rl2::Step::MemOpTLB { tlb_va } => {
                assert(rl1::step_MemOpTLB(pre.interp(), post.interp(), c, tlb_va, lbl));
            },
            rl2::Step::WalkInit { core, vaddr } => {
                assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::WalkStep { core, walk } => {
                assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::TLBFill { core, walk } => {
                let walk_na = rl2::walk_next(pre.core_mem(core), walk);
                let walk_a  = pre.writer_mem().pt_walk(walk.vaddr);
                let walk_na_res = walk_na.result();
                //assert(walk_na_res is Valid);
                let vbase = walk_na_res->Valid_vbase;
                let pte = walk_na_res->Valid_pte;
                rl2::lemma_iter_walk_equals_pt_walk(pre.core_mem(core), walk.vaddr);
                rl2::lemma_iter_walk_equals_pt_walk(pre.writer_mem(), walk.vaddr);
                //rl2::lemma_iter_walk_equals_pt_walk(pre.core_mem(core), vbase);
                //rl2::lemma_iter_walk_equals_pt_walk(pre.writer_mem(), vbase);
                rl2::lemma_pt_walk_result_vbase_equal(pre.writer_mem(), walk.vaddr);

                if pre.polarity is Mapping {
                    if core != pre.writes.core {
                        rl2::lemma_valid_implies_equal_walks(pre, c, core, walk.vaddr);
                    }
                    assert(rl1::step_TLBFill(pre.interp(), post.interp(), c, core, vbase, lbl));
                } else {
                    if pre.hist.pending_unmaps.contains_key(vbase) {
                        //assert(pte == pre.interp().pending_unmaps[vbase]);
                        //assert(pre.hist.pending_unmaps.contains_pair(vbase, pte));
                        //assert(rl2::is_iter_walk_prefix(pre.core_mem(core), walk));
                        //assert(pte == walk_na_res->Valid_pte);
                        assert(rl1::step_TLBFillNA(pre.interp(), post.interp(), c, core, vbase, lbl));
                    } else {
                        //assert(pre.writer_mem().pt_walk(vbase).result() == WalkResult::Valid { vbase, pte });
                        assert(rl1::step_TLBFill(pre.interp(), post.interp(), c, core, vbase, lbl));
                    }
                }
            },
            rl2::Step::TLBEvict { core, tlb_va } => {
                assert(rl1::step_TLBEvict(pre.interp(), post.interp(), c, core, tlb_va, lbl));
            },
            rl2::Step::WriteNonneg => {
                let (core, addr, value) =
                    if let Lbl::Write(core, addr, value) = lbl {
                        (core, addr, value)
                    } else { arbitrary() };
                rl2::lemma_mem_view_after_step_write(pre, post, c, lbl);
                pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
                // TODO: because it's a nonnegative write
                assume(post.hist.pending_unmaps == pre.hist.pending_unmaps);
                assert(rl1::step_WriteNonneg(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::WriteNonpos => {
                let (core, addr, value) =
                    if let Lbl::Write(core, addr, value) = lbl {
                        (core, addr, value)
                    } else { arbitrary() };
                rl2::lemma_mem_view_after_step_write(pre, post, c, lbl);
                pre.pt_mem.lemma_write_seq(pre.writer_sbuf());
                // TODO: because it's a nonpositive write
                assume(post.hist.pending_maps == pre.hist.pending_maps);
                assert(rl1::step_WriteNonpos(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::Writeback { core } => {
                super::lemma_writeback_preserves_writer_mem(pre, post, c, core, lbl);
                assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::Read => {
                let (core, addr, value) =
                    if let Lbl::Read(core, addr, value) = lbl {
                        (core, addr, value)
                    } else { arbitrary() };
                if pre.interp().is_tso_read_deterministic(core, addr) {
                    if !pre.writes.tso.contains(addr) {
                        assert(forall|i| #![auto] 0 <= i < pre.writer_sbuf().len() ==> pre.writer_sbuf()[i].0 != addr);
                        broadcast use pt_mem::PTMem::lemma_write_seq_idle;
                    }
                    assert(pre.read_from_mem_tso(core, addr) == pre.writer_mem().read(addr));
                }
                assert(rl1::step_Read(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::Barrier => {
                assert(rl1::step_Barrier(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::SadWrite => {
                assert(rl1::step_SadWrite(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::Sadness => {
                assert(rl1::step_Sadness(pre.interp(), post.interp(), c, lbl));
            },
            rl2::Step::Stutter => {
                assert(rl1::step_Stutter(pre.interp(), post.interp(), c, lbl));
            },
        }
    }

    proof fn next_step_MemOpNoTr_refines(pre: rl2::State, post: rl2::State, c: rl2::Constants, step: rl2::Step, lbl: Lbl)
        requires
            step is MemOpNoTr,
            pre.happy,
            pre.inv(c),
            rl2::next_step(pre, post, c, step, lbl),
        ensures rl1::next_step(pre.interp(), post.interp(), c, step.interp(pre, lbl), lbl)
    {
        let walk = step->MemOpNoTr_walk;
        let (core, memop_vaddr, memop) = if let Lbl::MemOp(core, vaddr, memop) = lbl {
                (core, vaddr, memop)
            } else { arbitrary() };
        let core_mem = pre.core_mem(core);
        let writer_mem = pre.writer_mem();
        let walk_na = rl2::walk_next(pre.core_mem(core), walk);

        rl2::lemma_iter_walk_equals_pt_walk(core_mem, walk.vaddr);
        rl2::lemma_iter_walk_equals_pt_walk(writer_mem, walk.vaddr);

        if pre.polarity is Mapping {
            assert(forall|i| 0 <= i < walk.path.len() ==> walk_na.path[i] == walk.path[i]) by {
                reveal(rl2::walk_next);
            };
            assert(walk_na.result() is Invalid);

            // STEP 1: This walk has the same result if done on the same core but atomically.
            let walk_a_same_core = rl2::iter_walk(core_mem, walk.vaddr);
            assert(walk_a_same_core == walk_na);

            // STEP 2: The atomic walk on this core is the same as an atomic walk on the writer's view
            // of the memory. (Or if not, it's in a region in `pre.pending_maps`.)
            let walk_a_writer_core = rl2::iter_walk(writer_mem, walk.vaddr);

            assert(walk_a_writer_core == writer_mem.pt_walk(walk.vaddr));

            if pre.pending_map_for(walk.vaddr) {
                let vb = choose|vb| {
                    &&& #[trigger] pre.hist.pending_maps.contains_key(vb)
                    &&& vb <= walk.vaddr < vb + pre.hist.pending_maps[vb].frame.size
                };
                pre.interp().pending_maps.contains_key(vb);
                assert(rl1::step_MemOpNoTrNA(pre.interp(), post.interp(), c, vb, lbl));
            } else {
                if core == pre.writes.core {
                    // If the walk happens on the writer core, the two atomic walks are done on the same
                    // memory, i.e. are trivially equal.
                    assert(walk_a_writer_core == walk_a_same_core);
                    assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
                } else {
                    rl2::lemma_valid_implies_equal_walks(pre, c, core, walk.vaddr);
                    assert forall|va| writer_mem.pt_walk(va).result() is Valid && !pre.pending_map_for(va)
                        implies #[trigger] core_mem.pt_walk(va).result() == writer_mem.pt_walk(va).result()
                    by { rl2::lemma_valid_not_pending_implies_equal(pre, c, core, va); };
                    assert(walk_a_same_core.result() == walk_a_writer_core.result());
                    assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
                }
            }
        } else {
            //assert(walk_na.result() is Invalid);
            //let walk_a_same_core = rl2::iter_walk(core_mem, walk.vaddr);
            //assert(rl2::is_iter_walk_prefix(pre.core_mem(core), walk) || walk_a_same_core.result() is Invalid);
            // TODO: Reconsider how I formulate this invariant exactly.
            assume(pre.inv_unmapping__invalid_walk(c));
            //if walk_a_same_core.result() is Invalid {
            //    assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
            //} else {
            //    assert(rl1::step_MemOpNoTr(pre.interp(), post.interp(), c, lbl));
            //}
            // TODO: something similar to inv_mapping__inflight_walks
            // When unmapping, the atomic walk is a prefix of the inflight walk but both must be
            // invalid.
            // No case distinction on pending_maps or pending_unmaps needed. This transition always
            // appears atomic. (With strong enough conditions, i.e. start at bottom and unmap
            // empty directories one by one.
        }
    }

    pub proof fn init_refines(pre: rl2::State, c: rl2::Constants)
        requires rl2::init(pre, c),
        ensures rl1::init(pre.interp(), c),
    {}

    pub proof fn next_refines(pre: rl2::State, post: rl2::State, c: rl2::Constants, lbl: Lbl)
        requires
            pre.inv(c),
            rl2::next(pre, post, c, lbl),
        ensures
            rl1::next(pre.interp(), post.interp(), c, lbl),
    {
        let step = choose|step: rl2::Step| rl2::next_step(pre, post, c, step, lbl);
        next_step_refines(pre, post, c, step, lbl);
    }
}


} // verus!
