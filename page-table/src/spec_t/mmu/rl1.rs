use vstd::prelude::*;
use crate::spec_t::mmu::*;
use crate::spec_t::mmu::pt_mem::*;
use crate::spec_t::mem::word_index_spec;
use crate::spec_t::mmu::defs::{ aligned, Core, LoadResult };
use crate::spec_t::mmu::rl3::{ Writes };
use crate::spec_t::mmu::translation::{ MASK_NEG_DIRTY_ACCESS };

verus! {

// This file contains refinement layer 1 of the MMU. Compared to layer 2, it removes store buffers
// and defines an atomic semantics to page table walks. This is the most abstract version of the
// MMU model.

pub struct State {
    pub happy: bool,
    /// Word-indexed physical (non-page-table) memory
    pub phys_mem: Seq<nat>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    pub writes: Writes,
    /// Tracks the virtual address ranges for which we cannot guarantee atomic walk results
    /// If polarity is negative, we give no guarantees about the results in these ranges; If it's
    /// positive, the possible results are atomic semantics or an "invalid" result.
    /// Each element is a tuple `(vbase, size)`
    pub pending_maps: Map<usize, PTE>,
}

pub enum Step {
    // Mixed
    Invlpg,
    // Faulting memory op due to failed translation
    // (atomic walk)
    MemOpNoTr,
    // Faulting memory op due to failed translation
    // (non-atomic walk result)
    MemOpNoTrNA { vbase: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    TLBFill { core: Core, vaddr: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // TSO
    Write,
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}


impl State {
    pub open spec fn is_this_write_happy(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.all.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonneg_write(addr, value)
    }

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.all.contains(addr) ==> self.writes.core == core
    }

    //pub open spec fn wf(self, c: Constants) -> bool {
    //    true
    //}
    //
    //pub open spec fn inv(self, c: Constants) -> bool {
    //    self.happy ==> {
    //    &&& self.wf(c)
    //    }
    //}
}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            //neg: pre.writes.neg.insert(core, set![]),
            core: pre.writes.core,
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.pt_mem.pt_walk(memop_vaddr).result() is Invalid
    &&& memop.is_pagefault()

    &&& post == pre
}

pub open spec fn step_MemOpNoTrNA(
    pre: State,
    post: State,
    c: Constants,
    vbase: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.pending_maps.contains_key(vbase)
    &&& vbase <= vaddr < vbase + pre.pending_maps[vbase].frame.size
    &&& memop.is_pagefault()

    &&& post == pre
}

pub open spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, vaddr, memop)
    &&& pre.happy

    &&& {
    let pte = pre.tlbs[core][tlb_va];
    let pmem_idx = word_index_spec(pte.frame.base + (vaddr - tlb_va) as nat);
    &&& c.valid_core(core)
    &&& aligned(vaddr as nat, 8)
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& tlb_va <= vaddr < tlb_va + pte.frame.size
    &&& match memop {
        MemOp::Store { new_value, result } => {
            if pmem_idx < pre.phys_mem.len() && !pte.flags.is_supervisor && pte.flags.is_writable {
                &&& result is Ok
                &&& post.phys_mem === pre.phys_mem.update(pmem_idx as int, new_value as nat)
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
        MemOp::Load { is_exec, result } => {
            if pmem_idx < pre.phys_mem.len() && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                &&& result == LoadResult::Value(pre.phys_mem[pmem_idx as int])
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
    &&& post.writes == pre.writes
}

// ---- Non-atomic page table walks ----

/// A TLB fill in response to an atomic page table walk
pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }

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
pub open spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value)

    &&& post.happy      == pre.happy
    &&& post.phys_mem   == pre.phys_mem
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.tlbs       == pre.tlbs
    &&& post.writes.all == pre.writes.all.insert(addr)
    //&&& post.writes.neg == if !pre.pt_mem.is_nonneg_write(addr, value) {
    //        pre.writes.neg.map_values(|ws:Set<_>| ws.insert(addr))
    //    } else { pre.writes.neg }
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& pre.is_tso_read_deterministic(core, addr)
            ==> value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.
pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            all: if core == pre.writes.core { set![] } else { pre.writes.all },
            ..pre.writes
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& !pre.is_this_write_happy(core, addr, value)
    &&& !post.happy
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                    => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr                 => step_MemOpNoTr(pre, post, c, lbl),
        Step::MemOpNoTrNA { vbase }     => step_MemOpNoTrNA(pre, post, c, vbase, lbl),
        Step::MemOpTLB { tlb_va }       => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::TLBFill { core, vaddr }   => step_TLBFill(pre, post, c, core, vaddr, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::Write                     => step_Write(pre, post, c, lbl),
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
    &&& pre.tlbs === Map::new(|core| c.valid_core(core), |core| map![])
    &&& pre.happy == true
    //&&& pre.writes.core == ..
    &&& pre.writes.all === set![]
    &&& pre.pending_maps === map![]

    &&& c.valid_core(pre.writes.core)
    &&& forall|va| aligned(va as nat, 8) ==> #[trigger] pre.pt_mem.mem.contains_key(va)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& pre.pt_mem.pml4 <= u64::MAX - 4096
}

//proof fn init_implies_inv(pre: State, c: Constants)
//    requires init(pre, c)
//    ensures pre.inv(c)
//{}
//
//proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next_step(pre, post, c, step, lbl),
//    ensures post.inv(c)
//{}


} // verus!
