#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use map::*;
use seq::*;
use set_lib::*;

use option::{ *, Option::* };
use crate::spec_t::{ hardware, hlspec };
use crate::impl_u::spec_pt;
use crate::definitions_t::{ between, MemRegion, overlap, PageTableEntry, RWOp, MapResult, UnmapResult, ResolveResult, Arch, aligned, new_seq, candidate_mapping_overlaps_existing_vmem, candidate_mapping_overlaps_existing_pmem };
use crate::definitions_t::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use crate::spec_t::mem::{ word_index_spec };
use option::{ *, Option::* };
use crate::impl_u::lib;

verus! {

pub struct OSVariables {
    pub hw: hardware::HWVariables,
}

impl OSVariables {
    pub open spec fn pt_mappings_dont_overlap_in_vmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: pte1.frame.size },
                    MemRegion { base: b2, size: pte2.frame.size }))
    }

    pub open spec fn pt_mappings_dont_overlap_in_pmem(self) -> bool {
        forall|b1: nat, pte1: PageTableEntry, b2: nat, pte2: PageTableEntry|
            self.interp_pt_mem().contains_pair(b1, pte1) && self.interp_pt_mem().contains_pair(b2, pte2) ==>
            ((b1 == b2) || !overlap(pte1.frame, pte2.frame))
    }

    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, pte| self.hw.tlb.contains_pair(base, pte) ==> #[trigger] self.interp_pt_mem().contains_pair(base, pte)
    }

    pub open spec fn pt_entry_sizes_are_valid(self) -> bool {
        forall|base, pte| self.interp_pt_mem().contains_pair(base, pte) ==> {
            ||| pte.frame.size == L3_ENTRY_SIZE
            ||| pte.frame.size == L2_ENTRY_SIZE
            ||| pte.frame.size == L1_ENTRY_SIZE
        }
    }

    #[verifier(opaque)]
    pub open spec fn pt_entries_aligned(self) -> bool {
        forall|base, pte| self.interp_pt_mem().contains_pair(base, pte)
            ==> aligned(base, 8) && aligned(pte.frame.base, 8)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.pt_mappings_dont_overlap_in_vmem()
        &&& self.pt_mappings_dont_overlap_in_pmem()
        &&& self.pt_entry_sizes_are_valid()
        &&& self.pt_entries_aligned()
        &&& self.tlb_is_submap_of_pt()
    }

    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            map: self.interp_pt_mem(),
        }
    }

    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.hw.pt_mem)
    }

    pub open spec fn effective_mappings(self) -> Map<nat,PageTableEntry> {
        Map::new(
            |base: nat| self.hw.tlb.dom().contains(base) || self.interp_pt_mem().dom().contains(base),
            |base: nat| if self.hw.tlb.dom().contains(base) { self.hw.tlb.index(base) } else { self.interp_pt_mem().index(base) },
            )
    }

    pub open spec fn interp_vmem(self) -> Map<nat,nat> {
        let phys_mem_size = self.interp_constants().phys_mem_size;
        let mappings: Map<nat,PageTableEntry> = self.effective_mappings();
        Map::new(
            |vmem_idx: nat| hlspec::mem_domain_from_mappings_contains(phys_mem_size, vmem_idx, mappings),
            |vmem_idx: nat| {
                let vaddr = vmem_idx * WORD_SIZE as nat;
                let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
                let paddr = (pte.frame.base + (vaddr - base)) as nat;
                let pmem_idx = word_index_spec(paddr);
                self.hw.mem[pmem_idx]
            })
    }

    pub open spec fn interp(self) -> hlspec::AbstractVariables {
        let mappings: Map<nat,PageTableEntry> = self.effective_mappings();
        let mem: Map<nat,nat> = self.interp_vmem();
        hlspec::AbstractVariables {
            mem,
            mappings,
        }
    }

    pub open spec fn interp_constants(self) -> hlspec::AbstractConstants {
        hlspec::AbstractConstants {
            phys_mem_size: self.hw.mem.len(),
        }
    }
}

pub open spec fn step_HW(s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& hardware::next_step(s1.hw, s2.hw, system_step)
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

pub open spec fn step_Map(s1: OSVariables, s2: OSVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}

pub open spec fn step_Unmap(s1: OSVariables, s2: OSVariables, base: nat, result: UnmapResult) -> bool {
    // The hw step tells us that s2.tlb is a submap of s1.tlb, so all we need to specify is
    // that s2.tlb doesn't contain this particular entry.
    &&& !s2.hw.tlb.dom().contains(base)
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

pub open spec fn step_Resolve(s1: OSVariables, s2: OSVariables, base: nat, result: ResolveResult) -> bool {
    &&& hardware::step_PTMemOp(s1.hw, s2.hw)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}


pub enum OSStep {
    HW      { step: hardware::HWStep },
    Map     { vaddr: nat, pte: PageTableEntry, result: MapResult },
    Unmap   { vaddr: nat, result: UnmapResult },
    Resolve { vaddr: nat, result: ResolveResult },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { step } =>
                match step {
                    hardware::HWStep::ReadWrite { vaddr, paddr, op, pte } => hlspec::AbstractStep::ReadWrite { vaddr, op, pte },
                    hardware::HWStep::PTMemOp                             => arbitrary(),
                    hardware::HWStep::TLBFill { vaddr, pte }              => hlspec::AbstractStep::Stutter,
                    hardware::HWStep::TLBEvict { vaddr }                  => hlspec::AbstractStep::Stutter,
                },
            OSStep::Map     { vaddr, pte, result } => hlspec::AbstractStep::Map { vaddr, pte, result },
            OSStep::Unmap   { vaddr, result }      => hlspec::AbstractStep::Unmap { vaddr, result },
            OSStep::Resolve { vaddr, result }      => hlspec::AbstractStep::Resolve { vaddr, result },
        }
    }
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW      { step }               => step_HW(s1, s2, step),
        OSStep::Map     { vaddr, pte, result } => step_Map(s1, s2, vaddr, pte, result),
        OSStep::Unmap   { vaddr, result }      => step_Unmap(s1, s2, vaddr, result),
        OSStep::Resolve { vaddr, result }      => step_Resolve(s1, s2, vaddr, result),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

pub open spec fn init(s: OSVariables) -> bool {
    hardware::init(s.hw)
}

}
