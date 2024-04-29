#![verus::trusted]
// trusted:
// describes how the whole system behaves
//
// this refers to definitions in an untrusted file, but uses them in a way that the
// state-machine refinement can check

use vstd::prelude::*;

use crate::spec_t::{ hardware, hlspec, mem };
use crate::impl_u::spec_pt;
use crate::definitions_t::{ between, MemRegion, overlap, PageTableEntry, aligned,
L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, WORD_SIZE };

verus! {
	
//INFO: OSConstants smth smth IronFleet
pub struct OSConstants {
    pub hw: hardware::HWConstants,
}
	

pub struct OSVariables {
    pub hw: hardware::HWVariables,
	pub log_pt: mem::PageTableMemory,
	pub pf: Map<(nat, nat), nat>,			
}

impl OSVariables {
	
	/*
	
    pub open spec fn NUMA_pt_mappings_dont_overlap_in_vmem(self) -> bool {
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
	*/

	
	//INFO is now referring to nr-log pt. however it is questionable if this is what we want
    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            pt_mem: self.log_pt,
        }
    }
	
	//INFO is now referring to nr-log pt. however it is questionable if this is what we want
    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.log_pt)
    }

    pub open spec fn effective_mappings(self) -> Map<nat,PageTableEntry> {
        Map::new(
            |base: nat| /* self.hw.tlb.dom().contains(base) || */ self.interp_pt_mem().dom().contains(base),
            |base: nat| /* if self.hw.tlb.dom().contains(base) { self.hw.tlb.index(base) } else { */ self.interp_pt_mem().index(base) ,
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
                let pmem_idx = mem::word_index_spec(paddr);
                self.hw.mem[pmem_idx as int]
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

//INFO: added OSConstant
pub open spec fn step_HW(c: OSConstants, s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {
	&&& s1.log_pt == s2.log_pt
    &&& s1.pf == s2.pf
    &&& !(system_step is PTMemOp)
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& spec_pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

//INFO: added OSConstants, NUMA_id and core_id
pub open spec fn step_Map(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat, base: nat, pte: PageTableEntry, result: Result<(),()>) -> bool {
	
	//PROPOSAL: put entry in log_pt if valid and set NUMA_id_pt to log_pt 
	//(this should simulate the NUMA_Node syncing the pagetable and adding a new entry to it. )
	//(however it is incorrect as putting entry into log_pt could return a log_pt that has more entries after new entry)
	&&& s1.log_pt == s2.log_pt
    &&& s1.pf == s2.pf
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}
	
//INFO: added OSConstants, NUMA_id and core_id
pub open spec fn step_Unmap(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat, base: nat, result: Result<(),()>) -> bool {
    // The hw step tells us that s2.tlb is a submap of s1.tlb, so all we need to specify is
    // that s2.tlb doesn't contain this particular entry.
	//INFO this is not necessary as it is already in step_PT
	&&& s1.log_pt == s2.log_pt
    &&& s1.pf == s2.pf
	&&& hardware::valid_core_id(c.hw, NUMA_id, core_id)
  	&&& s1.pf[(NUMA_id, core_id)] == 0
	//PROPOSAL: this for either one NUMA node or all
    &&& forall|NUMA_id: nat, core_id: nat| hardware::valid_core_id(c.hw, NUMA_id, core_id) ==> !s2.hw.NUMAs[NUMA_id].cores[core_id].tlb.dom().contains(base)
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

//INFO: added OSConstants, NUMA_id and core_id
pub open spec fn step_Resolve(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat , base: nat, result: Result<(nat,PageTableEntry),()>) -> bool {
	&&& s1.log_pt == s2.log_pt
    &&& s1.pf == s2.pf
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}

//INFO: added NUMA_id and core_id
#[allow(inconsistent_fields)]
pub enum OSStep {
    HW      { step: hardware::HWStep },
    Map     { NUMA_id:nat , core_id:nat, vaddr: nat, pte: PageTableEntry, result: Result<(),()> },
    Unmap   { NUMA_id:nat , core_id:nat, vaddr: nat, result: Result<(),()> },
    Resolve { NUMA_id:nat , core_id:nat, vaddr: nat, result: Result<(nat,PageTableEntry),()> },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { step } =>
                match step {
					//INFO: looses information on who is doing the readwrite
                    hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, NUMA_id, core_id } => hlspec::AbstractStep::ReadWrite { vaddr, op, pte },
                    hardware::HWStep::PTMemOp { NUMA_id, core_id}                       => arbitrary(),
                    hardware::HWStep::TLBFill { vaddr, pte, NUMA_id, core_id }              => hlspec::AbstractStep::Stutter,
                    hardware::HWStep::TLBEvict { vaddr, NUMA_id, core_id }                  => hlspec::AbstractStep::Stutter,
                },
			//INFO: added Core_id and NUMA_id
            OSStep::Map     { NUMA_id, core_id, vaddr, pte, result } => hlspec::AbstractStep::Map { vaddr, pte, result },
            OSStep::Unmap   { NUMA_id, core_id, vaddr, result }      => hlspec::AbstractStep::Unmap { vaddr, result },
            OSStep::Resolve { NUMA_id, core_id, vaddr, result }      => hlspec::AbstractStep::Resolve { vaddr, result },
        }
    }
}

// INFO: added NUMA_id and core_id
// INFO: added OSConstants
pub open spec fn next_step(c: OSConstants, s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW      { step }               => step_HW(c, s1, s2, step),
        OSStep::Map     { NUMA_id, core_id, vaddr, pte, result } => step_Map(c, s1, s2, NUMA_id, core_id, vaddr, pte, result),
        OSStep::Unmap   { NUMA_id, core_id, vaddr, result }      => step_Unmap(c, s1, s2, NUMA_id, core_id, vaddr, result),
        OSStep::Resolve { NUMA_id, core_id, vaddr, result }      => step_Resolve(c, s1, s2, NUMA_id, core_id, vaddr, result),
    }
}

//INFO: exist wegbekommen?
//INFO: added OSConstants
pub open spec fn next(c: OSConstants, s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(c, s1, s2, step)
}

//INFO: added OSConstants
pub open spec fn init(c: OSConstants, s: OSVariables) -> bool {
	&&& hardware::interp_pt_mem(s.log_pt) === Map::empty()
    &&& spec_pt::init(s.pt_variables())
    &&& hardware::init(c.hw, s.hw)
	&&& forall|NUMA_id: nat, core_id: nat| hardware::valid_core_id(c.hw, NUMA_id, core_id) ==> s.pf.contains_key((NUMA_id, core_id))
    &&& forall|NUMA_id: nat, core_id: nat| hardware::valid_core_id(c.hw, NUMA_id, core_id) ==> s.pf[(NUMA_id, core_id)] == 0
	
}

}
