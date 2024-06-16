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


pub struct OSConstants {
    pub hw: hardware::HWConstants,

    //maps User Level Thread to its core    
    pub ULT2core : Map<nat, (nat, nate)>,
    //highest thread_id
    pub ULT_no: nat,
}


pub struct OSVariables {

    pub hw: hardware::HWVariables,
    pub nr: nr::simple_log::SimpleLog::State,

    // maps node_id to its version
    pub replicas: Map<nat, nat>,
    // maps numa node to ULT id blocking it 
    // pub lock: Map<nat, nat>,
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

	//TODO this
	//INFO is now referring to nr-log pt. however it is questionable if this is what we want
    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            pt_mem: self.log_pt,
        }
    }
	
    //TODO this
	//INFO is now referring to nr-log pt. however it is questionable if this is what we want
    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.log_pt)
    }

    //TODO this
    pub open spec fn effective_mappings(self) -> Map<nat,PageTableEntry> {
        Map::new(
            |base: nat| /* self.hw.tlb.dom().contains(base) || */ self.interp_pt_mem().dom().contains(base),
            |base: nat| /* if self.hw.tlb.dom().contains(base) { self.hw.tlb.index(base) } else { */ self.interp_pt_mem().index(base) ,
            )
    }

    //TODO this
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
	
    //TODO this
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
            thread_no: self.ULT_no,
            phys_mem_size: self.hw.mem.len(),
        }
    }
}


//INFO: added OSConstant
pub open spec fn step_HW(c: OSConstants, s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {

    &&& !(system_step is PTMemOp)
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& nr::simple_log::SimpleLog::Step::no_op()
}

/*
pub open spec fn step_Map(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat, base: nat, pte: PageTableEntry, result: Result<(),()>) -> bool {

    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}
*/

//Proposal: add HW stutter step
//TODO update Replica
//TODO check im step_PTmemOP lets you change entire pt
pub open spec fn step_Map(c: OSConstants, s1: OSVariables, s2: OSVariables, nr_step: nr::simple_log::SimpleLog::Step<DT>, ULT_id: nat) ->
{
    let (NUMA_id, core_id) = c.ULT2core.index(ULT_id);
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& match step {
        nr::simple_log::SimpleLog::Step::update_start(rid, uop) =>{
            true,
         },
         nr::simple_log::SimpleLog::Step::update_add_op_to_log(rid) => {
            true,
         },
         nr::simple_log::SimpleLog::Step::update_incr_version(logidx) => {
            true,
         },
         nr::simple_log::SimpleLog::Step::update_finish(rid, resp) => {
            true,
         },
         _ => {false},
    }
}
	
//INFO: added OSConstants, NUMA_id and core_id
pub open spec fn step_Unmap(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat, base: nat, result: Result<(),()>) -> bool {
    // The hw step tells us that s2.tlb is a submap of s1.tlb, so all we need to specify is
    // that s2.tlb doesn't contain this particular entry.
	//INFO this is not necessary as it is already in step_PT

	&&& hardware::valid_core_id(c.hw, NUMA_id, core_id)

	//PROPOSAL: this for either one NUMA node or all
    &&& forall|NUMA_id: nat, core_id: nat| hardware::valid_core_id(c.hw, NUMA_id, core_id) ==> !s2.hw.NUMAs[NUMA_id].cores[core_id].tlb.dom().contains(base)
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

//INFO: added OSConstants, NUMA_id and core_id
pub open spec fn step_Resolve(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat , base: nat, result: Result<(nat,PageTableEntry),()>) -> bool {
	
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}

//INFO: added NUMA_id and core_id
#[allow(inconsistent_fields)]
pub enum OSStep {
    HW      { step: hardware::HWStep },
    Map     { nr_step: nr::simple_log::SimpleLog::Step<DT>, ULT_id: nat, vaddr: nat, pte: PageTableEntry, result: Result<(),()>,},
    Unmap   { nr_step: nr::simple_log::SimpleLog::Step<DT>, ULT_id: nat, vaddr: nat, pte: PageTableEntry, result: Result<(),()> },
    Resolve { nr_step: nr::simple_log::SimpleLog::Step<DT>, ULT_id: nat, vaddr: nat, result: Result<(nat,PageTableEntry),()> },
}



//INFO map updated OS Steps to updated HL steps
impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::HW { step } =>
                match step {
					//INFO: looses information on who is doing the readwrite
                    hardware::HWStep::ReadWrite { vaddr, paddr, op, pte, NUMA_id, core_id } => hlspec::AbstractStep::ReadWrite { vaddr, op, pte },
                    hardware::HWStep::PTMemOp { NUMA_id, core_id}                           => arbitrary(),
                    hardware::HWStep::TLBFill { vaddr, pte, NUMA_id, core_id }              => hlspec::AbstractStep::Stutter,
                    hardware::HWStep::TLBEvict { vaddr, NUMA_id, core_id }                  => hlspec::AbstractStep::Stutter,
                },
			OSStep::Map { nr_step, ULT_id, vaddr, pte, result } =>
                match nr_step {
                    nr::simple_log::SimpleLog::Step::update_start(rid, uop)      => {hlspec::AbstractStep::Map_Start {thread_id: ULT_id, vaddr, pte}},
                    nr::simple_log::SimpleLog::Step::update_add_op_to_log(rid)   => {hlspec::AbstractStep::Stutter},
                    nr::simple_log::SimpleLog::Step::update_incr_version(logidx) => {hlspec::AbstractStep::Stutter},
                    nr::simple_log::SimpleLog::Step::update_finish(rid, resp)    => {hlspec::AbstractStep::Map_End {thread_id: ULT_id, result}},
                    _ => {arbitary()},
                },
            OSStep::Unmap { nr_step, ULT_id, vaddr, pte, result } =>
                match nr_step {
                    nr::simple_log::SimpleLog::Step::update_start(rid, uop)      => {hlspec::AbstractStep::Unmap_Start {thread_id: ULT_id, vaddr, pte}},
                    nr::simple_log::SimpleLog::Step::update_add_op_to_log(rid)   => {hlspec::AbstractStep::Stutter},
                    nr::simple_log::SimpleLog::Step::update_incr_version(logidx) => {hlspec::AbstractStep::Stutter},
                    nr::simple_log::SimpleLog::Step::update_finish(rid, resp)    => {hlspec::AbstractStep::Unmap_End {thread_id: ULT_id, result}},
                    _ => {arbitary()},
                },
            OSStep::Resolve { nr_step, ULT_id, vaddr, result }      =>
                match nr_step {
                    nr::simple_log::SimpleLog::Step::readonly_start(rid, uop)          => {hlspec::AbstractStep::Resolve_Start {thread_id: ULT_id, vaddr}},
                    nr::simple_log::SimpleLog::Step::readonly_read_version(rid)        => {hlspec::AbstractStep::Stutter},
                    nr::simple_log::SimpleLog::Step::readonly_finish(rid, logidx, rop) => {hlspec::AbstractStep::Resolve_End {thread_id: ULT_id, result}},
                    _ => {arbitary()},
                },
        }
    }
}


pub open spec fn next_step(c: OSConstants, s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::HW      { step }                                 => step_HW     (c, s1, s2, step),
        OSStep::Map     { nr_step, ULT_id, vaddr, pte, result }  => step_Map    (c, s1, s2, ULT_id, vaddr, pte, result),
        OSStep::Unmap   { nr_step, ULT_id, vaddr, pte, result }  => step_Unmap  (c, s1, s2, ULT_id, vaddr, pte, result),
        OSStep::Resolve { nr_step, ULT_id, vaddr, result }       => step_Resolve(c, s1, s2, ULT_id, vaddr, result),
    }
}

pub open spec fn next(c: OSConstants, s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(c, s1, s2, step)
}

//INFO: added OSConstants
pub open spec fn init(c: OSConstants, s: OSVariables) -> bool {
    //TODO hardware stuff
	&&& hardware::interp_pt_mem(s.log_pt) === Map::empty()
    &&& hardware::init(c.hw, s.hw)
    //wf of ULT2core mapping
	&&& forall |id: nat| id <= c.ULT_no <==> c.ULT2core.contains_key(id)
    &&& forall |id: nat| id <= c.ULT_no ==> let (NUMA_id, core_id) = ULT2core.index(id) in hardware::valid_core_id(c.hw, NUMA_id, core_id)
   
    &&& nr::simple_log::SimpleLog::Initialize()
}

}
