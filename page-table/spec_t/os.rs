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

    // maps node_id to its (min?) version
    pub replicas: Map<nat, nat>,
    // maps numa node to ULT id blocking it 
    pub core_state: Map<(nat, core), OSArguments>,
}


pub struct OSArguments {
    Map   {ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>},
    Unmap {ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>},
    Empty,
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


//self.NRvariables.nrstate_at_version::<DT>(NRVariables.log.len)
//self.FNRVariables.nrstate_at_version::<DT>(NRVariables.version)


	//TODO delete this
    // this is only used for spec_pt transitions so its not used anymore
    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            pt_mem: self.log_pt,
        }
    }
	
    //TODO adjust DT. Think what compute log does and how it needs to be implemented/changed
    // also think about what our view is. i dont think it was the pagetable? but it would make sense to me
	//INFO is now referring to nr-log pt. however it is questionable if this is what we want
    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.NRVariables.nrstate_at_version::<DT>(NRVariables.log.len))
    }

    //TODO see above and change if needed
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
	
    //TODO add solution for thread_state and sound bool
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

pub open spec fn core_state_unchanged_besides_thread_state(
    s1: AbstractVariables,
    s2: AbstractVariables,
    thread_id: nat,
    thread_arguments: AbstractArguments,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
    &&& s2.mem === s1.mem
    &&& s2.mappings === s1.mappings
    &&& s2.sound == s1.sound
}


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

//TODO think aboutt Replica min version.
//TODO built aop from os_step
pub open spec fn step_Map(c: OSConstants, s1: OSVariables, s2: OSVariables, nr_step: nr::simple_log::SimpleLog::Step<DT>, ULT_id: nat, os_args: OSArguments) -> bool
{
    let (NUMA_id, core_id) = c.ULT2core.index(ULT_id);
    let if OSArguments::Map {ULT_id: ult_id, rid, vaddr, pte, result}, = os_args {
        let aop = //TODO
        &&& s2.replicas == s1.replicas
        &&& ULT_id == ult_id
        &&& nr::simple_log::SimpleLog::State::next_by(s1.nr, s2.nr, aop, nr_step)
        &&& match nr_step {
            nr::simple_log::SimpleLog::Step::update_start(rid, uop) =>{
                &&& s1.core_state[(NUMA_id, core_id)] is OSArguments::Empty
                &&& s2.core_state == s1.core_state.insert((NUMA_id, core_id), os_args)
                &&& s1.hw == s2.hw
            },
            nr::simple_log::SimpleLog::Step::update_add_op_to_log(rid) => {
                &&& s1.core_state[(NUMA_id, core_id)] == os_args
                &&& s2.core_state == s1.core_state
                &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id) //TODO check this
            },
            nr::simple_log::SimpleLog::Step::update_incr_version(logidx) => {
                &&& s1.core_state[(NUMA_id, core_id)] == os_args
                &&& s2.core_state == s1.core_state
                &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id) //TODO check this
            },
            nr::simple_log::SimpleLog::Step::update_finish(rid, resp) => {
                &&& s1.core_state[(NUMA_id, core_id)] == os_args
                &&& s2.core_state == s1.core_state.insert((NUMA_id, core_id), OSArguments::Empty)
                &&& s1.hw == s2.hw
            },
             _ => {false},
        }
    } else {
        false
    }
}


pub open spec fn step_Map_Start (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>} ) -> bool {
    let (NUMA_id, core_id) = c.ULT2core.index(ULT_id);
    let os_arg = OSArguments::Map {ULT_id, rid, vaddr, pte, result},
    &&& s1.core_state[(NUMA_id, core_id)] is OSArguments::Empty
    &&& s2.core_state == s1.core_state.insert((NUMA_id, core_id), os_args)
    &&& s2.replicas == s1.replicas
    &&& s2.hw == s1.hw
    &&& nr::simple_log::SimpleLog::Step::update_start(rid, uop)
}


pub open spec fn step_Map_End (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat ) -> bool {
    let (NUMA_id, core_id) = c.ULT2core.index(ULT_id);
    if let OSArguments::Map {ULT_id: ult_id, rid, vaddr, pte, result} = s1.core_state[(NUMA_id, core_id)] {
        &&& ULT_id == ult_id
        &&& s2.core_state == s1.core_state.insert((NUMA_id, core_id), OSArguments::Empty)
        &&& s2.replicas == s1.replicas
        &&& s2.hw == s1.hw
        &&& nr::simple_log::SimpleLog::Step::update_end(rid, uop)
    } else { false }
}

pub open spec fn step_nr (c: OSConstants, s1: OSVariables, s2: OSVariables, aop: <DT>, step: nr::simple_log::SimpleLog::Step<DT>) -> bool {
    &&& s1.hw == s2.hw // optional pmem_op
    &&& s1.replicas == s2.replicas // also not right
    &&& s2.core_state == s1.core_state
    &&& nr::simple_log::SimpleLog::State::next_by(s1.nr, s2.nr, aop, step);
    &&& match step {
        nr::simple_log::SimpleLog::Step::readonly_start(rid, rop)          => { true  },
        nr::simple_log::SimpleLog::Step::readonly_read_version(rid)        => { true  },
        nr::simple_log::SimpleLog::Step::readonly_finish(rid, logidx, rop) => { true  },
        nr::simple_log::SimpleLog::Step::update_start(rid, uop)            => { false }, //no
        nr::simple_log::SimpleLog::Step::update_add_op_to_log(rid)         => { true  },
        nr::simple_log::SimpleLog::Step::update_incr_version(logidx)       => { false }, //no 
        nr::simple_log::SimpleLog::Step::update_finish(rid, resp)          => { true  },
        SimpleLog::Step::no_op()                                           => { true  },
        SimpleLog::Step::dummy_to_use_type_params(state)                   => { false }, //no
    }
}

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


pub open spec fn step_Resolve(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat , base: nat, result: Result<(nat,PageTableEntry),()>) -> bool {
	
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}


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
