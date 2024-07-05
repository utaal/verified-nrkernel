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
    pub ULT2core : Map<nat, Core>,
    //highest thread_id
    pub ULT_no: nat,
}


pub struct OSVariables {

    pub hw: hardware::HWVariables,
    pub nr: nr::simple_log::SimpleLog::State,
    // maps numa node to ULT id blocking it 
    pub core_state: Map<Core, OSArguments>,
    pub TLB_Shootdown: Map<(core, core), bool>,
}


pub struct OSArguments {
    Map   { ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>},
    Unmap { ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>},
    Resolve { ULT_id: nat},
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

	//TODO delete this
    // this is only used for spec_pt transitions so its not used anymore
    pub open spec fn pt_variables(self) -> spec_pt::PageTableVariables {
        spec_pt::PageTableVariables {
            pt_mem: self.log_pt,
        }
    }

    //TODO look into this again, when dispatchstuff is implemented
    //The log page
    pub open spec fn interp_pt_mem(self) -> Map<nat,PageTableEntry> {
        hardware::interp_pt_mem(self.NRVariables.nrstate_at_version::<DT>(NRVariables.log.len))
    }

    pub open spec fn interp_numa_pt_mem(self, numa: nat) -> Map<nat,PageTableEntry>
        recommends self.NRVariables.replica_versions.contains(numa)
    { 
        hardware::interp_pt_mem(self.NRVariables.nrstate_at_version::<DT>(self.NRVariables.replica_versions.contains(numa)))
    }

    pub open spec fn effective_mappings(self, core: Core) -> Map<nat,PageTableEntry> 
        recommends self.hw.NUMAs.contains_key(core.NUMA_id),
                   self.hw.NUMAs[core.NUMA_id].cores.contains_key(core.core_id)
    {
        self.interp_mem_pt_mem(core.NUMA_id).union_prefer_right(self.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb)
    }

    pub open spec fn interp_vmem(self, core: Core) -> Map<nat,nat> {
        let phys_mem_size = self.interp_constants().phys_mem_size;
        let mappings: Map<nat,PageTableEntry> = self.effective_mappings(core);
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

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// HW/NR-Statemachine steps 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub open spec fn step_HW(c: OSConstants, s1: OSVariables, s2: OSVariables, system_step: hardware::HWStep) -> bool {
    &&& !(system_step is PTMemOp)
    &&& hardware::next_step(c.hw, s1.hw, s2.hw, system_step)
    &&& nr::simple_log::SimpleLog::Step::no_op()
}

pub open spec fn step_nr (c: OSConstants, s1: OSVariables, s2: OSVariables, aop: <DT>) -> bool {
    &&& s1.hw == s2.hw // optional pmem_op
    &&& s2.core_state == s1.core_state
    &&& nr::simple_log::SimpleLog::State::next(s1.nr, s2.nr, aop);
    &&& match aop {
        AsyncLabel::<DT>::Start(rid, InputOperation::Read(op, node_id))    => { true  }, //resolve/readonly start
        AsyncLabel::<DT>::End(rid, OutputOperation::Read(ret));            => { true  }, //resolve/readonly end 
        AsyncLabel::<DT>::Start(rid, InputOperation::Write(op));           => { false }, //update start
        AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));           => { false }, //update end
        Internal                                                           => { true  }, //everything else
        _                                                                  => { false }, //mmu label 
     }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Map
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub open spec fn step_Map_Start (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>} ) -> bool {
    let core = c.ULT2core.index(ULT_id);
    let os_arg = OSArguments::Map {ULT_id, rid, vaddr, pte, result},
    &&& s1.core_state[core] is OSArguments::Empty
    &&& s2.core_state == s1.core_state.insert(core, os_args)
    &&& s2.hw == s1.hw
    &&& s2.shootdown == s1.shootdown
    &&& aop is AsyncLabel::<DT>::Start(rid, InputOperation::Write(op))
    &&& nr::simple_log::SimpleLog::State::next(s1.nr, s2.nr, aop)
}


pub open spec fn step_Map_End (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat, aop: AsyncLabel::<DT> ) -> bool {
    let (NUMA_id, core_id) = c.ULT2core.index(ULT_id);
    if let OSArguments::Map {ULT_id: ult_id, rid, vaddr, pte, result} = s1.core_state[(NUMA_id, core_id)] {
        &&& ULT_id == ult_id
        &&& s2.core_state == s1.core_state.insert((NUMA_id, core_id), OSArguments::Empty)
        &&& s2.hw == s1.hw
        &&& s2.shootdown == s1.shootdown
        aop is  AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));  
        &&& nr::simple_log::SimpleLog::State::next(s1.nr, s2.nr, aop)
    } else { false }
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Unmap
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//NR shootsdown all cores that run the same process -> entire shootdown row is set true at beginning of shootdown



pub open spec fn step_Unmap_Start (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat, rid: nat, vaddr: nat, pte: PageTableEntry, result: result<()()>} ) -> bool {
    let core = c.ULT2core.index(ULT_id);
    let version = //TODO;
    let os_arg = OSArguments::Map {ULT_id, rid, vaddr, pte, result, version},
    &&& s1.core_state[core] is OSArguments::Empty
    &&& s2.core_state == s1.core_state.insert(core, os_args)
    &&& s2.hw == s1.hw
    &&& forall |handler: (nat, nat)| hardware::valid_core_id(c.hw, handler) ==> s2.shootdown[(core, handler)] 
    //TODO debug this line
    &&& forall |dispatcher: (nat,nat), handler: (nat, nat)| hardware::valid_core_id(c.hw, handler) && hardware::valid_core_id(c.hw, dispatcher) && dispatcher !== core ==> s2.shootdown[(dispatcher, handler)] === s1.shootdown[(dispatcher, handler)] 
    &&& s2.shootdown.dom() === s1.shootdown.dom()
    //TODO more condidtions on aop
    &&& aop is AsyncLabel::<DT>::Start(rid, InputOperation::Write(op));
    &&& nr::simple_log::SimpleLog::State::next(s1.nr, s2.nr, aop);

}

//proposal B.2 
// make shootdown step hw::TLB_evict if entry is in TLB otherwise HW::stutter_step -> dosnt restrict other evicts but makes sure that special "shootdown" step cant happend during maps
// -> shootdown sets shootdown map bit false -> shootdown step is not just redundant to hw step
// require that all numa_nodes have a version number higher than unmap-version-number and all shootdown for unmap to finish

//what if we unmapped and mapped same entry? and by 

pub open spec fn step_shootdown (c: OSConstants, s1: OSVariables, s2: OSVariables, core: Core, dispatcher: Core) -> bool {
    
    &&& hardware::valid_core_id(c.hw, core) 
    &&& hardware::valid_core_id(c.hw, dispatcher) 
    &&& s1.shootdown[(dispatcher, core)]
    &&& s1.core_state[core] is OSArguments::Unmap || s1.core_state[core] is OSArguments::Empty

    &&& s2.core_state = s1.core_state
    &&& s2.nr == s1.nr
    &&& s2.shootdown = s1.shootdown.insert((dispatcher, core), false)
    &&& if let OSArguments::Unmap {ULT_id: ult_id, rid, vaddr, pte, result, version} = s1.core_state[core] {
            if s.hw.NUMAs[core.NUMA_id].cores[core.core_id].tlb.dom().contains(vaddr) { 
                hardware::step_tlb_evict(c.hw, s1.hw, s2.hw, vaddr, core)) 
            } else { 
                s2.hw == s1.hw
            }
        } else {false}
}


pub open spec fn step_Unmap_End (c: OSConstants, s1: OSVariables, s2: OSVariables, ULT_id: nat ) -> bool {
    let core = c.ULT2core.index(ULT_id);
    &&& forall |id : (nat, nat)| hardware::valid_core_id(c.hw, id)  ==>  !s1.shootdown[(core, id)]
    //TODO more condidtions on aop
    &&& aop is  AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));  
    
    &&& nr::simple_log::SimpleLog::State::next(s1.nr, s2.nr, aop);
    &&& s2.shootdown == s1.shootdown
    &&& s2.hw == s1.hw
    &&& s2.core_state == s1.core_state.insert(core), OSArguments::Empty)
    &&& if let OSArguments::Unmap {ULT_id: ult_id, rid, vaddr, pte, result, version} = s1.core_state[core] {
            &&& ULT_id == ult_id
            //TODO &&& forall |replica: nat| replica < c.hw.NUMA_no ==> s1.nr.replicas[replica] > version 
            
        } else { false }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Resolve
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//TODO everything

pub open spec fn step_Resolve(c: OSConstants, s1: OSVariables, s2: OSVariables, NUMA_id:nat , core_id:nat , base: nat, result: Result<(nat,PageTableEntry),()>) -> bool {
	
    &&& hardware::step_PTMemOp(c.hw, s1.hw, s2.hw, NUMA_id, core_id)
    &&& spec_pt::step_Resolve(s1.pt_variables(), s2.pt_variables(), base, result)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Statemachine functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
            OSStep::NR { step } =>
                match step {
                    nr::simple_log::SimpleLog::Step::update_start(rid, uop)            =>  arbitrary(),
                    nr::simple_log::SimpleLog::Step::update_finish(rid, resp)          =>  arbitrary(),
                    nr::simple_log::SimpleLog::Step::dummy_to_use_type_params(state)   =>  arbitrary(), 
                },
			OSStep::Map_Start     { ULT_id, vaddr, pte, result }     => { hlspec::AbstractStep::Map_Start     {thread_id: ULT_id, vaddr, pte},
            OSStep::Map_End       { ULT_id, vaddr, pte, result }     => { hlspec::AbstractStep::Map_End       {thread_id: ULT_id, result},
            OSStep::Unmap_Start   { ULT_id, vaddr, pte, result }     => { hlspec::AbstractStep::Unmap_Start   {thread_id: ULT_id, vaddr, pte},
            OSStep::Unmap_End     { ULT_id, vaddr, pte, result }     => { hlspec::AbstractStep::Unmap_End     {thread_id: ULT_id, result},
            OSStep::Resolve_Start { nr_step, ULT_id, vaddr, result } => { hlspec::AbstractStep::Resolve_Start {thread_id: ULT_id, result },
            OSStep::Resolve_Start { nr_step, ULT_id, vaddr, result } => { hlspec::AbstractStep::Resolve_End   {thread_id: ULT_id, result },
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
    //wf of shootdown
    &&& forall |dispatcher: (nat, nat), handler: (nat, nat) | hardware::valid_core_id(c.w, dispatcher) && hardware::valid_core_id(c.hw, handler) <==> shootdown.dom().contains(dispatcher, handler)
    &&& forall |dispatcher: (nat, nat), handler: (nat, nat) | hardware::valid_core_id(c.w, dispatcher) && hardware::valid_core_id(c.hw, handler) ==> !shootdown[(dispatcher, handler)]
    
    &&& nr::simple_log::SimpleLog::Initialize()

}

}
