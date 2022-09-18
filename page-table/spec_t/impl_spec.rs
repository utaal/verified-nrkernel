#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::spec_t::hlspec;
use crate::pervasive::*;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult, ResolveResult, PageTableEntry };
use crate::impl_u::spec_pt;
use crate::spec_t::hardware::interp_pt_mem;
use crate::mem_t as mem;
use crate::impl_u::l2_impl;
use option::*;

verus! {

pub struct PTState {
    pub memory: mem::PageTableMemory,
}

// FIXME: What's the pen-and-paper VC here? I think it's: The specification for each of the
// operations specified here results in the corresponding state transition in the *os* state
// machine being satisfied.
// FIXME: do i need to add memory invariant preservation to the ensures?
// Do i actually need it?
pub trait PTImpl {
    spec fn implspec_inv(&self, memory: mem::PageTableMemory) -> bool;

    proof fn implspec_init_implies_inv(&self, memory: mem::PageTableMemory)
        requires
            spec_pt::init(spec_pt::PageTableVariables { map: interp_pt_mem(memory) })
        ensures
            self.implspec_inv(memory);

    fn implspec_map_frame(&self, memory: mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory))
        requires
            spec_pt::step_Map_enabled(interp_pt_mem(memory), vaddr, pte@),
            self.implspec_inv(memory),
        ensures
            self.implspec_inv(res.1),
            spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(res.1) }, vaddr, pte@, res.0);

    // FIXME: do i need to add tlb state to the spec_pt state machine?
    fn implspec_unmap(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (UnmapResult, mem::PageTableMemory))
        requires
            spec_pt::step_Unmap_enabled(vaddr),
            self.implspec_inv(memory),
        ensures
            self.implspec_inv(res.1),
            spec_pt::step_Unmap(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(res.1) }, vaddr, res.0);
            // FIXME: tlb stuff

    // can't write a valid trigger for this
    // fn implspec_resolve(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (ResolveResult<usize>, mem::PageTableMemory))
    //     requires
    //         spec_pt::step_Resolve_enabled(vaddr),
    //         self.implspec_inv(memory),
    //     ensures
    //         self.implspec_inv(res.1),
    //         exists|pte:Option<(nat,PageTableEntry)>| {
    //             let rr: ResolveResult<nat> = match res.0 {
    //                 ResolveResult::PAddr(n)    => ResolveResult::PAddr(n as nat),
    //                 ResolveResult::ErrUnmapped => ResolveResult::ErrUnmapped,
    //             };
    //             #[trigger] spec_pt::step_Resolve(
    //                 spec_pt::PageTableVariables { map: interp_pt_mem(memory) },
    //                 spec_pt::PageTableVariables { map: interp_pt_mem(res.1) },
    //                 vaddr,
    //                 pte,
    //                 rr
    //             )};
}

/// We axiomatize the page table walker with the implementation's interpretation function.
#[verifier(external_body)]
pub proof fn axiom_page_table_walk_interp()
    ensures
        forall|pt: l2_impl::PageTable| pt.inv() ==> #[trigger] pt.interp().interp().map === interp_pt_mem(pt.memory);

}
