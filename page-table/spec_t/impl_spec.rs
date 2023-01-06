#![allow(unused_imports)]
use builtin_macros::*;
use builtin::*;
use crate::spec_t::hlspec;
use crate::pervasive::*;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult, ResolveResult, ResolveResultExec, PageTableEntry };
use crate::impl_u::spec_pt;
use crate::spec_t::hardware::interp_pt_mem;
use crate::spec_t::mem;
use option::*;
use set::*;

verus! {

pub trait InterfaceSpec {
    spec fn ispec_inv(&self, memory: mem::PageTableMemory) -> bool;

    proof fn ispec_init_implies_inv(&self, memory: mem::PageTableMemory)
        requires
            memory.inv(),
            memory.regions() === set![memory.cr3_spec()@],
            memory.region_view(memory.cr3_spec()@).len() == 512,
            (forall|i: nat| i < 512 ==> memory.region_view(memory.cr3_spec()@)[i as int] == 0),
        ensures
            self.ispec_inv(memory);

    fn ispec_map_frame(&self, memory: mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: (MapResult, mem::PageTableMemory))
        requires
            memory.alloc_available_pages() >= 3, // TODO: maybe this shouldn't be here and instead
                                                 // we add and call a "refill" method in map_frame?
            spec_pt::step_Map_enabled(interp_pt_mem(memory), vaddr as nat, pte@),
            self.ispec_inv(memory),
        ensures
            self.ispec_inv(res.1),
            spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(res.1) }, vaddr as nat, pte@, res.0);

    fn ispec_unmap(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (UnmapResult, mem::PageTableMemory))
        requires
            spec_pt::step_Unmap_enabled(vaddr as nat),
            self.ispec_inv(memory),
        ensures
            self.ispec_inv(res.1),
            spec_pt::step_Unmap(spec_pt::PageTableVariables { map: interp_pt_mem(memory) }, spec_pt::PageTableVariables { map: interp_pt_mem(res.1) }, vaddr as nat, res.0);

    fn ispec_resolve(&self, memory: mem::PageTableMemory, vaddr: usize) -> (res: (ResolveResultExec, mem::PageTableMemory))
        requires
            spec_pt::step_Resolve_enabled(vaddr as nat),
            self.ispec_inv(memory),
        ensures
            res.1 === memory,
            spec_pt::step_Resolve(
                spec_pt::PageTableVariables { map: interp_pt_mem(memory) },
                spec_pt::PageTableVariables { map: interp_pt_mem(memory) },
                vaddr as nat,
                res.0@
            );
}

}
