#![verus::trusted]
// trusted:
// these are the interface specifications, they are part of the theorem

use vstd::prelude::*;
use crate::definitions_t::{ PageTableEntryExec, ResolveResultExec };
use crate::impl_u::spec_pt;
use crate::spec_t::hardware::interp_pt_mem;
use crate::spec_t::mem;

verus! {

pub trait InterfaceSpec {
    spec fn ispec_inv(&self, mem: &mem::PageTableMemory) -> bool;

    proof fn ispec_init_implies_inv(&self, mem: &mem::PageTableMemory)
        requires
            mem.inv(),
            mem.regions() === set![mem.cr3_spec()@],
            mem.region_view(mem.cr3_spec()@).len() == 512,
            (forall|i: nat| i < 512 ==> mem.region_view(mem.cr3_spec()@)[i as int] == 0),
        ensures
            self.ispec_inv(mem);

    fn ispec_map_frame(&self, mem: &mut mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: Result<(),()>)
        requires
            old(mem).alloc_available_pages() >= 3,
            spec_pt::step_Map_enabled(interp_pt_mem(*old(mem)), vaddr as nat, pte@),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Map(spec_pt::PageTableVariables { map: interp_pt_mem(*old(mem)) }, spec_pt::PageTableVariables { map: interp_pt_mem(*mem) }, vaddr as nat, pte@, res);

    fn ispec_unmap(&self, mem: &mut mem::PageTableMemory, vaddr: usize) -> (res: Result<(),()>)
        requires
            spec_pt::step_Unmap_enabled(vaddr as nat),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Unmap(spec_pt::PageTableVariables { map: interp_pt_mem(*old(mem)) }, spec_pt::PageTableVariables { map: interp_pt_mem(*mem) }, vaddr as nat, res);

    fn ispec_resolve(&self, mem: &mem::PageTableMemory, vaddr: usize) -> (res: ResolveResultExec)
        requires
            spec_pt::step_Resolve_enabled(vaddr as nat),
            self.ispec_inv(mem),
        ensures
            spec_pt::step_Resolve(
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                spec_pt::PageTableVariables { map: interp_pt_mem(*mem) },
                vaddr as nat,
                res@
            );
}

pub struct PageTableImpl {}

pub closed spec fn implements_interface_spec<T: InterfaceSpec>() -> bool {
    true
}

// ensure that there's an implementation of the InterfaceSpec trait
pub proof fn theorem()
    ensures implements_interface_spec::<PageTableImpl>(),
{
}

}
