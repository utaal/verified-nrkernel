#![verus::trusted]
// trusted:
// these are the interface specifications, they are part of the theorem

use vstd::prelude::*;
use crate::definitions_t::{ PageTableEntryExec };
use crate::impl_u::spec_pt;
use crate::spec_t::mem;
use crate::extra::result_map_ok;

verus! {

pub open spec fn pt_vars(mem: mem::PageTableMemory) -> spec_pt::PageTableVariables {
    spec_pt::PageTableVariables { pt_mem: mem }
}

pub trait InterfaceSpec {
    spec fn ispec_inv(&self, mem: &mem::PageTableMemory) -> bool;

    proof fn ispec_init_implies_inv(&self, mem: &mem::PageTableMemory)
        requires spec_pt::init(pt_vars(*mem))
        ensures self.ispec_inv(mem);

    fn ispec_map_frame(&self, mem: &mut mem::PageTableMemory, vaddr: usize, pte: PageTableEntryExec) -> (res: Result<(),()>)
        requires
            spec_pt::step_Map_enabled(pt_vars(*old(mem)), vaddr as nat, pte@),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Map(pt_vars(*old(mem)), pt_vars(*mem), vaddr as nat, pte@, res);

    fn ispec_unmap(&self, mem: &mut mem::PageTableMemory, vaddr: usize) -> (res: Result<(),()>)
        requires
            spec_pt::step_Unmap_enabled(vaddr as nat),
            self.ispec_inv(&*old(mem)),
        ensures
            self.ispec_inv(mem),
            spec_pt::step_Unmap(pt_vars(*old(mem)), pt_vars(*mem), vaddr as nat, res);

    fn ispec_resolve(&self, mem: &mem::PageTableMemory, vaddr: usize) -> (res: Result<(usize,PageTableEntryExec),()>)
        requires
            spec_pt::step_Resolve_enabled(vaddr as nat),
            self.ispec_inv(mem),
        ensures
            spec_pt::step_Resolve(
                pt_vars(*mem),
                pt_vars(*mem),
                vaddr as nat,
                result_map_ok(res, |t: (usize, PageTableEntryExec)| (t.0 as nat, t.1@))
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
