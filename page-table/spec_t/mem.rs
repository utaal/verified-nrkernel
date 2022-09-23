#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use modes::*;
use seq::*;
use option::{*, Option::*};
use map::*;
use set::*;
use set_lib::*;
use vec::*;

use result::{*, Result::*};

use crate::definitions_t::{ Arch, ArchExec, MemRegion, MemRegionExec, overlap, between, aligned, new_seq, PageTableEntry };
use crate::definitions_t::{ MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::impl_u::indexing;

verus! {

pub fn word_index(addr: usize) -> (res: usize)
    requires
        aligned(addr, 8),
    ensures
        res as nat === word_index_spec(addr),
        // Prove this equivalence to use the indexing lemmas
        res as nat === indexing::index_from_offset(addr, WORD_SIZE),
        word_index_spec(addr) === indexing::index_from_offset(addr, WORD_SIZE),
{
    addr / WORD_SIZE
}

pub open spec fn word_index_spec(addr: nat) -> nat
    recommends aligned(addr, 8)
{
    addr / WORD_SIZE
}

pub struct TLB {
}

impl TLB {
    pub spec fn view(self) -> Map<nat,PageTableEntry>;

    /// Invalidates any TLB entries containing `vbase`.
    #[verifier(external_body)]
    pub fn invalidate_entry(&mut self, vbase: usize)
        ensures
            forall|base, pte| self.view().contains_pair(base, pte) ==> old(self).view().contains_pair(base, pte),
            !self.view().dom().contains(vbase),
    {
        unreached()
    }
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `phys_mem_ref` is the starting address of the physical memory linear mapping
    phys_mem_ref: *mut u64,
}

impl PageTableMemory {
    pub spec fn regions(self) -> Set<MemRegion>;
    pub spec fn region_view(self, r: MemRegion) -> Seq<u64>;

    pub open spec fn inv(self) -> bool {
        &&& forall|s1: MemRegion, s2: MemRegion| self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(s1, s2)
    }

    /// `cr3` returns a MemRegion whose base is the address at which the layer 0 page directory is mapped
    #[verifier(external_body)]
    pub fn cr3(&self) -> (res: MemRegionExec)
        ensures res === self.cr3_spec()
    { unreached() }

    pub open spec fn cr3_spec(&self) -> MemRegionExec;

    #[verifier(external_body)]
    pub proof fn cr3_facts(&self)
        ensures
            aligned(self.cr3_spec().base, PAGE_SIZE),
            self.cr3_spec().size == PAGE_SIZE;

    // We assume that alloc_page never fails. In practice we can just keep a buffer of 3+ pages
    // that are allocated before we use map_frame.
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> (r: MemRegionExec)
        requires
            old(self).inv()
        ensures
            r@.size == PAGE_SIZE,
            r@.base + PAGE_SIZE <= MAXPHYADDR,
            aligned(r@.base, PAGE_SIZE),
            !old(self).regions().contains(r@),
            self.regions() === old(self).regions().insert(r@),
            self.region_view(r@) === new_seq::<u64>(512nat, 0u64),
            forall|r2: MemRegion| r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.inv()
    {
        unreached()
    }

    #[verifier(external_body)]
    pub fn write(&mut self, paddr: usize, region: Ghost<MemRegion>, value: u64)
        requires
            aligned(paddr, 8),
            old(self).inv(),
            old(self).regions().contains(region@),
            region@.contains(paddr),
            word_index_spec(sub(paddr, region@.base)) < 512,
        ensures
            self.region_view(region@) === old(self).region_view(region@).update(word_index_spec(sub(paddr, region@.base)), value),
            forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
            self.regions() === old(self).regions(),
    {
        let word_offset: isize = word_index(paddr) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).write(value); }
    }

    #[verifier(external_body)]
    pub fn read(&self, paddr: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            aligned(paddr, 8),
            self.regions().contains(region@),
            word_index_spec(sub(paddr, region@.base)) < 512,
        ensures
            res == self.spec_read(paddr, region@)
    {
        let word_offset: isize = word_index(paddr) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).read() }
    }

    pub open spec fn spec_read(self, paddr: nat, region: MemRegion) -> (res: u64) {
        self.region_view(region)[word_index_spec(sub(paddr, region.base))]
    }
}

}
