#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::unreached;
use vstd::modes::*;
use vstd::seq::*;
use vstd::option::{*, Option::*};
use vstd::map::*;
use vstd::set::*;
use vstd::set_lib::*;
use vstd::vec::*;
use vstd::result::{*, Result::*};

use crate::definitions_t::{ Arch, ArchExec, MemRegion, MemRegionExec, overlap, between, aligned, new_seq, PageTableEntry };
use crate::definitions_t::{ WORD_SIZE, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS };
use crate::impl_u::l1;
use crate::impl_u::l0::{ambient_arith};
use crate::impl_u::indexing;

verus! {

pub fn word_index(addr: usize) -> (res: usize)
    requires
        aligned(addr as nat, 8),
    ensures
        res as nat === word_index_spec(addr as nat),
        // Prove this equivalence to use the indexing lemmas
        res as nat === indexing::index_from_offset(addr as nat, WORD_SIZE as nat),
        word_index_spec(addr as nat) === indexing::index_from_offset(addr as nat, WORD_SIZE as nat),
{
    addr / WORD_SIZE
}

pub open spec fn word_index_spec(addr: nat) -> nat
    recommends aligned(addr, 8)
{
    addr / (WORD_SIZE as nat)
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
            !self.view().dom().contains(vbase as nat),
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
    pub spec fn alloc_available_pages(self) -> nat;
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
            aligned(self.cr3_spec().base as nat, PAGE_SIZE as nat),
            self.cr3_spec().size == PAGE_SIZE;

    // We assume that alloc_page never fails. In practice we can just keep a buffer of 3+ pages
    // that are allocated before we use map_frame.
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> (r: MemRegionExec)
        requires
            old(self).inv(),
            0 < old(self).alloc_available_pages(),
        ensures
            self.alloc_available_pages() == old(self).alloc_available_pages() - 1,
            r@.size == PAGE_SIZE,
            r@.base + PAGE_SIZE <= MAXPHYADDR,
            aligned(r@.base, PAGE_SIZE as nat),
            !old(self).regions().contains(r@),
            self.regions() === old(self).regions().insert(r@),
            self.region_view(r@) === new_seq::<u64>(512nat, 0u64),
            forall|r2: MemRegion| r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.cr3_spec() == old(self).cr3_spec(),
            self.inv(),
    {
        unreached()
    }

    #[verifier(external_body)]
    /// Write value to physical address `pbase + idx * WORD_SIZE`
    pub fn write(&mut self, pbase: usize, idx: usize, region: Ghost<MemRegion>, value: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            old(self).inv(),
            old(self).regions().contains(region@),
            idx < 512,
        ensures
            self.region_view(region@) === old(self).region_view(region@).update(idx as int, value),
            forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
            self.regions() === old(self).regions(),
            old(self).alloc_available_pages() == self.alloc_available_pages(),
            self.cr3_spec() == old(self).cr3_spec(),
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).write(value); }
    }

    #[verifier(external_body)]
    /// Read value at physical address `pbase + idx * WORD_SIZE`
    pub fn read(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
        ensures
            res == self.spec_read(idx as nat, region@)
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).read() }
    }

    pub open spec fn spec_read(self, idx: nat, region: MemRegion) -> (res: u64) {
        self.region_view(region)[idx as int]
    }

    /// This function manually does the address computation which `read` and `write` rely on not
    /// overflowing. Since this function is not `external_body`, Verus checks that there's no
    /// overflow. The preconditions are those of `read`, which are a subset of the `write`
    /// preconditions.
    fn check_overflow(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
    {
        // FIXME: Make assumptions and then do the proof
        // pub const KERNEL_BASE: u64 = 0x4000_0000_0000;
        // (I think KERNEL_BASE is phys_mem_ref?)
        assume(false);
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        let phys_mem_ref: isize = self.phys_mem_ref_as_usize() as isize;
        // https://dev-doc.rust-lang.org/beta/std/primitive.pointer.html#method.offset
        // This needs to fit into an isize
        let raw_ptr_offset = phys_mem_ref + word_offset * (WORD_SIZE as isize);
    }

    #[verifier(external_body)]
    spec fn phys_mem_ref_as_usize_spec(&self) -> usize;

    #[verifier(external_body)]
    fn phys_mem_ref_as_usize(&self) -> (res: usize)
        ensures res == self.phys_mem_ref_as_usize_spec()
    {
        unsafe { self.phys_mem_ref as usize }
    }
}

}
