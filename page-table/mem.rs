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
use crate::lib_axiom::*;

use result::{*, Result::*};

use crate::aux_defs::{ Arch, ArchExec, MemRegion, MemRegionExec, overlap, between, aligned, new_seq };
use crate::aux_defs::{ MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, ENTRY_BYTES, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS };
use crate::pt_impl::l1;
use crate::pt_impl::l0::{ambient_arith};

verus! {

/// We view the memory as a sequence of u64s but have to use byte offsets in the page table
/// entries. This function converts a word-aligned byte offset to a word index.
pub fn word_index(idx: usize) -> (res: usize)
    requires
        aligned(idx, 8),
    ensures
        res == word_index_spec(idx)
{
    idx / 8
}

pub open spec fn word_index_spec(idx: nat) -> nat
    recommends aligned(idx, 8)
{
    if aligned(idx, 8) {
        idx / 8
    } else {
        arbitrary()
    }
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `ptr` is the starting address of the physical memory linear mapping
    ptr: *mut u64,
}

impl PageTableMemory {
    // pub open spec fn view(&self) -> Seq<nat>;

    pub spec fn regions(self) -> Set<MemRegion>;

    pub open spec fn inv(self) -> bool {
        &&& forall|s1: MemRegion, s2: MemRegion| self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(s1, s2)
    }

    /// `cr3` returns the physical address at which the layer 0 page directory is mapped
    #[verifier(external_body)]
    pub fn cr3(&self) -> (res: usize)
        ensures
            res == self.cr3_spec()
    {
        // FIXME:
        unreached()
    }

    pub open spec fn cr3_spec(&self) -> usize;

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
            forall|offset| r@.contains(offset) ==> #[trigger] self.spec_read(offset, r@) == 0,
            forall|offset, r2| r2 !== r@ && r2.contains(offset) ==> #[trigger] self.spec_read(offset, r2) == old(self).spec_read(offset, r2),
            self.inv() // TODO: derivable
    {
        // FIXME:
        unreached()
    }

    #[verifier(external_body)]
    pub fn write(&mut self, offset: usize, region: Ghost<MemRegion>, value: u64)
        requires
            aligned(offset, 8),
            old(self).inv(),
            old(self).regions().contains(region@),
            region@.contains(offset),
            // word_index_spec(offset) < old(self)@.len(),
        ensures
            self.spec_read(offset, region@) == value,
            forall|offset2: nat| offset2 != offset ==> self.spec_read(offset2, region@) == old(self).spec_read(offset2, region@),
            forall|offset2: nat, r: MemRegion| r !== region@ ==> self.spec_read(offset2, r) == old(self).spec_read(offset2, r),
            self.inv(), // TODO: derivable
    {
        unsafe { self.ptr.offset(offset as isize).write(value); }
        unreached()
    }

    #[verifier(external_body)]
    pub fn read(&self, offset: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            aligned(offset, 8),
            self.regions().contains(region@),
            region@.contains(offset),
            // word_index_spec(offset) < self@.len(),
        ensures
            res == self.spec_read(offset, region@)
    {
        unsafe { self.ptr.offset(word_index(offset) as isize).read() }
    }

    pub open spec fn spec_read(self, offset: nat, region: MemRegion) -> (res: u64);
}

}
