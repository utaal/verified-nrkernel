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

// /// A contiguous part of the memory
// pub struct MemorySlice {
//     base: usize,
//     mem: Seq<nat>,
// }

// impl MemorySlice {
//     /// Physical base address of the slice
//     pub closed spec fn base(self) -> nat {
//         self.base
//     }

//     /// Size of the slice in bytes
//     pub closed spec fn size(self) -> nat {
//         self.mem.len()
//     }

//     /// Check if this slice corresponds to the same memory region as `r`
//     pub open spec fn equals_region(self, r: MemRegion) -> bool {
//         &&& self.base() == r.base
//         &&& self.size() == r.size
//     }

//     /// Returns true if the slice contains the memory of the given address
//     pub closed spec fn contains_addr(self, addr: nat) -> bool {
//         between(addr, self.base, self.size())
//     }

//     pub closed spec fn write(self, idx: nat, value: nat) -> MemorySlice {
//         MemorySlice {
//             base: self.base,
//             mem:  self.mem.update(idx, value),
//         }
//     }

//     pub closed spec fn overlap(self, other: MemorySlice) -> bool {
//         if self.base <= other.base {
//             other.base < self.base + self.size()
//         } else {
//             self.base < other.base + other.size()
//         }
//     }
// }

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `ptr` is the starting address of the physical memory linear mapping
    ptr: *mut u64,
    // owned: Set<MemorySlice>,
    // domain: Set<MemRegion>,
}

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

impl PageTableMemory {
    // pub open spec fn view(&self) -> Seq<nat>;

    pub closed spec fn owned(self) -> Set<MemRegion>;
    pub closed spec fn domain(self) -> Set<MemRegion>;

    // pub open spec fn obtain_slice(self, base: nat, size: nat) -> MemorySlice
    //     recommends self.contains_slice(base, size)
    // {
    //     if self.contains_slice(base, size) {
    //         choose|slice: MemorySlice| #[trigger] self.slices().contains(slice) && slice.base() == base && slice.size() == size
    //     } else {
    //         arbitrary()
    //     }
    // }

    // pub open spec fn contains_slice(self, base: nat, size: nat) -> bool {
    //     exists|slice: MemorySlice| #[trigger] self.slices().contains(slice) && slice.base() == base && slice.size() == size
    // }

    pub open spec fn inv(self) -> bool {
        &&& true // owned is subset of domain
        &&& forall|s1: MemRegion, s2: MemRegion| self.domain().contains(s1) && self.domain().contains(s2) && s1 !== s2 ==> !overlap(s1, s2)
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
    // FIXME: need to ensure we use disjoint memory when allocating a page. Can we somehow use
    // linearity for that?
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> (r: MemRegionExec)
        requires
            old(self).inv()
        ensures
            r@.size == PAGE_SIZE,
            r@.base + PAGE_SIZE <= MAXPHYADDR,
            aligned(r@.base, PAGE_SIZE),
            self.domain() === old(self).domain().insert(r@),
            self.owned()  === old(self).owned().insert(r@),
            forall|offset| r@.contains(offset) ==> #[trigger] self.spec_read(offset, r@) == 0,
            forall|offset, r2| r2 !== r@ && r2.contains(offset) ==> #[trigger] self.spec_read(offset, r2) == old(self).spec_read(offset, r2),
            self.inv() // TODO: derivable
        // ensures
        //     offset <= MAXPHYADDR,
        //     aligned(offset, PAGE_SIZE),
        //     forall_arith(|i: nat| i < 512nat ==> word_index_spec((offset + #[trigger] (i * 8)) as nat) < self@.len()),
        //     forall_arith(|i: nat| i < 512nat ==> self.spec_read((offset + #[trigger] (i * 8)) as nat) == 0),
        //     // TODO: should probably introduce some function for the indexing and trigger on that
        //     // forall|i: nat| i < 512nat ==> word_index_spec((offset + i * ENTRY_BYTES) as nat) < self@.len(),
        //     // forall|i: nat| i < 512nat ==> self.spec_read((offset + i * ENTRY_BYTES) as nat) == 0
    {
        // FIXME:
        unreached()
    }

    #[verifier(external_body)]
    pub fn write(&mut self, offset: usize, region: Ghost<MemRegion>, value: u64)
        requires
            old(self).inv(),
            aligned(offset, 8),
            old(self).owned().contains(region@),
            region@.contains(offset),
            // word_index_spec(offset) < old(self)@.len(),
        ensures
            self.spec_read(offset, region@) == value,
            forall|x| x != offset ==> self.spec_read(x, region@) == old(self).spec_read(x, region@),
            self.inv(), // TODO: derivable
            // self@ === old(self)@.update(word_index_spec(offset), value)
    {
        unsafe { self.ptr.offset(offset as isize).write(value); }
        // FIXME: what's wrong with the code below?
        unreached()
        // let res: Ghost<MemorySlice> = ghost(slice@.write(word_index_spec(offset), value));
        // res
    }

    #[verifier(external_body)]
    pub fn read(&self, offset: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            aligned(offset, 8),
            self.owned().contains(region@),
            region@.contains(offset),
            // word_index_spec(offset) < self@.len(),
        ensures
            res == self.spec_read(offset, region@)
    {
        unsafe { self.ptr.offset(word_index(offset) as isize).read() }
    }

    pub open spec fn spec_read(self, offset: nat, region: MemRegion) -> (res: u64);

    // FIXME: how do i make this use tracked? Need to ensure the args are consumed in union and split
    pub spec fn union(mems: Seq<PageTableMemory>) -> PageTableMemory;

    #[verifier(external_body)]
    pub proof fn axiom_union(mems: Seq<PageTableMemory>)
        requires
            // Each memory satisfies the invariant:
            forall|i: nat| i < mems.len() ==> #[trigger] mems[i].inv(),
            // Any two memories may not have overlapping regions in their respective domains, unless the regions are equal:
            forall|i: nat, j: nat, r1: MemRegion, r2: MemRegion|
                i !== j && i < mems.len() && j < mems.len() && #[trigger] mems[i].domain().contains(r1) && #[trigger] mems[j].domain().contains(r2) && r1 !== r2 ==> !overlap(r1, r2),
            // If one memory owns a region, no other memory may own that same region:
            forall|i: nat, j: nat, r: MemRegion|
                i !== j && i < mems.len() && j < mems.len() && #[trigger] mems[i].owned().contains(r) ==> !(#[trigger] mems[j].owned().contains(r)),
        ensures
            // The union's domain is the union of the memories' domains:
            forall|i: nat, r: MemRegion|
                i < mems.len() && mems[i].domain().contains(r) ==> Self::union(mems).domain().contains(r),
            forall|r: MemRegion|
                Self::union(mems).domain().contains(r) ==> exists|i: nat| i < mems.len() ==> #[trigger] mems[i].domain().contains(r),
            // The union's owned regions are the union of the memories' owned regions:
            forall|i: nat, r: MemRegion|
                i < mems.len() && mems[i].owned().contains(r)  ==> Self::union(mems).owned().contains(r),
            forall|r: MemRegion|
                Self::union(mems).owned().contains(r)  ==> exists|i: nat| i < mems.len() ==> #[trigger] mems[i].owned().contains(r),
            // The memory locations still have the same values
            forall|i: nat, r: MemRegion, offset: nat|
                i < mems.len() && mems[i].owned().contains(r) && r.contains(offset) ==> Self::union(mems).spec_read(offset, r) == mems[i].spec_read(offset, r);

    pub spec fn split(self, mems: Seq<(Set<MemRegion>, Set<MemRegion>)>) -> Seq<PageTableMemory>;

    #[verifier(external_body)]
    pub proof fn axiom_split(self, mems: Seq<(Set<MemRegion>, Set<MemRegion>)>)
        requires
            self.inv(),
            // bunch of preconditions
        ensures
            // Each memory satisfies the invariant:
            forall|i: nat| i < mems.len() ==> #[trigger] self.split(mems)[i].inv();
            // bunch of postconditions
}

}
