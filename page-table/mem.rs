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

use crate::aux_defs::{ Arch, ArchExec, MemRegion, MemRegionExec, overlap, between, aligned };
use crate::aux_defs::{ MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE, ENTRY_BYTES, PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS };
use crate::pt_impl::l1;
use crate::pt_impl::l0::{ambient_arith};

verus! {

/// A contiguous part of the memory
pub struct MemorySlice {
    base: u64,
    mem: Seq<nat>,
}

impl MemorySlice {
    /// Physical base address of the slice
    pub closed spec fn base(self) -> nat {
        self.base
    }

    /// Size of the slice in bytes
    pub closed spec fn size(self) -> nat {
        self.mem.len()
    }

    /// Returns true if the slice contains the memory of the given address
    pub closed spec fn contains_addr(self, addr: nat) -> bool {
        between(addr, self.base, self.size())
    }

    // pub closed spec fn base(self) -> usize {
    //     self.base as usize
    // }

    // pub closed spec fn base_u64(self) -> u64 {
    //     self.base as u64
    // }

    pub closed spec fn write(self, idx: nat, value: nat) -> MemorySlice {
        MemorySlice {
            base: self.base,
            mem:  self.mem.update(idx, value),
        }
    }

    pub closed spec fn overlap(self, other: MemorySlice) -> bool {
        if self.base <= other.base {
            other.base < self.base + self.size()
        } else {
            self.base < other.base + other.size()
        }
    }
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `ptr` is the starting address of the physical memory linear mapping
    ptr: *mut u64,
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

    pub closed spec fn slices(self) -> Set<MemorySlice>;

    pub open spec fn obtain_slice(self, base: nat, size: nat) -> MemorySlice
        recommends self.contains_slice(base, size)
    {
        if self.contains_slice(base, size) {
            choose|slice: MemorySlice| self.slices().contains(slice) && slice.base() == base && slice.size() == size
        } else {
            arbitrary()
        }
    }

    pub open spec fn contains_slice(self, base: nat, size: nat) -> bool {
        exists|slice: MemorySlice| self.slices().contains(slice) && slice.base() == base && slice.size() == size
    }

    pub open spec fn inv(self) -> bool {
        forall|s1: MemorySlice, s2: MemorySlice| s1 !== s2 ==> !s1.overlap(s2)
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
    pub fn alloc_page(&mut self) -> (res: (usize, MemorySlice))
        requires
            old(self).inv()
        ensures
            res.1.base() == res.0,
            res.1.size() == PAGE_SIZE,
            res.1.base() + PAGE_SIZE <= MAXPHYADDR,
            aligned(res.1.base(), PAGE_SIZE),
            self.slices() === old(self).slices().insert(res.1),
            self.inv()
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

    // TODO: Verus doesn't support mutable borrow args except self? just returning a new slice for
    // now
    #[verifier(external_body)]
    pub fn write(&mut self, slice: Ghost<MemorySlice>, offset: usize, value: u64) -> (new_slice: Ghost<MemorySlice>)
        requires
            old(self).inv(),
            aligned(offset, 8),
            old(self).slices().contains(slice@),
            slice@.contains_addr(offset),
            // word_index_spec(offset) < old(self)@.len(),
        ensures
            new_slice@ === slice@.write(word_index_spec(offset), value),
            self.inv(),
            // self@ === old(self)@.update(word_index_spec(offset), value)
    {
        unsafe { self.ptr.offset(offset as isize).write(value); }
        // FIXME: what's wrong with the code below?
        unreached()
        // let res: Ghost<MemorySlice> = ghost(slice@.write(word_index_spec(offset), value));
        // res
    }

    #[verifier(external_body)]
    pub fn read(&self, slice: Ghost<MemorySlice>, offset: usize) -> (res: u64)
        requires
            aligned(offset, 8),
            self.slices().contains(slice@),
            slice@.contains_addr(offset),
            // word_index_spec(offset) < self@.len(),
        ensures
            res == self.spec_read(slice@, offset)
    {
        unsafe { self.ptr.offset(word_index(offset) as isize).read() }
    }

    pub open spec fn spec_read(self, slice: MemorySlice, offset: nat) -> (res: u64);
}

}
