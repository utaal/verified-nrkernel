#![allow(unused_imports)]
use crate::pervasive::option::{*, Option::*};
use crate::pervasive::vec::*;

use crate::pervasive::result::{*, Result::*};

use crate::definitions_t::{ ArchExec, MemRegionExec };
use crate::definitions_t::{ WORD_SIZE, PAGE_SIZE };

pub fn word_index(offset: usize) -> usize
{
    offset / WORD_SIZE
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `ptr` is the starting address of the physical memory linear mapping
    ptr: *mut u64,
}

impl PageTableMemory {
    /// `cr3` returns the physical address at which the layer 0 page directory is mapped as well as
    /// the corresponding memory region
    #[verifier(external_body)]
    pub fn cr3(&self) -> ((), usize)
    {
        // FIXME:
        unimplemented!()
    }

    // We assume that alloc_page never fails. In practice we can just keep a buffer of 3+ pages
    // that are allocated before we use map_frame.
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> MemRegionExec
    {
        // FIXME:
        unimplemented!()
    }

    #[verifier(external_body)]
    pub fn write(&mut self, offset: usize, region: (), value: u64)
    {
        let word_offset: isize = word_index(offset) as isize;
        unsafe {
            self.ptr.offset(word_offset).write(value);
        }
    }

    #[verifier(external_body)]
    pub fn read(&self, offset: usize, region: ()) -> u64
    {
        let word_offset: isize = word_index(offset) as isize;
        unsafe {
            self.ptr.offset(word_offset).read()
        }
    }
}
