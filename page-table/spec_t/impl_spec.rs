#![allow(unused_imports)]
use crate::pervasive::*;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::mem_t as mem;
use crate::impl_u::l2_impl;

pub trait PTImpl {
    fn implspec_map_frame(&self, memory: mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (MapResult, mem::PageTableMemory);
    fn implspec_unmap(&self, memory: mem::PageTableMemory, base: usize) -> (UnmapResult, mem::PageTableMemory);
}
