#![allow(unused_imports)]
use crate::definitions_t::{MapResult, PageTableEntryExec, UnmapResult};
use crate::impl_u::l2_impl;
use crate::mem_t as mem;
use crate::pervasive::*;

pub trait PTImpl {
    fn implspec_map_frame(
        &self,
        memory: mem::PageTableMemory,
        base: usize,
        pte: PageTableEntryExec,
    ) -> (MapResult, mem::PageTableMemory);
    fn implspec_unmap(
        &self,
        memory: mem::PageTableMemory,
        base: usize,
    ) -> (UnmapResult, mem::PageTableMemory);
}
