#![allow(unused_imports)]
use crate::pervasive::option::{*, Option::*};
use crate::pervasive::vec::*;
use crate::mem_t as mem;

use crate::pervasive::result::{*, Result::*};

use crate::definitions_t::{ x86_arch_exec, WORD_SIZE, PAGE_SIZE, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE };
use crate::impl_u::l2_impl;
use crate::definitions_t::{ PageTableEntryExec, MapResult, UnmapResult };
use crate::spec_t::impl_spec;

pub struct PageTableImpl {}

impl impl_spec::PTImpl for PageTableImpl {
    fn implspec_map_frame(&self, memory: mem::PageTableMemory, base: usize, pte: PageTableEntryExec) -> (MapResult, mem::PageTableMemory) {
        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            arch:      x86_arch_exec(),
            ghost_pt:  (),
        };
        let res = page_table.map_frame(base, pte);
        (res, page_table.memory)
    }

    fn implspec_unmap(&self, memory: mem::PageTableMemory, base: usize) -> (UnmapResult, mem::PageTableMemory) {
        let mut page_table = l2_impl::PageTable {
            memory:    memory,
            arch:      x86_arch_exec(),
            ghost_pt:  (),
        };
        let res = page_table.unmap(base);
        (res, page_table.memory)
    }
}
