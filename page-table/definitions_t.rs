#![allow(unused_imports)]
use core::clone::Clone;

use crate::pervasive::option::{*, Option::*};
use crate::pervasive::vec::*;
use crate::pervasive::result::{*, Result::*};

// Upper bound for x86 4-level paging.
// 512 entries, each mapping 512*1024*1024*1024 bytes
pub const PT_BOUND_HIGH: usize = 512 * 512 * 1024 * 1024 * 1024;
pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;
pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;
pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;
pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub fn aligned_exec(addr: usize, size: usize) -> bool
{
    addr % size == 0
}

pub enum MapResult {
    ErrOverlap,
    Ok,
}

pub enum UnmapResult {
    ErrNoSuchMapping,
    Ok,
}

pub enum ResolveResult {
    ErrUnmapped,
    PAddr(usize),
}

pub struct MemRegionExec { pub base: usize, pub size: usize }

impl MemRegionExec {
}

pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

pub struct PageTableEntryExec {
    pub frame: MemRegionExec,
    pub flags: Flags,
}

impl PageTableEntryExec {
}

// Architecture

// page_size, next_sizes
// 2**40    , [ 2 ** 30, 2 ** 20 ]
// 2**30    , [ 2 ** 20 ]
// 2**20    , [ ]

// [es0 # es1 , es2 , es3 ] // entry_size
// [1T  # 1G  , 1M  , 1K  ] // pages mapped at this level are this size <--

// [n0  # n1  , n2  , n3  ] // number_of_entries
// [1   # 1024, 1024, 1024]

// es1 == es0 / n1 -- n1 * es1 == es0
// es2 == es1 / n2 -- n2 * es2 == es1
// es3 == es2 / n3 -- n3 * es3 == es2

// [es0  #  es1 , es2 , es3 , es4 ] // entry_size
// [256T #  512G, 1G  , 2M  , 4K  ]
// [n0   #  n1  , n2  , n3  , n4  ] // number_of_entries
// [     #  512 , 512 , 512 , 512 ]
// [     #  9   , 9   , 9   , 9   , 12  ]

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

impl Clone for ArchLayerExec {
    fn clone(&self) -> Self {
        ArchLayerExec {
            entry_size: self.entry_size,
            num_entries: self.num_entries,
        }
    }
}

impl ArchLayerExec {
}

pub struct ArchExec {
    // TODO: This could probably be an array, once we have support for that
    pub layers: Vec<ArchLayerExec>,
}

impl ArchExec {
    pub fn entry_size(&self, layer: usize) -> usize
    {
        self.layers.index(layer).entry_size
    }

    pub fn num_entries(&self, layer: usize) -> usize
    {
        self.layers.index(layer).num_entries
    }

    pub fn index_for_vaddr(&self, layer: usize, base: usize, vaddr: usize) -> usize
    {
        let es = self.entry_size(layer);
        let offset = vaddr - base;
        let res = offset / es;
        res
    }

    pub fn entry_base(&self, layer: usize, base: usize, idx: usize) -> usize
    {
        base + idx * self.entry_size(layer)
    }

    pub fn next_entry_base(&self, layer: usize, base: usize, idx: usize) -> usize
    {
        let offset = (idx + 1) * self.entry_size(layer);
        base + offset
    }
}

pub const MAXPHYADDR_BITS: u64 = 52;
// FIXME: is this correct?
// spec const MAXPHYADDR: nat      = ((1u64 << 52u64) - 1u64) as nat;
// TODO: Probably easier to use computed constant because verus can't deal with the shift except in
// bitvector assertions.
pub const WORD_SIZE: usize = 8;
pub const PAGE_SIZE: usize = 4096;

// FIXME: can we get rid of this somehow?
pub fn x86_arch_exec() -> ArchExec
{
    ArchExec {
        layers: Vec { vec: alloc::vec![
            ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 },
        ] },
    }
}
