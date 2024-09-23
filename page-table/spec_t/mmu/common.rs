use vstd::prelude::*;

use crate::spec_t::hardware::{ Core, PageDirectoryEntry };
use crate::definitions_t::{ PageTableEntry, Flags };

verus! {

pub enum PTWalk {
    Partial1(usize, PageDirectoryEntry, Flags),
    Partial2(usize, PageDirectoryEntry, PageDirectoryEntry, Flags),
    Partial3(usize, PageDirectoryEntry, PageDirectoryEntry, PageDirectoryEntry, Flags),
    Invalid(usize),
    Valid(usize, PageTableEntry),
}

pub enum CacheEntry {
    Partial1(usize, usize), // TODO
    Partial2(usize, usize), // TODO
    Partial3(usize, usize), // TODO
}

impl PTWalk {
    pub open spec fn as_cache_entry(self) -> CacheEntry {
        arbitrary() // TODO:
    }
}

impl CacheEntry {
    pub open spec fn as_ptwalk(self) -> PTWalk {
        arbitrary() // TODO:
    }
}

pub enum Lbl {
    /// Internal event
    Tau,
    /// Completion of a page table walk.
    /// Core, virtual address, Some(pte) if valid, None if invalid
    Walk(Core, usize, Option<PageTableEntry>),
    /// Write to physical memory.
    /// Core, physical address, written value
    Write(Core, usize, usize),
    /// Read from physical memory.
    /// Core, physical address, read value
    Read(Core, usize, usize),
    /// Invlpg instruction
    /// Core and virtual address
    Invlpg(Core, usize),
    /// Serializing instruction
    Barrier(Core),
}

}
