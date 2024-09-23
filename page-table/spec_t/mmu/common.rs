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
    Partial1(usize, PageDirectoryEntry, Flags),
    Partial2(usize, PageDirectoryEntry, PageDirectoryEntry, Flags),
    Partial3(usize, PageDirectoryEntry, PageDirectoryEntry, PageDirectoryEntry, Flags),
}

impl PTWalk {
    pub open spec fn as_cache_entry(self) -> CacheEntry
        recommends self is Partial1 || self is Partial2 || self is Partial3
    {
        match self {
            PTWalk::Partial1(va, l0e, flags)           => CacheEntry::Partial1(va, l0e, flags),
            PTWalk::Partial2(va, l0e, l1e, flags)      => CacheEntry::Partial2(va, l0e, l1e, flags),
            PTWalk::Partial3(va, l0e, l1e, l2e, flags) => CacheEntry::Partial3(va, l0e, l1e, l2e, flags),
            _                                          => arbitrary(),
        }
    }
}

impl CacheEntry {
    pub open spec fn as_ptwalk(self) -> PTWalk {
        match self {
            CacheEntry::Partial1(va, l0e, flags)           => PTWalk::Partial1(va, l0e, flags),
            CacheEntry::Partial2(va, l0e, l1e, flags)      => PTWalk::Partial2(va, l0e, l1e, flags),
            CacheEntry::Partial3(va, l0e, l1e, l2e, flags) => PTWalk::Partial3(va, l0e, l1e, l2e, flags),
        }
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

pub trait MMU: Sized {
    spec fn init(self) -> bool;
    spec fn next(pre: Self, post: Self, lbl: Lbl) -> bool;
    spec fn inv(self) -> bool;
    proof fn init_implies_inv(self)
        requires self.init()
        ensures self.inv()
    ;
    proof fn next_preserves_inv(pre: Self, post: Self, lbl: Lbl)
        requires
            pre.inv(),
            Self::next(pre, post, lbl)
        ensures post.inv()
    ;
}

}
