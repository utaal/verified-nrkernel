//pub mod rl3;
pub mod rl4;
pub mod pt_mem;

use vstd::prelude::*;
use crate::spec_t::hardware::{ Core, PageDirectoryEntry };
use crate::definitions_t::{ PageTableEntry, Flags };

verus! {

// partial(usize, Seq<PageDirectoryEntry>, Option<(Flags, PageTableEntry)>)
// ?
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

#[verifier(external_body)]
pub struct MemoryTypePlaceholder { }

pub trait MMU: Sized {
    /// `mem_view` is necessary to express some of the transitions in the OS state machine. Need to
    /// decide on the exact type for this. (PML4 + Map<usize,usize> ?)
    /// TODO: Maybe this doesn't need to be part of the MMU trait, can probably track this as
    /// separate ghost state in the OS state machine.
    spec fn mem_view(self) -> MemoryTypePlaceholder; // Map<usize,usize>;
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

pub struct DummyAtomicMMU { }

impl MMU for DummyAtomicMMU {
    spec fn mem_view(self) -> MemoryTypePlaceholder; // Map<usize,usize>;
    spec fn init(self) -> bool;
    spec fn next(pre: Self, post: Self, lbl: Lbl) -> bool;
    spec fn inv(self) -> bool;
    proof fn init_implies_inv(self) {
        admit();
    }
    proof fn next_preserves_inv(pre: Self, post: Self, lbl: Lbl) {
        admit();
    }
}

} // verus!
