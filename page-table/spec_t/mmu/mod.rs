//pub mod rl3;
pub mod rl4;
pub mod pt_mem;

use vstd::prelude::*;
use crate::spec_t::hardware::{ Core, PageDirectoryEntry };
use crate::definitions_t::{ PageTableEntry, Flags, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MemRegion };

verus! {

// partial(usize, Seq<PageDirectoryEntry>, Option<(Flags, PageTableEntry)>)
// ?
pub enum PTWalk {
    Partial {
        va: usize,
        path: Seq<(usize, PageDirectoryEntry)>,
    },
    Invalid {
        va: usize
    },
    Valid {
        va: usize,
        path: Seq<(usize, PageDirectoryEntry)>,
    },
}

pub struct CacheEntry {
    pub va: usize,
    pub path: Seq<(usize, PageDirectoryEntry)>,
}

impl PTWalk {
    pub open spec fn as_cache_entry(self) -> CacheEntry
        recommends self is Partial
    {
        match self {
            PTWalk::Partial { va, path } => CacheEntry { va, path },
            _ => arbitrary(),
        }
    }

    pub open spec fn path(self) -> Seq<(usize, PageDirectoryEntry)>
        recommends self is Partial || self is Valid
    {
        match self {
            PTWalk::Partial { path, .. } => path,
            PTWalk::Valid { path, .. }   => path,
            _                            => arbitrary(),
        }
    }

    pub open spec fn flags(self) -> Flags
        recommends
            self is Partial || self is Valid,
            0 < self.path().len() <= 3,
    {
        let flags0 = Flags::from_GPDE(self.path()[0].1@);
        let flags1 = flags0.combine(Flags::from_GPDE(self.path()[1].1@));
        let flags2 = flags1.combine(Flags::from_GPDE(self.path()[2].1@));
        let flags3 = flags2.combine(Flags::from_GPDE(self.path()[3].1@));
        if self.path().len() == 1 {
            flags0
        } else if self.path().len() == 2 {
            flags1
        } else if self.path().len() == 3 {
            flags2
        } else if self.path().len() == 4 {
            flags3
        } else { arbitrary() }
    }

    pub open spec fn prefixes(self) -> Set<PTWalk> {
        match self {
            PTWalk::Partial { va, path }    => {
                if path.len() == 1 {
                    set![self]
                } else if path.len() == 2 {
                    set![
                        PTWalk::Partial { va, path: seq![path[0]] },
                        self,
                    ]
                } else if path.len() == 3 {
                    set![
                        PTWalk::Partial { va, path: seq![path[0]] },
                        PTWalk::Partial { va, path: seq![path[0], path[1]] },
                        self,
                    ]
                } else { arbitrary() }
            },
            PTWalk::Invalid { va }          => set![self],
            PTWalk::Valid { va, path } => {
                if path.len() == 2 {
                    set![
                        PTWalk::Partial { va, path: seq![path[0]] },
                        self,
                    ]
                } else if path.len() == 3 {
                    set![
                        PTWalk::Partial { va, path: seq![path[0]] },
                        PTWalk::Partial { va, path: seq![path[0], path[1]] },
                        self,
                    ]
                } else if path.len() == 4 {
                    set![
                        PTWalk::Partial { va, path: seq![path[0]] },
                        PTWalk::Partial { va, path: seq![path[0], path[1]] },
                        PTWalk::Partial { va, path: seq![path[0], path[1], path[2]] },
                        self,
                    ]
                } else { arbitrary() }
            },
        }
    }

    pub open spec fn pte(self) -> PageTableEntry
        recommends self is Valid
    {
        let va = self->Valid_va as nat;
        let path = self->Valid_path;
        let size = if path.len() == 2 {
            L1_ENTRY_SIZE
        } else if path.len() == 3 {
            L2_ENTRY_SIZE
        } else if path.len() == 4 {
            L3_ENTRY_SIZE
        } else { arbitrary() } as nat;
        let base = (va - (va % size)) as nat;
        PageTableEntry {
            frame: MemRegion { base, size },
            flags: self.flags(),
        }
    }
}

impl CacheEntry {
    pub open spec fn as_ptwalk(self) -> PTWalk {
        PTWalk::Partial { va: self.va, path: self.path }
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
