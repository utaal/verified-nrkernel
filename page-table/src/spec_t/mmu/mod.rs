pub mod rl1;
pub mod rl2;
pub mod rl3;
pub mod pt_mem;

use vstd::prelude::*;
use crate::spec_t::hardware::{ PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ PTE, Flags, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MemRegion, bitmask_inc, Core, align_to_usize, WORD_SIZE };

verus! {

pub struct Walk {
    pub vaddr: usize,
    pub path: Seq<(usize, GPDE)>,
    pub complete: bool,
}

pub enum WalkResult {
    Valid { vbase: usize, pte: PTE },
    /// A `WalkResult::Invalid` indicates that no valid translation exists for the given (8-aligned) vaddr
    Invalid { vaddr: usize },
}

impl WalkResult {
    pub open spec fn vaddr(self) -> usize {
        match self {
            WalkResult::Valid { vbase, .. } => vbase,
            WalkResult::Invalid { vaddr, .. } => vaddr,
        }
    }
}

impl Walk {
    pub open spec fn addr_for_idx(self, i: int, pml4: usize) -> usize
        recommends i < 4
    {
        let Walk { vaddr, path, .. } = self;
        if i == 0 {
            add(pml4, mul(l0_bits!(vaddr), WORD_SIZE))
        } else if i == 1 {
            add(path[0].1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
        } else if i == 2 {
            add(path[1].1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
        } else if i == 3 {
            add(path[2].1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
        } else {
            arbitrary()
        }
    }

    pub open spec fn result(self) -> WalkResult {
        let path = self.path;
        if path.last().1 is Page {
            let (vbase, base, size) = if path.len() == 2 {
                (align_to_usize(self.vaddr, L1_ENTRY_SIZE), path[1].1->Page_addr, L1_ENTRY_SIZE)
            } else if path.len() == 3 {
                (align_to_usize(self.vaddr, L2_ENTRY_SIZE), path[2].1->Page_addr, L2_ENTRY_SIZE)
            } else if path.len() == 4 {
                (align_to_usize(self.vaddr, L3_ENTRY_SIZE), path[3].1->Page_addr, L3_ENTRY_SIZE)
            } else { arbitrary() };
            WalkResult::Valid {
                vbase,
                pte: PTE {
                    frame: MemRegion { base: base as nat, size: size as nat },
                    flags: self.flags(),
                }
            }
        } else if path.last().1 is Empty {
            // The result holds for an 8-byte aligned address
            WalkResult::Invalid { vaddr: align_to_usize(self.vaddr, 8) }
        } else {
            arbitrary()
        }
    }

    pub open spec fn flags(self) -> Flags {
        let path = self.path;
        let flags0 = Flags::from_GPDE(path[0].1);
        let flags1 = flags0.combine(Flags::from_GPDE(path[1].1));
        let flags2 = flags1.combine(Flags::from_GPDE(path[2].1));
        let flags3 = flags2.combine(Flags::from_GPDE(path[3].1));
        if path.len() == 1 {
            flags0
        } else if path.len() == 2 {
            flags1
        } else if path.len() == 3 {
            flags2
        } else if path.len() == 4 {
            flags3
        } else { arbitrary() }
    }
}

pub struct Constants {
    pub cores: Set<Core>,
}

impl Constants {
    pub open spec fn valid_core(self, core: Core) -> bool {
        self.cores.contains(core)
    }
}

pub enum Lbl {
    /// Internal event
    Tau,
    /// Completion of a page table walk.
    /// Core, virtual address, walk result
    Walk(Core, WalkResult),
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

pub struct DummyAtomicMMU { }

impl MMU for DummyAtomicMMU {
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




// TODO: Should probably see if I can get rid of this. Only made triggering hard.
pub trait SeqTupExt: Sized {
    type A;
    spec fn contains_fst(self, fst: Self::A) -> bool;
}

impl<A,B> SeqTupExt for Seq<(A, B)> {
    type A = A;

    open spec fn contains_fst(self, fst: Self::A) -> bool {
        exists|i| 0 <= i < self.len() && #[trigger] self[i] == (fst, self[i].1)
    }
}

} // verus!
