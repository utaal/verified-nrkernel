pub mod rl1;
pub mod rl2;
pub mod rl3;
pub mod rl4;
pub mod pt_mem;

use vstd::prelude::*;
use crate::spec_t::hardware::{ PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ PTE, Flags, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MemRegion, bitmask_inc, Core, align_to_usize };

verus! {

pub struct Walk {
    pub vbase: usize,
    pub path: Seq<(usize, GPDE)>,
    pub complete: bool,
}

pub enum WalkResult {
    Valid {
        vbase: usize,
        pte: PTE,
    },
    /// A `WalkResult::Invalid { .. }` indicates that the the range `[base..(base + size)]` has no
    /// existing valid translation (according to the result of a page table walk).
    Invalid {
        vbase: usize,
        size: usize,
    },
}

impl WalkResult {
    pub open spec fn vbase(self) -> usize {
        match self {
            WalkResult::Valid { vbase, .. } => vbase,
            WalkResult::Invalid { vbase, .. } => vbase,
        }
    }
}

impl Walk {
    // TODO: reconsider how this thing works in the step by step walks
    /// Also returns the address from which the value `value` must be read.
    pub open spec fn next(self, pml4: usize, value: usize) -> (Walk, usize) {
        let vbase = self.vbase; let path = self.path;
        // TODO: do this better
        let addr = if path.len() == 0 {
            add(pml4, l0_bits!(vbase as u64) as usize)
        } else if path.len() == 1 {
            add(path.last().0, l1_bits!(vbase as u64) as usize)
        } else if path.len() == 2 {
            add(path.last().0, l2_bits!(vbase as u64) as usize)
        } else if path.len() == 3 {
            add(path.last().0, l3_bits!(vbase as u64) as usize)
        } else { arbitrary() };

        let entry = PDE { entry: value as u64, layer: Ghost(path.len()) }@;
        let walk = Walk {
            vbase,
            path: path.push((addr, entry)),
            complete: !(entry is Directory)
        };
        (walk, addr)
    }

    //pub open spec fn valid(self, pt_mem: PTMem) -> bool {
    //    arbitrary() // basically the pt_walk_path
    //}

    pub open spec fn result(self) -> WalkResult {
        let path = self.path;
        if path.last().1 is Page {
            let (vbase, base, size) = if path.len() == 2 {
                (align_to_usize(self.vbase, L1_ENTRY_SIZE), path[1].1->Page_addr, L1_ENTRY_SIZE)
            } else if path.len() == 3 {
                (align_to_usize(self.vbase, L2_ENTRY_SIZE), path[2].1->Page_addr, L2_ENTRY_SIZE)
            } else if path.len() == 4 {
                (align_to_usize(self.vbase, L3_ENTRY_SIZE), path[3].1->Page_addr, L3_ENTRY_SIZE)
            } else { arbitrary() };
            WalkResult::Valid {
                vbase,
                pte: PTE {
                    frame: MemRegion { base: base as nat, size: size as nat },
                    flags: self.flags(),
                }
            }
        } else if path.last().1 is Empty {
            // FIXME: this is wrong, needs to be vaddr aligned to entry size
            let (vbase, size) = if path.len() == 1 {
                (align_to_usize(self.vbase, L1_ENTRY_SIZE), L1_ENTRY_SIZE)
            } else if path.len() == 2 {
                (align_to_usize(self.vbase, L2_ENTRY_SIZE), L2_ENTRY_SIZE)
            } else if path.len() == 3 {
                (align_to_usize(self.vbase, L3_ENTRY_SIZE), L3_ENTRY_SIZE)
            } else { arbitrary() };
            WalkResult::Invalid { vbase, size }
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

#[verifier(external_body)]
pub struct MemoryTypePlaceholder { }

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

} // verus!
