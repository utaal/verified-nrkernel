//pub mod rl1;
//pub mod rl2;
//pub mod rl3;
pub mod rl4;
pub mod pt_mem;

use vstd::prelude::*;
use crate::spec_t::hardware::{ PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits };
use crate::definitions_t::{ PTE, Flags, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MemRegion, bitmask_inc, Core, align_to_usize, aligned };

verus! {

pub struct Walk {
    pub vbase: usize,
    pub path: Seq<(usize, GPDE)>,
    pub complete: bool,
}

pub enum WalkResult {
    Valid { vbase: usize, pte: PTE },
    /// A `WalkResult::Invalid` indicates that no valid translation exists for the 4k range
    /// starting at the (4k-aligned) address of the ptwalk.
    Invalid { vbase: usize },
}

//impl WalkResult {
//    pub open spec fn vbase(self) -> usize {
//        match self {
//            WalkResult::Valid { vbase, .. } => vbase,
//            WalkResult::Invalid { vbase, .. } => vbase,
//        }
//    }
//}

impl Walk {

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
            // This vbase is always 4k-aligned
            WalkResult::Invalid { vbase: self.vbase }
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

//pub open spec fn is_l0_entry(pt_mem: pt_mem::PTMem, addr: usize) -> bool {
//    pt_mem.pml4() <= addr < pt_mem.pml4() + 4096
//}


pub open spec fn pt_walk(pt_mem: pt_mem::PTMem, vbase: usize, path: Seq<(usize, GPDE)>) -> bool {
    let l0_idx = l0_bits!(vbase as u64) as usize;
    let l1_idx = l1_bits!(vbase as u64) as usize;
    let l2_idx = l2_bits!(vbase as u64) as usize;
    let l3_idx = l3_bits!(vbase as u64) as usize;
    let l0_addr = add(pt_mem.pml4, l0_idx);
    let l0e = PDE { entry: pt_mem.read(l0_addr) as u64, layer: Ghost(0) };
    match l0e@ {
        GPDE::Directory { addr: l1_daddr, .. } => {
            let l1_addr = add(l1_daddr, l1_idx);
            let l1e = PDE { entry: pt_mem.read(l1_addr) as u64, layer: Ghost(1) };
            match l1e@ {
                GPDE::Directory { addr: l2_daddr, .. } => {
                    let l2_addr = add(l2_daddr, l2_idx);
                    let l2e = PDE { entry: pt_mem.read(l2_addr) as u64, layer: Ghost(2) };
                    match l2e@ {
                        GPDE::Directory { addr: l3_daddr, .. } => {
                            let l3_addr = add(l3_daddr, l3_idx);
                            let l3e = PDE { entry: pt_mem.read(l3_addr) as u64, layer: Ghost(3) };
                            &&& aligned(vbase as nat, L3_ENTRY_SIZE as nat)
                            &&& path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)]
                        },
                        _ => {
                            &&& aligned(vbase as nat, L2_ENTRY_SIZE as nat)
                            &&& path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)]
                        },
                    }
                },
                _ => {
                    &&& aligned(vbase as nat, L1_ENTRY_SIZE as nat)
                    &&& path == seq![(l0_addr, l0e@), (l1_addr, l1e@)]
                },
            }
        },
        _ => {
            &&& aligned(vbase as nat, L0_ENTRY_SIZE as nat)
            &&& path == seq![(l0_addr, l0e@)]
        },
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

} // verus!
