use vstd::prelude::*;

use crate::spec_t::hardware::{ PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits };
//use crate::definitions_t::{ PTE, L0_ENTRY_SIZE, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, bitmask_inc, aligned };
use crate::definitions_t::{ PTE, bitmask_inc };
use crate::spec_t::mmu::{ Walk, WalkResult, SeqTupExt };

//use crate::definitions_t::{
//    aligned, WORD_SIZE,
//};

verus! {

// TODO: memory size
pub struct PTMem {
    pub mem: Map<usize, usize>,
    //pub types: Map<usize, MType>,
    pub pml4: usize,
}

impl PTMem {
    pub open spec fn write(self, addr: usize, value: usize) -> PTMem {
        PTMem {
            mem: self.mem.insert(addr, value),
            //types: self.types,
            pml4: self.pml4,
        }
    }

    pub open spec fn read(self, addr: usize) -> usize {
        self.mem[addr]
    }

    //pub open spec fn retype(self, m: Map<usize, MType>) -> PTMem {
    //    PTMem {
    //        mem: self.mem,
    //        types: self.types.union_prefer_right(m),
    //        pml4: self.pml4,
    //    }
    //}

    ///// Set of currently valid (complete) walks in the page table (including those ending in invalid entries)
    //pub open spec fn all_pt_walks(self) -> Set<Walk> {
    //    Set::new(|e| pt_walk_pred(self, e))
    //}

    ///// This address is only used in one location in the page table.
    ///// TODO: this should be part of the invariant. What's the condition i need on writes?
    //pub open spec fn is_single_location(self, addr: usize) -> bool {
    //    forall|walk1, walk2, i, j| #![auto]
    //        self.all_pt_walks().contains(walk1)
    //        && self.all_pt_walks().contains(walk2)
    //        && 0 <= i < walk1.path.len()
    //        && 0 <= j < walk2.path.len()
    //        && walk1.path[i].0 == walk2.path[j].0
    //        ==> walk2 == walk1
    //}

    /// Sequentially apply a sequence of writes. (Used to apply a whole store buffer.)
    pub open spec fn write_seq(self, writes: Seq<(usize, usize)>) -> Self {
        writes.fold_left(self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1))
    }

    // Using present bits doesn't work because mb0 bits can still make it invalid and those are
    // different depending on the entry
    //pub open spec fn is_pos_or_neg_write(self, addr: usize, value: usize) -> bool {
    //    if self.read(addr) & 1 == 1 {
    //        value & 1 == 0
    //    } else {
    //        value & 1 == 1
    //    }
    //}

    ///// A present bit of 1 doesn't guarantee that this is a valid entry. It may not be reachable
    ///// from PML4 or it may have must-be-zero flags set (which depends on what layer the entry is
    ///// reachable at).
    //pub open spec fn maybe_neg_write(self, addr: usize) -> bool {
    //    self.read(addr) & 1 != 0
    //}

    /// A present bit of 0 guarantees that this is not currently a valid entry.
    /// I.e. this write can be:
    /// - Invalid -> Valid
    /// - Invalid -> Invalid
    ///
    /// The second conjunct guarantees that we write at most once to each address.
    // ///
    // /// I also require that the written value has P=1. This doesn't guarantee the result is a valid
    // /// entry (might be unreachable or have mb0 bits set) but it guarantees... what? only one write
    // /// per addr i guess
    pub open spec fn is_nonneg_write(self, addr: usize, value: usize) -> bool {
        &&& self.read(addr) & 1 == 0
        &&& value & 1 == 1
    }

    /// Writing a present bit of 0 guarantees that this doesn't become a valid entry.
    /// I.e. this write can be:
    /// - Valid -> Invalid
    /// - Invalid -> Invalid
    pub open spec fn is_nonpos_write(self, _addr: usize, value: usize) -> bool {
        //&&& self.read(addr) & 1 == 1
        &&& value & 1 == 0
    }

    ///// Is this a negative write? I.e. is it to a location that currently represents a page mapping
    ///// anywhere in the page table?
    //pub open spec fn is_neg_write(self, addr: usize) -> bool {
    //    forall|walk| #![auto]
    //        self.all_pt_walks().contains(walk) && walk.path.last().0 == addr
    //        ==> walk.path.last().1 is Page
    //}
    //
    ///// Is this a positive write? I.e. is it to a location that currently represents a reachable
    ///// but invalid location in the page table and changes it to a page mapping?
    ///// TODO: do i need to know that this actually becomes a valid entry or is it sufficient to
    ///// know that it was previously invalid?
    //pub open spec fn is_nonneg_write(self, addr: usize) -> bool {
    //    forall|walk| #![auto]
    //        self.all_pt_walks().contains(walk) && walk.path.last().0 == addr
    //        ==> walk.path.last().1 is Empty
    //}

    pub open spec fn pt_walk(self, vaddr: usize) -> Walk {
        let l0_idx = l0_bits!(vaddr as u64) as usize;
        let l1_idx = l1_bits!(vaddr as u64) as usize;
        let l2_idx = l2_bits!(vaddr as u64) as usize;
        let l3_idx = l3_bits!(vaddr as u64) as usize;
        let l0_addr = add(self.pml4, l0_idx);
        let l0e = PDE { entry: self.read(l0_addr) as u64, layer: Ghost(0) };
        match l0e@ {
            GPDE::Directory { addr: l1_daddr, .. } => {
                let l1_addr = add(l1_daddr, l1_idx);
                let l1e = PDE { entry: self.read(l1_addr) as u64, layer: Ghost(1) };
                match l1e@ {
                    GPDE::Directory { addr: l2_daddr, .. } => {
                        let l2_addr = add(l2_daddr, l2_idx);
                        let l2e = PDE { entry: self.read(l2_addr) as u64, layer: Ghost(2) };
                        match l2e@ {
                            GPDE::Directory { addr: l3_daddr, .. } => {
                                let l3_addr = add(l3_daddr, l3_idx);
                                let l3e = PDE { entry: self.read(l3_addr) as u64, layer: Ghost(3) };
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)],
                                    complete: true,
                                }
                            },
                            _ => {
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)],
                                    complete: true,
                                }
                            },
                        }
                    },
                    _ => {
                        Walk { vaddr, path: seq![(l0_addr, l0e@), (l1_addr, l1e@)], complete: true }
                    },
                }
            },
            _ => {
                Walk { vaddr, path: seq![(l0_addr, l0e@)], complete: true }
            },
        }
    }

    pub open spec fn is_base_pt_walk(self, vaddr: usize) -> bool {
        &&& self.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }
        &&& vbase == vaddr
    }

    pub open spec fn view(self) -> Map<usize,PTE> {
        Map::new(
            |va| self.is_base_pt_walk(va),
            |va| self.pt_walk(va).result()->pte
        )
    }

    pub broadcast proof fn lemma_write_seq_idle(self, writes: Seq<(usize, usize)>, addr: usize)
        requires
            self.mem.contains_key(addr),
            !writes.contains_addr(addr),
        ensures #[trigger] self.write_seq(writes).read(addr) == self.read(addr)
    {
        admit();
    }
}

///// Only complete page table walks
//pub open spec fn pt_walk_pred(pt_mem: PTMem, walk: Walk) -> bool {
//    let vaddr = walk.vaddr;
//    let l0_idx = l0_bits!(vaddr as u64) as usize;
//    let l1_idx = l1_bits!(vaddr as u64) as usize;
//    let l2_idx = l2_bits!(vaddr as u64) as usize;
//    let l3_idx = l3_bits!(vaddr as u64) as usize;
//    let l0_addr = add(pt_mem.pml4, l0_idx);
//    let l0e = PDE { entry: pt_mem.read(l0_addr) as u64, layer: Ghost(0) };
//    &&& walk.complete
//    &&& match l0e@ {
//        GPDE::Directory { addr: l1_daddr, .. } => {
//            let l1_addr = add(l1_daddr, l1_idx);
//            let l1e = PDE { entry: pt_mem.read(l1_addr) as u64, layer: Ghost(1) };
//            &&& match l1e@ {
//                GPDE::Directory { addr: l2_daddr, .. } => {
//                    let l2_addr = add(l2_daddr, l2_idx);
//                    let l2e = PDE { entry: pt_mem.read(l2_addr) as u64, layer: Ghost(2) };
//                    &&& match l2e@ {
//                        GPDE::Directory { addr: l3_daddr, .. } => {
//                            let l3_addr = add(l3_daddr, l3_idx);
//                            let l3e = PDE { entry: pt_mem.read(l3_addr) as u64, layer: Ghost(3) };
//                            &&& aligned(vaddr as nat, L3_ENTRY_SIZE as nat)
//                            &&& walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)]
//                        },
//                        _ => {
//                            &&& aligned(vaddr as nat, L2_ENTRY_SIZE as nat)
//                            &&& walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)]
//                        },
//                    }
//                },
//                _ => {
//                    &&& aligned(vaddr as nat, L1_ENTRY_SIZE as nat)
//                    &&& walk.path == seq![(l0_addr, l0e@), (l1_addr, l1e@)]
//                },
//            }
//        },
//        _ => {
//            &&& aligned(vaddr as nat, L0_ENTRY_SIZE as nat)
//            &&& walk.path == seq![(l0_addr, l0e@)]
//        },
//    }
//}


//pub open spec fn pt_walk_path_size(path: Seq<(usize, GPDE)>) -> usize {
//    if path.len() == 1 {
//        L0_ENTRY_SIZE
//    } else if path.len() == 2 {
//        L1_ENTRY_SIZE
//    } else if path.len() == 3 {
//        L2_ENTRY_SIZE
//    } else if path.len() == 4 {
//        L3_ENTRY_SIZE
//    } else { arbitrary() }
//}

///// "Convert" `pt_walk_path` to `WalkResult`
//pub open spec fn pt_walk(pt_mem: PTMem, wr: WalkResult, path: Seq<(usize, GPDE)>) -> bool {
//    match wr {
//        WalkResult::Valid { vbase, pte } => {
//            &&& pt_walk_path(pt_mem, vbase, path)
//            &&& path.last().1 is Page
//            &&& pte == PTE {
//
//            }
//        },
//        WalkResult::Invalid { vbase } => {
//            exists|vbase2| {
//                &&& pt_walk_path(pt_mem, vbase2, path)
//                &&& aligned(vbase as nat, 8)
//                &&& path.last().1 is Empty
//                &&& vbase2 <= vbase < vbase2 + pt_walk_path_size(path)
//            }
//        },
//    }
//}

//#[verifier(external_body)]
//pub struct PTMem {
//    /// `phys_mem_ref` is the starting address of the physical memory linear mapping
//    phys_mem_ref: *mut usize,
//    /// Physical address of the PML4 directory, where address translation starts.
//    pml4: usize,
//}

//pub enum MType {
//    PDir0E,
//    PDir1E,
//    PDir2E,
//    PDir3E,
//    Untyped,
//}

//impl MType {
//    pub open spec fn is_page_type(self) -> bool {
//        match self {
//            MType::PDir0 | MType::PDir1 | MType::PDir2 | MType::PTable => true,
//            MType::User | MType::Untyped => false,
//        }
//    }
//}

// TODO: define this, prove some stuff and add it to vstd
//pub open spec fn flatten<A>(s: Set<Set<A>>) -> Set<A>;

//impl PTMem {
//    ///// The view of the memory is byte-indexed but stores full words. Only 8-byte aligned indices
//    ///// are meaningful. This way we get to store full words without breaking them down into bytes
//    ///// and worrying about endianness but unlike if we kept a word-indexed memory, we also don't
//    ///// have to convert back and forth between u64- and byte-indexed.
//    ///// TODO: unaligned addresses probably just shouldn't be in domain? make an invariant to that effect probably.
//    //pub open spec fn view(self) -> Map<usize, usize>;
//    //
//    //pub open spec fn pml4(self) -> usize;
//    //
//    //pub open spec fn write(self, addr: usize, value: usize) -> PTMem;
//    //
//    ///// Describes the effect of performing a write on the PTMem.
//    //pub proof fn axiom_write(self, addr: usize, value: usize) -> (res: PTMem)
//    //    ensures res@ == self@.insert(addr, value)
//    //{
//    //    admit();
//    //    self.write(addr, value)
//    //}
//
//    //pub open spec fn page_addrs(self) -> Map<usize, GPDE> {
//    //    arbitrary() // TODO: the thing below but as Map
//    //}
//    ///// All addresses that may be used in a page table walk.
//    //pub open spec fn page_addrs(self) -> Set<usize> {
//    //    let l0_addrs = self.page_addrs_aux(set![self.pml4()], 0);
//    //    let l1_addrs = self.page_addrs_aux(l0_addrs, 1);
//    //    let l2_addrs = self.page_addrs_aux(l1_addrs, 2);
//    //    let l3_addrs = self.page_addrs_aux(l2_addrs, 3);
//    //    flatten(set![l0_addrs, l1_addrs, l2_addrs, l3_addrs])
//    //}
//    //
//    ///// Takes all addresses pointing to layer N entries and returns a set of all entries pointing
//    ///// to layer N+1 entries.
//    //pub open spec fn page_addrs_aux(self, addrs: Set<usize>, layer: nat) -> Set<usize> {
//    //    flatten(addrs.map(|prev_addr| {
//    //        let pde = PDE {
//    //            entry: self@[prev_addr] as u64,
//    //            layer: Ghost(layer),
//    //        };
//    //        if self@.contains_key(prev_addr) && !(pde@ is Empty) {
//    //            let next_base = match pde@ {
//    //                GPDE::Directory { addr, .. } => addr,
//    //                GPDE::Page      { addr, .. } => addr,
//    //                GPDE::Empty                  => arbitrary(),
//    //            };
//    //            Set::new(|next_addr: usize| next_base <= next_addr < next_base + 4096 && aligned(next_addr as nat, 8))
//    //        } else {
//    //            set![]
//    //        }
//    //    }))
//    //}
//
//    //pub spec fn regions(self) -> Set<MemRegion>;
//    //
//    //pub spec fn region_view(self, r: MemRegion) -> Seq<u64>;
//
//    //pub open spec fn inv(self) -> bool {
//    //    &&& self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000
//    //    &&& forall|s1: MemRegion, s2: MemRegion|
//    //        self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(
//    //            s1,
//    //            s2,
//    //        )
//    //    //&&& aligned(self.cr3_spec().base as nat, PAGE_SIZE as nat)
//    //    //&&& self.cr3_spec().size == PAGE_SIZE
//    //}
//
//    //pub open spec fn init(self) -> bool {
//    //    &&& self.inv()
//    //}
//
//    ///// `cr3` returns a MemRegion whose base is the address at which the layer 0 page directory is mapped
//    //#[verifier(external_body)]
//    //pub fn cr3(&self) -> (res: MemRegionExec)
//    //    ensures
//    //        res === self.cr3_spec(),
//    //{
//    //    MemRegionExec { base: self.cr3 as usize, size: PAGE_SIZE }
//    //}
//    //
//    //pub open spec fn cr3_spec(&self) -> MemRegionExec;
//
//    //#[verifier(external_body)]
//    ///// Write value to physical address `pbase + idx * WORD_SIZE`
//    //pub fn write(&mut self, pbase: usize, idx: usize, region: Ghost<MemRegion>, value: u64)
//    //    requires
//    //        pbase == region@.base,
//    //        aligned(pbase as nat, WORD_SIZE as nat),
//    //        //old(self).inv(),
//    //        old(self).regions().contains(region@),
//    //        idx < 512,
//    //    ensures
//    //        self.region_view(region@) === old(self).region_view(region@).update(idx as int, value),
//    //        forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
//    //        self.regions() === old(self).regions(),
//    //        //self.alloc_available_pages() == old(self).alloc_available_pages(),
//    //        //self.cr3_spec() == old(self).cr3_spec(),
//    //        //self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
//    //{
//    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
//    //    unsafe {
//    //        self.phys_mem_ref.offset(word_offset).write(value);
//    //    }
//    //}
//    //
//    //#[verifier(external_body)]
//    ///// Read value at physical address `pbase + idx * WORD_SIZE`
//    //pub fn read(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>) -> (res: u64)
//    //    requires
//    //        pbase == region@.base,
//    //        aligned(pbase as nat, WORD_SIZE as nat),
//    //        self.regions().contains(region@),
//    //        idx < 512,
//    //    ensures
//    //        res == self.spec_read(idx as nat, region@),
//    //{
//    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
//    //    unsafe { self.phys_mem_ref.offset(word_offset).read() }
//    //}
//    //
//    //pub open spec fn spec_read(self, idx: nat, region: MemRegion) -> (res: u64) {
//    //    self.region_view(region)[idx as int]
//    //}
//
//    ///// This function manually does the address computation which `read` and `write` rely on not
//    ///// overflowing. Since this function is not `external_body`, Verus checks that there's no
//    ///// overflow. The preconditions are those of `read`, which are a subset of the `write`
//    ///// preconditions.
//    ///// (This is an exec function so it generates the normal overflow VCs.)
//    //#[verus::line_count::ignore]
//    //fn check_overflow(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>)
//    //    requires
//    //        pbase <= MAX_PHYADDR,
//    //        self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000,
//    //        pbase == region@.base,
//    //        aligned(pbase as nat, WORD_SIZE as nat),
//    //        self.regions().contains(region@),
//    //        idx < 512,
//    //{
//    //    proof {
//    //        crate::definitions_u::lemma_maxphyaddr_facts();
//    //    }
//    //    // https://dev-doc.rust-lang.org/beta/std/primitive.pointer.html#method.offset
//    //    // The raw pointer offset computation needs to fit in an isize.
//    //    // isize::MAX is   0x7FFF_FFFF_FFFF_FFFF
//    //    //
//    //    // `pbase` is a physical address, so we know it's <= MAX_PHYADDR (2^52-1).
//    //    // The no-overflow assertions below require phys_mem_ref <= 0x7FEFFFFFFFFFF009.
//    //    // In the invariant we require the (arbitrarily chosen) nicer number
//    //    // 0x7FE0_0000_0000_0000 as an upper bound for phys_mem_ref.
//    //    // (In practice the address has to be smaller anyway, because the address space
//    //    // isn't that large.) NrOS uses 0x4000_0000_0000.
//    //    assert(word_index_spec(pbase as nat) < 0x2_0000_0000_0000) by (nonlinear_arith)
//    //        requires
//    //            aligned(pbase as nat, WORD_SIZE as nat),
//    //            pbase <= MAX_PHYADDR,
//    //            MAX_PHYADDR <= 0xFFFFFFFFFFFFF,
//    //    ;
//    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
//    //    assert(word_offset < 0x2_0000_0000_01FF) by (nonlinear_arith)
//    //        requires
//    //            idx < 512,
//    //            word_offset == word_index_spec(pbase as nat) + idx,
//    //            word_index_spec(pbase as nat) < 0x2_0000_0000_0000,
//    //    ;
//    //    let phys_mem_ref: isize = self.phys_mem_ref_as_usize() as isize;
//    //
//    //    assert(word_offset * WORD_SIZE < 0x10_0000_0000_0FF8) by (nonlinear_arith)
//    //        requires
//    //            word_offset < 0x2_0000_0000_01FF,
//    //    ;
//    //    let byte_offset: isize = word_offset * (WORD_SIZE as isize);
//    //    let raw_ptr_offset = phys_mem_ref + word_offset * (WORD_SIZE as isize);
//    //}
//    //
//    //#[verifier(external_body)]
//    //pub spec fn phys_mem_ref_as_usize_spec(&self) -> usize;
//    //
//    //#[verifier(external_body)]
//    //fn phys_mem_ref_as_usize(&self) -> (res: usize)
//    //    ensures
//    //        res == self.phys_mem_ref_as_usize_spec(),
//    //{
//    //    unsafe { self.phys_mem_ref as usize }
//    //}
//}

} // verus!
