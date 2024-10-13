use vstd::prelude::*;

use crate::spec_t::hardware::{ GhostPageDirectoryEntry };

use crate::definitions_t::{
    aligned, WORD_SIZE,
};

verus! {

pub fn word_index(addr: usize) -> (res: usize)
    requires
        aligned(addr as nat, 8),
    ensures
        res as nat === word_index_spec(addr as nat),
        // Prove this equivalence to use the indexing lemmas
        res as nat === crate::definitions_t::index_from_offset(addr as nat, WORD_SIZE as nat),
        word_index_spec(addr as nat) === crate::definitions_t::index_from_offset(
            addr as nat,
            WORD_SIZE as nat,
        ),
{
    addr / WORD_SIZE
}

pub open spec fn word_index_spec(addr: nat) -> nat
    recommends aligned(addr, 8),
{
    addr / (WORD_SIZE as nat)
}

#[verifier(external_body)]
pub struct PTMem {
    /// `phys_mem_ref` is the starting address of the physical memory linear mapping
    phys_mem_ref: *mut usize,
    /// Physical address of the PML4 directory, where address translation starts.
    pml4: usize,
}

//pub enum MType {
//    PDir0,
//    PDir1,
//    PDir2,
//    PTable,
//    User,
//    Untyped,
//}
//
//impl MType {
//    pub open spec fn is_page_type(self) -> bool {
//        match self {
//            MType::PDir0 | MType::PDir1 | MType::PDir2 | MType::PTable => true,
//            MType::User | MType::Untyped => false,
//        }
//    }
//}

// TODO: define this, prove some stuff and add it to vstd
pub open spec fn flatten<A>(s: Set<Set<A>>) -> Set<A>;

impl PTMem {
    /// The view of the memory is byte-indexed but stores full words. Only 8-byte aligned indices
    /// are meaningful. This way we get to store full words without breaking them down into bytes
    /// and worrying about endianness but unlike if we kept a word-indexed memory, we also don't
    /// have to convert back and forth between u64- and byte-indexed.
    /// TODO: unaligned addresses probably just shouldn't be in domain? make an invariant to that effect probably.
    pub open spec fn view(self) -> Map<usize, usize>;

    pub open spec fn pml4(self) -> usize;

    pub open spec fn write(self, addr: usize, value: usize) -> PTMem;
    
    /// Describes the effect of performing a write on the PTMem.
    pub proof fn axiom_write(self, addr: usize, value: usize) -> (res: PTMem)
        ensures res@ == self@.insert(addr, value)
    {
        admit();
        self.write(addr, value)
    }

    pub open spec fn page_addrs(self) -> Map<usize, GhostPageDirectoryEntry> {
        arbitrary() // TODO: the thing below but as Map
    }
    ///// All addresses that may be used in a page table walk.
    //pub open spec fn page_addrs(self) -> Set<usize> {
    //    let l0_addrs = self.page_addrs_aux(set![self.pml4()], 0);
    //    let l1_addrs = self.page_addrs_aux(l0_addrs, 1);
    //    let l2_addrs = self.page_addrs_aux(l1_addrs, 2);
    //    let l3_addrs = self.page_addrs_aux(l2_addrs, 3);
    //    flatten(set![l0_addrs, l1_addrs, l2_addrs, l3_addrs])
    //}
    //
    ///// Takes all addresses pointing to layer N entries and returns a set of all entries pointing
    ///// to layer N+1 entries.
    //pub open spec fn page_addrs_aux(self, addrs: Set<usize>, layer: nat) -> Set<usize> {
    //    flatten(addrs.map(|prev_addr| {
    //        let pde = PageDirectoryEntry {
    //            entry: self@[prev_addr] as u64,
    //            layer: Ghost(layer),
    //        };
    //        if self@.contains_key(prev_addr) && !(pde@ is Empty) {
    //            let next_base = match pde@ {
    //                GhostPageDirectoryEntry::Directory { addr, .. } => addr,
    //                GhostPageDirectoryEntry::Page      { addr, .. } => addr,
    //                GhostPageDirectoryEntry::Empty                  => arbitrary(),
    //            };
    //            Set::new(|next_addr: usize| next_base <= next_addr < next_base + 4096 && aligned(next_addr as nat, 8))
    //        } else {
    //            set![]
    //        }
    //    }))
    //}

    //pub spec fn regions(self) -> Set<MemRegion>;
    //
    //pub spec fn region_view(self, r: MemRegion) -> Seq<u64>;

    //pub open spec fn inv(self) -> bool {
    //    &&& self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000
    //    &&& forall|s1: MemRegion, s2: MemRegion|
    //        self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(
    //            s1,
    //            s2,
    //        )
    //    //&&& aligned(self.cr3_spec().base as nat, PAGE_SIZE as nat)
    //    //&&& self.cr3_spec().size == PAGE_SIZE
    //}

    //pub open spec fn init(self) -> bool {
    //    &&& self.inv()
    //}

    ///// `cr3` returns a MemRegion whose base is the address at which the layer 0 page directory is mapped
    //#[verifier(external_body)]
    //pub fn cr3(&self) -> (res: MemRegionExec)
    //    ensures
    //        res === self.cr3_spec(),
    //{
    //    MemRegionExec { base: self.cr3 as usize, size: PAGE_SIZE }
    //}
    //
    //pub open spec fn cr3_spec(&self) -> MemRegionExec;

    //#[verifier(external_body)]
    ///// Write value to physical address `pbase + idx * WORD_SIZE`
    //pub fn write(&mut self, pbase: usize, idx: usize, region: Ghost<MemRegion>, value: u64)
    //    requires
    //        pbase == region@.base,
    //        aligned(pbase as nat, WORD_SIZE as nat),
    //        //old(self).inv(),
    //        old(self).regions().contains(region@),
    //        idx < 512,
    //    ensures
    //        self.region_view(region@) === old(self).region_view(region@).update(idx as int, value),
    //        forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
    //        self.regions() === old(self).regions(),
    //        //self.alloc_available_pages() == old(self).alloc_available_pages(),
    //        //self.cr3_spec() == old(self).cr3_spec(),
    //        //self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
    //{
    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
    //    unsafe {
    //        self.phys_mem_ref.offset(word_offset).write(value);
    //    }
    //}
    //
    //#[verifier(external_body)]
    ///// Read value at physical address `pbase + idx * WORD_SIZE`
    //pub fn read(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>) -> (res: u64)
    //    requires
    //        pbase == region@.base,
    //        aligned(pbase as nat, WORD_SIZE as nat),
    //        self.regions().contains(region@),
    //        idx < 512,
    //    ensures
    //        res == self.spec_read(idx as nat, region@),
    //{
    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
    //    unsafe { self.phys_mem_ref.offset(word_offset).read() }
    //}
    //
    //pub open spec fn spec_read(self, idx: nat, region: MemRegion) -> (res: u64) {
    //    self.region_view(region)[idx as int]
    //}

    ///// This function manually does the address computation which `read` and `write` rely on not
    ///// overflowing. Since this function is not `external_body`, Verus checks that there's no
    ///// overflow. The preconditions are those of `read`, which are a subset of the `write`
    ///// preconditions.
    ///// (This is an exec function so it generates the normal overflow VCs.)
    //#[verus::line_count::ignore]
    //fn check_overflow(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>)
    //    requires
    //        pbase <= MAX_PHYADDR,
    //        self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000,
    //        pbase == region@.base,
    //        aligned(pbase as nat, WORD_SIZE as nat),
    //        self.regions().contains(region@),
    //        idx < 512,
    //{
    //    proof {
    //        crate::definitions_u::lemma_maxphyaddr_facts();
    //    }
    //    // https://dev-doc.rust-lang.org/beta/std/primitive.pointer.html#method.offset
    //    // The raw pointer offset computation needs to fit in an isize.
    //    // isize::MAX is   0x7FFF_FFFF_FFFF_FFFF
    //    //
    //    // `pbase` is a physical address, so we know it's <= MAX_PHYADDR (2^52-1).
    //    // The no-overflow assertions below require phys_mem_ref <= 0x7FEFFFFFFFFFF009.
    //    // In the invariant we require the (arbitrarily chosen) nicer number
    //    // 0x7FE0_0000_0000_0000 as an upper bound for phys_mem_ref.
    //    // (In practice the address has to be smaller anyway, because the address space
    //    // isn't that large.) NrOS uses 0x4000_0000_0000.
    //    assert(word_index_spec(pbase as nat) < 0x2_0000_0000_0000) by (nonlinear_arith)
    //        requires
    //            aligned(pbase as nat, WORD_SIZE as nat),
    //            pbase <= MAX_PHYADDR,
    //            MAX_PHYADDR <= 0xFFFFFFFFFFFFF,
    //    ;
    //    let word_offset: isize = (word_index(pbase) + idx) as isize;
    //    assert(word_offset < 0x2_0000_0000_01FF) by (nonlinear_arith)
    //        requires
    //            idx < 512,
    //            word_offset == word_index_spec(pbase as nat) + idx,
    //            word_index_spec(pbase as nat) < 0x2_0000_0000_0000,
    //    ;
    //    let phys_mem_ref: isize = self.phys_mem_ref_as_usize() as isize;
    //
    //    assert(word_offset * WORD_SIZE < 0x10_0000_0000_0FF8) by (nonlinear_arith)
    //        requires
    //            word_offset < 0x2_0000_0000_01FF,
    //    ;
    //    let byte_offset: isize = word_offset * (WORD_SIZE as isize);
    //    let raw_ptr_offset = phys_mem_ref + word_offset * (WORD_SIZE as isize);
    //}
    //
    //#[verifier(external_body)]
    //pub spec fn phys_mem_ref_as_usize_spec(&self) -> usize;
    //
    //#[verifier(external_body)]
    //fn phys_mem_ref_as_usize(&self) -> (res: usize)
    //    ensures
    //        res == self.phys_mem_ref_as_usize_spec(),
    //{
    //    unsafe { self.phys_mem_ref as usize }
    //}
}

} // verus!
