#![verus::trusted]
// trusted:
// these are wrappers for the interface with the memory
// `check_overflow` is a proof to harden the specification, it reduces the overall
// trusted-ness of this file, but not in a quantifiable fashion; for this reason we deem
// it appropriate to exclude it from P:C accounting

use vstd::prelude::*;

use crate::definitions_t::{ MemRegion, MemRegionExec, overlap, aligned, new_seq, PageTableEntry,
WORD_SIZE, PAGE_SIZE, MAX_PHYADDR };

verus! {

pub fn word_index(addr: usize) -> (res: usize)
    requires
        aligned(addr as nat, 8),
    ensures
        res as nat === word_index_spec(addr as nat),
        // Prove this equivalence to use the indexing lemmas
        res as nat === crate::definitions_t::index_from_offset(addr as nat, WORD_SIZE as nat),
        word_index_spec(addr as nat) === crate::definitions_t::index_from_offset(addr as nat, WORD_SIZE as nat),
{
    addr / WORD_SIZE
}

pub open spec fn word_index_spec(addr: nat) -> nat
    recommends aligned(addr, 8)
{
    addr / (WORD_SIZE as nat)
}

pub struct TLB {
}

impl TLB {
    pub spec fn view(self) -> Map<nat,PageTableEntry>;

    /// Invalidates any TLB entries containing `vbase`.
    #[verifier(external_body)]
    pub fn invalidate_entry(&mut self, vbase: usize)
        ensures
            forall|base, pte| self.view().contains_pair(base, pte) ==> old(self).view().contains_pair(base, pte),
            !self.view().dom().contains(vbase as nat),
    {
        unimplemented!()
    }
}

// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just specify reads to return those bits as arbitrary?
#[verifier(external_body)]
pub struct PageTableMemory {
    /// `phys_mem_ref` is the starting address of the physical memory linear mapping
    phys_mem_ref: *mut u64,
    cr3: u64,
}

impl PageTableMemory {
    pub spec fn alloc_available_pages(self) -> nat;
    pub spec fn regions(self) -> Set<MemRegion>;
    pub spec fn region_view(self, r: MemRegion) -> Seq<u64>;

    pub open spec fn inv(self) -> bool {
        &&& self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000
        &&& forall|s1: MemRegion, s2: MemRegion| self.regions().contains(s1) && self.regions().contains(s2) && s1 !== s2 ==> !overlap(s1, s2)
        &&& aligned(self.cr3_spec().base as nat, PAGE_SIZE as nat)
        &&& self.cr3_spec().size == PAGE_SIZE
    }

    pub open spec fn init(self) -> bool {
        &&& self.inv()
    }

    /// `cr3` returns a MemRegion whose base is the address at which the layer 0 page directory is mapped
    #[verifier(external_body)]
    pub fn cr3(&self) -> (res: MemRegionExec)
        ensures res === self.cr3_spec()
    {
        MemRegionExec {
            base: self.cr3 as usize,
            size: PAGE_SIZE,
        }
    }

    pub open spec fn cr3_spec(&self) -> MemRegionExec;

    // We assume that alloc_page never fails. In practice we can just keep a buffer of 3+ pages
    // that are allocated before we use map_frame.
    /// Allocates one page and returns its physical address
    #[verifier(external_body)]
    pub fn alloc_page(&mut self) -> (r: MemRegionExec)
        requires
            old(self).inv(),
            0 < old(self).alloc_available_pages(),
        ensures
            self.alloc_available_pages() == old(self).alloc_available_pages() - 1,
            r@.size == PAGE_SIZE,
            r@.base + PAGE_SIZE <= MAX_PHYADDR,
            aligned(r@.base, PAGE_SIZE as nat),
            !old(self).regions().contains(r@),
            self.regions() === old(self).regions().insert(r@),
            self.region_view(r@) === new_seq::<u64>(512nat, 0u64),
            forall|r2: MemRegion| r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
            self.inv(),
    {
        unimplemented!()
    }

    /// Deallocates a page
    #[verifier(external_body)]
    pub fn dealloc_page(&mut self, r: MemRegionExec)
        requires
            old(self).inv(),
            old(self).regions().contains(r@),
        ensures
            self.regions() === old(self).regions().remove(r@),
            forall|r2: MemRegion| r2 !== r@ ==> #[trigger] self.region_view(r2) === old(self).region_view(r2),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
            self.inv(),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    /// Write value to physical address `pbase + idx * WORD_SIZE`
    pub fn write(&mut self, pbase: usize, idx: usize, region: Ghost<MemRegion>, value: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            old(self).inv(),
            old(self).regions().contains(region@),
            idx < 512,
        ensures
            self.region_view(region@) === old(self).region_view(region@).update(idx as int, value),
            forall|r: MemRegion| r !== region@ ==> self.region_view(r) === old(self).region_view(r),
            self.regions() === old(self).regions(),
            self.alloc_available_pages() == old(self).alloc_available_pages(),
            self.cr3_spec() == old(self).cr3_spec(),
            self.phys_mem_ref_as_usize_spec() == old(self).phys_mem_ref_as_usize_spec(),
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).write(value); }
    }

    #[verifier(external_body)]
    /// Read value at physical address `pbase + idx * WORD_SIZE`
    pub fn read(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>) -> (res: u64)
        requires
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
        ensures
            res == self.spec_read(idx as nat, region@)
    {
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        unsafe { self.phys_mem_ref.offset(word_offset).read() }
    }

    pub open spec fn spec_read(self, idx: nat, region: MemRegion) -> (res: u64) {
        self.region_view(region)[idx as int]
    }

    /// This function manually does the address computation which `read` and `write` rely on not
    /// overflowing. Since this function is not `external_body`, Verus checks that there's no
    /// overflow. The preconditions are those of `read`, which are a subset of the `write`
    /// preconditions.
    /// (This is an exec function so it generates the normal overflow VCs.)
    #[verus::line_count::ignore]
    fn check_overflow(&self, pbase: usize, idx: usize, region: Ghost<MemRegion>)
        requires
            pbase <= MAX_PHYADDR,
            self.phys_mem_ref_as_usize_spec() <= 0x7FE0_0000_0000_0000,
            pbase == region@.base,
            aligned(pbase as nat, WORD_SIZE as nat),
            self.regions().contains(region@),
            idx < 512,
    {
        proof { crate::definitions_u::lemma_maxphyaddr_facts(); }
        // https://dev-doc.rust-lang.org/beta/std/primitive.pointer.html#method.offset
        // The raw pointer offset computation needs to fit in an isize.
        // isize::MAX is   0x7FFF_FFFF_FFFF_FFFF
        //
        // `pbase` is a physical address, so we know it's <= MAX_PHYADDR (2^52-1).
        // The no-overflow assertions below require phys_mem_ref <= 0x7FEFFFFFFFFFF009.
        // In the invariant we require the (arbitrarily chosen) nicer number
        // 0x7FE0_0000_0000_0000 as an upper bound for phys_mem_ref.
        // (In practice the address has to be smaller anyway, because the address space
        // isn't that large.) NrOS uses 0x4000_0000_0000.
        assert(word_index_spec(pbase as nat) < 0x2_0000_0000_0000) by(nonlinear_arith)
            requires
                aligned(pbase as nat, WORD_SIZE as nat),
                pbase <= MAX_PHYADDR,
                MAX_PHYADDR <= 0xFFFFFFFFFFFFF;
        let word_offset: isize = (word_index(pbase) + idx) as isize;
        assert(word_offset < 0x2_0000_0000_01FF) by(nonlinear_arith)
            requires
                idx < 512,
                word_offset == word_index_spec(pbase as nat) + idx,
                word_index_spec(pbase as nat) < 0x2_0000_0000_0000;
        let phys_mem_ref: isize = self.phys_mem_ref_as_usize() as isize;

        assert(word_offset * WORD_SIZE < 0x10_0000_0000_0FF8) by(nonlinear_arith)
            requires word_offset < 0x2_0000_0000_01FF;
        let byte_offset: isize = word_offset * (WORD_SIZE as isize);
        let raw_ptr_offset = phys_mem_ref + word_offset * (WORD_SIZE as isize);
    }

    #[verifier(external_body)]
    pub spec fn phys_mem_ref_as_usize_spec(&self) -> usize;

    #[verifier(external_body)]
    fn phys_mem_ref_as_usize(&self) -> (res: usize)
        ensures res == self.phys_mem_ref_as_usize_spec()
    {
        unsafe { self.phys_mem_ref as usize }
    }
}

}
