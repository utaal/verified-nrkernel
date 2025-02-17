use vstd::prelude::*;
use crate::spec_t::mmu::defs::{ MemRegion, Arch, PTE };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ overlap, between, aligned };

verus! {

pub struct PageTableContents {
    pub map: Map<nat /* VAddr */, PTE>,
    pub arch: Arch,
    pub lower: nat,
    pub upper: nat,
}

impl PageTableContents {
    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.map.dom().finite()
        &&& self.arch.inv()
        &&& self.mappings_are_of_valid_size()
        &&& self.mappings_are_aligned()
        &&& self.mappings_dont_overlap()
        &&& self.mappings_in_bounds()
    }

    pub open spec(checked) fn mappings_are_of_valid_size(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).frame.size] #![trigger self.map.index(va).frame.base]
            self.map.contains_key(va) ==> self.arch.contains_entry_size(self.map.index(va).frame.size)
    }

    pub open spec(checked) fn mappings_are_aligned(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).frame.size] #![trigger self.map.index(va).frame.base]
            self.map.contains_key(va) ==>
            aligned(va, self.map.index(va).frame.size) && aligned(self.map.index(va).frame.base, self.map.index(va).frame.size)
    }

    pub open spec(checked) fn mappings_dont_overlap(self) -> bool {
        forall|b1: nat, b2: nat|
            #![trigger self.map[b1], self.map[b2]]
            #![trigger self.map.contains_key(b1), self.map.contains_key(b2)]
            self.map.contains_key(b1) && self.map.contains_key(b2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: self.map[b1].frame.size },
                    MemRegion { base: b2, size: self.map[b2].frame.size }))
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(self, base: nat, pte: PTE) -> bool {
        self.lower <= base && base + pte.frame.size <= self.upper
    }

    pub open spec(checked) fn mappings_in_bounds(self) -> bool {
        forall|b1: nat|
            #![trigger self.map[b1]] #![trigger self.map.contains_key(b1)]
            #![trigger self.candidate_mapping_in_bounds(b1, self.map[b1])]
            self.map.contains_key(b1) ==> self.candidate_mapping_in_bounds(b1, self.map[b1])
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PTE) -> bool {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size(pte.frame.size)
    }

    pub open spec(checked) fn valid_mapping(self, base: nat, pte: PTE) -> bool {
        forall|b: nat| #![auto]
            self.map.contains_key(b) ==> !overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: b, size: self.map.index(b).frame.size })
    }

    /// Maps the given `pte` at `base` in the address space
    pub open spec(checked) fn map_frame(self, base: nat, pte: PTE) -> Result<PageTableContents,PageTableContents> {
        if self.accepted_mapping(base, pte) {
            if self.valid_mapping(base, pte) {
                Ok(PageTableContents {
                    map: self.map.insert(base, pte),
                    ..self
                })
            } else {
                Err(self)
            }
        } else {
            arbitrary()
        }
    }

    proof fn map_frame_preserves_inv(self, base: nat, pte: PTE)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            // self.map_frame(base, frame).is_Ok(),
        ensures
            self.map_frame(base, pte).is_Ok()  ==> self.map_frame(base, pte).get_Ok_0().inv(),
            self.map_frame(base, pte).is_Err() ==> self.map_frame(base, pte).get_Err_0() === self,
    {
        if self.map_frame(base, pte).is_Ok() {
            let nself = self.map_frame(base, pte).get_Ok_0();
            assert(nself.mappings_in_bounds());
        }
    }

    pub open spec(checked) fn accepted_resolve(self, vaddr: nat) -> bool {
        between(vaddr, self.lower, self.upper)
    }

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    pub open spec(checked) fn resolve(self, vaddr: nat) -> Result<(nat, PTE),()>
        recommends self.accepted_resolve(vaddr)
    {
        if exists|base:nat, pte:PTE|
            self.map.contains_pair(base, pte) &&
            between(vaddr, base, base + pte.frame.size)
        {
            let (base, pte) = choose|base:nat, pte:PTE|
                self.map.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            Ok((base, pte))
        } else {
            Err(())
        }
    }

    pub open spec(checked) fn remove(self, n: nat) -> PageTableContents {
        PageTableContents {
            map: self.map.remove(n),
            ..self
        }
    }

    pub open spec(checked) fn accepted_unmap(self, base: nat) -> bool {
        &&& between(base, self.lower, self.upper)
        &&& exists|size: nat|
            #![trigger self.arch.contains_entry_size(size)]
            #![trigger aligned(base, size)]
            self.arch.contains_entry_size(size) && aligned(base, size)
    }

    /// Removes the frame from the address space that contains `base`.
    pub open spec(checked) fn unmap(self, base: nat) -> Result<PageTableContents,PageTableContents>
        recommends self.accepted_unmap(base)
    {
        if self.map.contains_key(base) {
            Ok(self.remove(base))
        } else {
            Err(self)
        }
    }

    proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
        ensures
            self.unmap(base).is_Ok() ==> self.unmap(base).get_Ok_0().inv(),
            self.unmap(base).is_Err() ==> self.unmap(base).get_Err_0() === self;

    pub proof fn lemma_unmap_decrements_len(self, base: nat)
        requires
                 self.inv(),
                 self.unmap(base).is_Ok()
        ensures
                self.map.dom().len() > 0,
                equal(self.unmap(base).get_Ok_0().map.dom(), self.map.dom().remove(base)),
                self.unmap(base).get_Ok_0().map.dom().len() == self.map.dom().len() - 1
    {
        assert(self.map.contains_key(base));
    }

    pub open spec fn ranges_disjoint(self, other: Self) -> bool {
        if self.lower <= other.lower {
            self.upper <= other.lower
        } else {
            // other.lower < self.lower
            other.upper <= self.lower
        }
    }

    pub open spec fn mappings_disjoint(self, other: Self) -> bool {
        forall|s: nat, o: nat| self.map.contains_key(s) && other.map.contains_key(o) ==>
            !overlap(MemRegion { base: s, size: self.map.index(s).frame.size }, MemRegion { base: o, size: other.map.index(o).frame.size })
    }

    pub proof fn lemma_ranges_disjoint_implies_mappings_disjoint(self, other: Self)
        requires
            self.inv(),
            other.inv(),
            self.ranges_disjoint(other),
        ensures
            self.mappings_disjoint(other);

    proof fn lemma_mappings_have_positive_entry_size(self)
        requires
            self.inv(),
        ensures
            forall|va: nat| #[trigger] self.map.contains_key(va) ==> self.map.index(va).frame.size > 0;
}

}
