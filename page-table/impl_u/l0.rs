#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use modes::*;
use seq::*;
use option::{*, Option::*};
use map::*;
use set::*;
use set_lib::*;
use crate::impl_u::lib;
use vec::*;
use crate::definitions_t::{ MemRegion, overlap, between, Arch, aligned, PageTableEntry, Flags };

use result::{*, Result::*};

verus! {

#[verifier(nonlinear)]
pub proof fn ambient_arith()
    ensures
        forall_arith(|a: nat, b: nat| a == 0 ==> #[trigger] (a * b) == 0),
        forall_arith(|a: nat, b: nat| b == 0 ==> #[trigger] (a * b) == 0),
        forall_arith(|a: nat, b: nat| a > 0 && b > 0 ==> #[trigger] (a * b) > 0),
        forall_arith(|a: int, b: int| #[trigger] (a * b) == (b * a)),
        forall|a:nat| a != 0 ==> aligned(0, a)
{
    lib::aligned_zero();
}

pub proof fn ambient_lemmas1()
    ensures
        forall|s1: Map<nat,PageTableEntry>, s2: Map<nat,PageTableEntry>| s1.dom().finite() && s2.dom().finite() ==> #[trigger] s1.union_prefer_right(s2).dom().finite(),
        forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat|
            (m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)),
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat|
            (m2.dom().contains(n) && !m1.dom().contains(n))
            ==> equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)),
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat, v: PageTableEntry|
            (!m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v)),
        forall|m1: Map<nat, PageTableEntry>, m2: Map<nat, PageTableEntry>, n: nat, v: PageTableEntry|
            (!m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v)),
        // forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().upper == d.upper_vaddr())),
        // forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().lower == d.base_vaddr)),
    {
    lemma_finite_map_union::<nat,PageTableEntry>();
    // assert_nonlinear_by({ ensures(forall|d: Directory| equal(d.num_entries() * d.entry_size(), d.entry_size() * d.num_entries())); });
    // assert_forall_by(|d: Directory, i: nat| {
    //     requires(#[auto_trigger] d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
    //     ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
    //     assert(d.directories_obey_invariant());
    // });
    lemma_map_union_prefer_right_remove_commute::<nat,PageTableEntry>();
    lemma_map_union_prefer_right_insert_commute::<nat,PageTableEntry>();
    assert(forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a)) by (nonlinear_arith) { };
}


pub struct PageTableContents {
    pub map: Map<nat /* VAddr */, PageTableEntry>,
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
            self.map.dom().contains(va) ==> self.arch.contains_entry_size(self.map.index(va).frame.size)
    }

    pub open spec(checked) fn mappings_are_aligned(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).frame.size] #![trigger self.map.index(va).frame.base]
            self.map.dom().contains(va) ==>
            aligned(va, self.map.index(va).frame.size) && aligned(self.map.index(va).frame.base, self.map.index(va).frame.size)
    }

    pub open spec(checked) fn mappings_dont_overlap(self) -> bool {
        forall|b1: nat, b2: nat|
            // TODO verus the default triggers were bad
            #![trigger self.map.index(b1), self.map.index(b2)] #![trigger self.map.dom().contains(b1), self.map.dom().contains(b2)]
            self.map.dom().contains(b1) && self.map.dom().contains(b2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: self.map.index(b1).frame.size },
                    MemRegion { base: b2, size: self.map.index(b2).frame.size }))
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(self, base: nat, pte: PageTableEntry) -> bool {
        self.lower <= base && base + pte.frame.size <= self.upper
    }

    pub open spec(checked) fn mappings_in_bounds(self) -> bool {
        forall|b1: nat|
            #![trigger self.map.index(b1)] #![trigger self.map.dom().contains(b1)]
            #![trigger self.candidate_mapping_in_bounds(b1, self.map.index(b1))]
            self.map.dom().contains(b1) ==> self.candidate_mapping_in_bounds(b1, self.map.index(b1))
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PageTableEntry) -> bool {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size(pte.frame.size)
    }

    pub open spec(checked) fn valid_mapping(self, base: nat, pte: PageTableEntry) -> bool {
        forall|b: nat| #![auto]
            self.map.dom().contains(b) ==> !overlap(
                MemRegion { base: base, size: pte.frame.size },
                MemRegion { base: b, size: self.map.index(b).frame.size })
    }

    /// Maps the given `pte` at `base` in the address space
    pub open spec(checked) fn map_frame(self, base: nat, pte: PageTableEntry) -> Result<PageTableContents,PageTableContents> {
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

    proof fn map_frame_preserves_inv(#[spec] self, base: nat, pte: PageTableEntry)
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
    pub open spec(checked) fn resolve(self, vaddr: nat) -> Result<(nat, PageTableEntry),()>
        recommends self.accepted_resolve(vaddr)
    {
        if exists|base:nat, pte:PageTableEntry|
            self.map.contains_pair(base, pte) &&
            between(vaddr, base, base + pte.frame.size)
        {
            let (base, pte) = choose|base:nat, pte:PageTableEntry|
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

    pub open spec(checked) fn accepted_unmap(self, base:nat) -> bool {
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
        if self.map.dom().contains(base) {
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
        assert(self.map.dom().contains(base));
        lemma_set_contains_IMP_len_greater_zero::<nat>(self.map.dom(), base);
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
        forall|s: nat, o: nat| self.map.dom().contains(s) && other.map.dom().contains(o) ==>
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
            forall|va: nat| #[trigger] self.map.dom().contains(va) ==> self.map.index(va).frame.size > 0;
}

// TODO: move
pub proof fn lemma_set_contains_IMP_len_greater_zero<T>(s: Set<T>, a: T)
    requires
        s.finite(),
        s.contains(a),
    ensures
        s.len() > 0,
{
    if s.len() == 0 {
        // contradiction
        assert(s.remove(a).len() + 1 == 0);
    }
}

pub proof fn lemma_map_union_prefer_right_insert_commute<S,T>()
    ensures
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            !m1.dom().contains(n) && !m2.dom().contains(n)
            ==> equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v)),
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
            !m1.dom().contains(n) && !m2.dom().contains(n)
            ==> equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v)),
{
    assert_forall_by(|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T| {
        requires(!m1.dom().contains(n) && !m2.dom().contains(n));
        ensures(equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v)));
        let union1 = m1.insert(n, v).union_prefer_right(m2);
        let union2 = m1.union_prefer_right(m2).insert(n, v);
        assert_maps_equal!(union1, union2);
        assert(equal(union1, union2));
    });
    assert_forall_by(|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T| {
        requires(!m1.dom().contains(n) && !m2.dom().contains(n));
        ensures(equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v)));
        let union1 = m1.union_prefer_right(m2.insert(n, v));
        let union2 = m1.union_prefer_right(m2).insert(n, v);
        assert_maps_equal!(union1, union2);
        assert(equal(union1, union2));
    });
}

pub proof fn lemma_map_union_prefer_right_remove_commute<S,T>()
    ensures
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S|
            m1.dom().contains(n) && !m2.dom().contains(n)
            ==> equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)),
        forall|m1: Map<S, T>, m2: Map<S, T>, n: S|
            m2.dom().contains(n) && !m1.dom().contains(n)
            ==> equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)),
{
    assert_forall_by(|m1: Map<S, T>, m2: Map<S, T>, n: S| {
        requires(m1.dom().contains(n) && !m2.dom().contains(n));
        ensures(equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)));
        let union1 = m1.remove(n).union_prefer_right(m2);
        let union2 = m1.union_prefer_right(m2).remove(n);
        assert_maps_equal!(union1, union2);
        assert(equal(union1, union2));
        // TODO: verus bug? (uncomment assertions below)
        // substituting union1 and/or union2's definition makes the assertion fail:
        // assert(equal(m1.remove(n).union_prefer_right(m2), union2));
        // assert(equal(union1, m1.union_prefer_right(m2).remove(n)));
    });
    assert_forall_by(|m1: Map<S, T>, m2: Map<S, T>, n: S| {
        requires(m2.dom().contains(n) && !m1.dom().contains(n));
        ensures(equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)));
        let union1 = m1.union_prefer_right(m2.remove(n));
        let union2 = m1.union_prefer_right(m2).remove(n);
        assert_maps_equal!(union1, union2);
        assert(equal(union1, union2));
    });
}

// TODO: should go somewhere else
pub proof fn lemma_finite_map_union<S,T>()
    ensures
        forall|s1: Map<S,T>, s2: Map<S,T>| s1.dom().finite() && s2.dom().finite() ==> #[trigger] s1.union_prefer_right(s2).dom().finite(),
{
    assert_forall_by(|s1: Map<S,T>, s2: Map<S,T>| {
        requires(s1.dom().finite() && s2.dom().finite());
        ensures(#[auto_trigger] s1.union_prefer_right(s2).dom().finite());

        assert(s1.dom().union(s2.dom()).finite());

        let union_dom = s1.union_prefer_right(s2).dom();
        let dom_union = s1.dom().union(s2.dom());

        assert(forall|s: S| union_dom.contains(s) ==> dom_union.contains(s));
        assert(forall|s: S| dom_union.contains(s) ==> union_dom.contains(s));

        assert_sets_equal!(union_dom, dom_union);
    });
}


}
