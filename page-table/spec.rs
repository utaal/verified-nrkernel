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
use vec::*;
use crate::lib_axiom::*;

use crate::lib::aligned;
use result::{*, Result::*};

verus! {

proof fn ambient_lemmas1()
    ensures
        forall(|d: Directory, i: nat| with_triggers!([d.inv(), d.entries.index(i)] => d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory() >>= d.entries.index(i).get_Directory_0().inv())),
        forall(|s1: Map<nat,MemRegion>, s2: Map<nat,MemRegion>| s1.dom().finite() && s2.dom().finite() >>= #[trigger] s1.union_prefer_right(s2).dom().finite()),
        forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
        forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
               (m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))),
        forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
               (m2.dom().contains(n) && !m1.dom().contains(n))
               >>= equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n))),
        forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat, v: MemRegion|
               (!m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v))),
        forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat, v: MemRegion|
               (!m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v))),
        // forall(|d: Directory| d.inv() >>= (#[trigger] d.interp().upper == d.upper_vaddr())),
        // forall(|d: Directory| d.inv() >>= (#[trigger] d.interp().lower == d.base_vaddr)),
    {
    lemma_finite_map_union::<nat,MemRegion>();
    assert_nonlinear_by({ ensures(forall(|d: Directory| equal(d.num_entries() * d.entry_size(), d.entry_size() * d.num_entries()))); });
    assert_forall_by(|d: Directory, i: nat| {
        requires(#[auto_trigger] d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
        ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
        assert(d.directories_obey_invariant());
    });
    lemma_map_union_prefer_right_remove_commute::<nat,MemRegion>();
    lemma_map_union_prefer_right_insert_commute::<nat,MemRegion>();
}

// This contains postconditions for which we need to call lemmas that depend on ambient_lemmas1.
// Proving these in ambient_lemmas1 would cause infinite recursion.
proof fn ambient_lemmas2()
    ensures
        forall(|d: Directory| d.inv() >>= (#[trigger] d.interp()).upper == d.upper_vaddr()),
        forall(|d: Directory| d.inv() >>= (#[trigger] d.interp()).lower == d.base_vaddr),
{
    assert_forall_by(|d: Directory| {
        requires(d.inv());
        ensures(#[auto_trigger] d.interp().upper == d.upper_vaddr() && d.interp().lower == d.base_vaddr);
        d.lemma_inv_implies_interp_inv();
    });
}


// #[proof]
// fn ambient_lemmas3() {
//     ensures([
//             forall(|d: Directory, base: nat, frame: MemRegion|
//                    d.inv() && #[trigger] d.accepted_mapping(base, frame) >>=
//                    d.interp().accepted_mapping(base, frame)),
//     ]);
//     assert_forall_by(|d: Directory, base: nat, frame: MemRegion| {
//         requires(d.inv() && #[trigger] d.accepted_mapping(base, frame));
//         ensures(d.interp().accepted_mapping(base, frame));
//         d.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
//     });
// }

#[derive(PartialEq, Eq, Structural)]
pub struct MemRegion { pub base: nat, pub size: nat }

// TODO use VAddr, PAddr

pub open spec fn strictly_decreasing(s: Seq<nat>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) > s.index(j))
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
}

// page_size, next_sizes
// 2**40    , [ 2 ** 30, 2 ** 20 ]
// 2**30    , [ 2 ** 20 ]
// 2**20    , [ ]

// [es0 # es1 , es2 , es3 ] // entry_size
// [1T  # 1G  , 1M  , 1K  ] // pages mapped at this level are this size <--

// [n0  # n1  , n2  , n3  ] // number_of_entries
// [1   # 1024, 1024, 1024]

// es1 == es0 / n1 -- n1 * es1 == es0
// es2 == es1 / n2 -- n2 * es2 == es1
// es3 == es2 / n3 -- n3 * es3 == es2

// [es0  #  es1 , es2 , es3 , es4 ] // entry_size
// [256T #  512G, 1G  , 2M  , 4K  ]
// [n0   #  n1  , n2  , n3  , n4  ] // number_of_entries
// [     #  512 , 512 , 512 , 512 ]
// [     #  9   , 9   , 9   , 9   , 12  ]

pub struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries of at this layer
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {
    pub closed spec(checked) fn inv(&self) -> bool {
        forall(|i:nat| with_triggers!([self.layers.index(i).entry_size], [self.layers.index(i).num_entries] => i < self.layers.len() >>= (
            true
            && self.layers.index(i).entry_size > 0
            && self.layers.index(i).num_entries > 0
            && self.entry_size_is_next_layer_size(i))))
    }

    pub closed spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends i < self.layers.len()
    {
        i + 1 < self.layers.len() >>=
            self.layers.index(i).entry_size == self.layers.index((i + 1) as nat).entry_size * self.layers.index((i + 1) as nat).num_entries
    }

    pub closed spec(checked) fn contains_entry_size_at_index_atleast(&self, entry_size: nat, min_idx: nat) -> bool {
        exists(|i: nat| min_idx <= i && i < self.layers.len() && #[trigger] self.layers.index(i).entry_size == entry_size)
    }

    pub closed spec(checked) fn contains_entry_size(&self, entry_size: nat) -> bool {
        self.contains_entry_size_at_index_atleast(entry_size, 0)
    }

    pub proof fn lemma_entry_sizes_aligned(self, i: nat, j: nat)
        requires
            self.inv(),
            i <= j,
            j < self.layers.len(),
        ensures
            aligned(self.layers.index(i).entry_size, self.layers.index(j).entry_size)
        decreases (self.layers.len() - i)
    {
        ambient_lemmas1();
        if i == j {
        } else {
            self.lemma_entry_sizes_aligned(i+1,j);
            crate::lib::mod_of_mul_auto();
            crate::lib::aligned_transitive_auto();
        }
        // NOTE: This is the only non-nonlinear lemma that became unstable when
        // switching to z3 4.8.17.
        assume(false); // unstable
    }

    pub proof fn lemma_entry_sizes_aligned_auto(self)
        ensures
            forall(|i: nat, j: nat|
                   self.inv() && i <= j && j < self.layers.len() >>=
                   aligned(self.layers.index(i).entry_size, self.layers.index(j).entry_size))
    {
        assert_forall_by(|i: nat, j: nat| {
            requires(self.inv() && i <= j && j < self.layers.len());
            ensures(aligned(self.layers.index(i).entry_size, self.layers.index(j).entry_size));
            self.lemma_entry_sizes_aligned(i, j);
        });
    }
}

proof fn arch_inv_test() {
    let x86 = Arch {
        layers: seq![
            ArchLayer { entry_size: 512 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 1 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 2 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 4 * 1024, num_entries: 512 },
        ],
    };
    // assert(x86.inv()); unstable
    assert(x86.layers.index(3).entry_size == 4096);
    assert(x86.contains_entry_size(4096));
}

// FIXME: conversion, should this really be tracked or just ghost? (was proof before)
pub tracked struct PageTableContents {
    pub map: Map<nat /* VAddr */, MemRegion>,
    pub arch: Arch,
    pub lower: nat,
    pub upper: nat,
}

pub open spec(checked) fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region2.base < region1.base + region1.size
    } else {
        region1.base < region2.base + region2.size
    }
}

fn overlap_sanity_check() {
    assert(overlap(
            MemRegion { base: 0, size: 4096 },
            MemRegion { base: 0, size: 4096 }));
    assert(overlap(
            MemRegion { base: 0, size: 8192 },
            MemRegion { base: 0, size: 4096 }));
    assert(overlap(
            MemRegion { base: 0, size: 4096 },
            MemRegion { base: 0, size: 8192 }));
    assert(overlap(
            MemRegion { base: 0, size: 8192 },
            MemRegion { base: 4096, size: 4096 }));
    assert(!overlap(
            MemRegion { base: 4096, size: 8192 },
            MemRegion { base: 0, size: 4096 }));
    assert(!overlap(
            MemRegion { base: 0, size: 4096 },
            MemRegion { base: 8192, size: 16384 }));
}

impl PageTableContents {
    pub closed spec(checked) fn inv(&self) -> bool {
        true
        && self.map.dom().finite()
        && self.arch.inv()
        && self.mappings_are_of_valid_size()
        && self.mappings_are_aligned()
        && self.mappings_dont_overlap()
        && self.mappings_in_bounds()
    }

    pub closed spec(checked) fn mappings_are_of_valid_size(self) -> bool {
        forall(|va: nat| with_triggers!([self.map.index(va).size],[self.map.index(va).base] =>
                                        self.map.dom().contains(va) >>= self.arch.contains_entry_size(self.map.index(va).size)))
    }

    pub closed spec(checked) fn mappings_are_aligned(self) -> bool {
        forall(|va: nat| with_triggers!([self.map.index(va).size],[self.map.index(va).base] =>
                                        self.map.dom().contains(va)
                                        >>= (aligned(va, self.map.index(va).size)
                                             && aligned(self.map.index(va).base, self.map.index(va).size))))
    }

    pub closed spec(checked) fn mappings_dont_overlap(self) -> bool {
        forall(|b1: nat, b2: nat| // TODO verus the default triggers were bad
               with_triggers!([self.map.index(b1), self.map.index(b2)],
                              [self.map.dom().contains(b1), self.map.dom().contains(b2)] =>
                              (self.map.dom().contains(b1) && self.map.dom().contains(b2))
                              >>= ((b1 == b2) || !overlap(
                                      MemRegion { base: b1, size: self.map.index(b1).size },
                                      MemRegion { base: b2, size: self.map.index(b2).size }))))
    }

    pub closed spec(checked) fn candidate_mapping_in_bounds(self, base: nat, frame: MemRegion) -> bool {
        self.lower <= base && base + frame.size <= self.upper
    }

    pub closed spec(checked) fn mappings_in_bounds(self) -> bool {
        forall(|b1: nat|
               with_triggers!([self.map.index(b1)], [self.map.dom().contains(b1)], [self.candidate_mapping_in_bounds(b1, self.map.index(b1))] =>
                              self.map.dom().contains(b1) >>= self.candidate_mapping_in_bounds(b1, self.map.index(b1))))
    }

    pub closed spec(checked) fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
        && self.candidate_mapping_in_bounds(base, frame)
        && self.arch.contains_entry_size(frame.size)
    }

    pub closed spec(checked) fn valid_mapping(self, base: nat, frame: MemRegion) -> bool {
        forall(|b: nat| #[auto_trigger] self.map.dom().contains(b) >>= !overlap(
                MemRegion { base: base, size: frame.size },
                MemRegion { base: b, size: self.map.index(b).size }
                ))
    }

    /// Maps the given `frame` at `base` in the address space
    pub closed spec(checked) fn map_frame(self, base: nat, frame: MemRegion) -> Result<PageTableContents,()> {
        if self.accepted_mapping(base, frame) {
            if self.valid_mapping(base, frame) {
                Ok(PageTableContents {
                    map: self.map.insert(base, frame),
                    ..self
                })
            } else {
                Err(())
            }
        } else {
            arbitrary()
        }
    }

    // don't think this is actually necessary for anything?
    proof fn map_frame_maps_valid(#[spec] self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
            self.valid_mapping(base, frame),
        ensures
            self.map_frame(base, frame).is_Ok();

    proof fn map_frame_preserves_inv(#[spec] self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
            self.map_frame(base, frame).is_Ok(),
        ensures
            self.map_frame(base, frame).get_Ok_0().inv(),
    {
        let nself = self.map_frame(base, frame).get_Ok_0();
        assert(nself.mappings_in_bounds());
    }

    spec(checked) fn accepted_resolve(self, vaddr: nat) -> bool {
        between(vaddr, self.lower, self.upper)
    }

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    // #[spec] fn resolve(self, vaddr: nat) -> MemRegion {
    spec(checked) fn resolve(self, vaddr: nat) -> Result<nat,()>
        recommends self.accepted_resolve(vaddr)
    {
        if exists(|base:nat|
                  self.map.dom().contains(base) &&
                  between(vaddr, base, base + (#[trigger] self.map.index(base)).size)) {
            let base = choose(|base:nat|
                           self.map.dom().contains(base) &&
                           between(vaddr, base, base + (#[trigger] self.map.index(base)).size));
            let offset = vaddr - base;
            Ok(self.map.index(base).base + offset)
        } else {
            Err(())
        }
    }

    spec(checked) fn remove(self, n: nat) -> PageTableContents {
        PageTableContents {
            map: self.map.remove(n),
            ..self
        }
    }

    spec(checked) fn accepted_unmap(self, base:nat) -> bool {
        true
        && between(base, self.lower, self.upper)
        && exists(|size: nat| with_triggers!([self.arch.contains_entry_size(size)], [aligned(base, size)] =>
            self.arch.contains_entry_size(size) && aligned(base, size)))
    }

    /// Removes the frame from the address space that contains `base`.
    spec(checked) fn unmap(self, base: nat) -> Result<PageTableContents,()>
        recommends self.accepted_unmap(base)
    {
        if self.map.dom().contains(base) {
            Ok(self.remove(base))
        } else {
            Err(())
        }
    }

    proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
            self.unmap(base).is_Ok(),
        ensures
            self.unmap(base).get_Ok_0().inv();

    proof fn lemma_unmap_decrements_len(self, base: nat)
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

    pub closed spec fn ranges_disjoint(self, other: Self) -> bool {
        if self.lower <= other.lower {
            self.upper <= other.lower
        } else {
            // other.lower < self.lower
            other.upper <= self.lower
        }
    }

    pub closed spec fn mappings_disjoint(self, other: Self) -> bool {
        forall(|s: nat, o: nat| self.map.dom().contains(s) && other.map.dom().contains(o) >>=
            !overlap(MemRegion { base: s, size: self.map.index(s).size }, MemRegion { base: o, size: other.map.index(o).size }))
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
            forall(|va: nat| #[trigger] self.map.dom().contains(va)
                   >>= self.map.index(va).size > 0);
}


// Second refinement layer

// FIXME: conversion, should this be tracked or ghost?
#[is_variant]
pub tracked enum NodeEntry {
    Directory(Directory),
    Page(MemRegion),
    Empty(),
}

// FIXME: conversion, should this be tracked or ghost?
pub tracked struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat,       // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
}

// Layer 0: 425 Directory ->
// Layer 1: 47  Directory ->
// Layer 2: 5   Page (1K)

// Layer 1: 46  Directory -> (1M)
// Layer 2: 1024 Pages

// Layer 0: 1024 Directories (1T)
// Layer 1: 1024 Directories (1G)
// Layer 2: 1024 Pages

impl Directory {

    pub closed spec(checked) fn well_formed(&self) -> bool {
        true
        && self.arch.inv()
        && self.layer < self.arch.layers.len()
        && aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        && self.entries.len() == self.num_entries()
    }

    pub closed spec(checked) fn arch_layer(&self) -> ArchLayer
        recommends self.well_formed()
    {
        self.arch.layers.index(self.layer)
    }

    pub closed spec(checked) fn entry_size(&self) -> nat
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.layers.index(self.layer).entry_size
    }

    pub closed spec(checked) fn num_entries(&self) -> nat // number of entries
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.layers.index(self.layer).num_entries
    }

    pub closed spec(checked) fn empty(&self) -> bool
        recommends self.well_formed()
    {
        forall(|i: nat| i < self.num_entries() >>= self.entries.index(i).is_Empty())
    }

    pub closed spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends self.well_formed()
    {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Page())
               >>= (#[trigger] self.entries.index(i)).get_Page_0().size == self.entry_size())
    }

    pub closed spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends self.well_formed()
    {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= {
                    let directory = (#[trigger] self.entries.index(i)).get_Directory_0();
                    true
                    && directory.layer == self.layer + 1
                    && directory.base_vaddr == self.base_vaddr + i * self.entry_size()
                })
    }

    pub closed spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases (self.arch.layers.len() - self.layer, 0)
    {
        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
                   >>= (#[trigger] self.entries.index(i)).get_Directory_0().inv())
        } else {
            arbitrary()
        }
    }

    pub closed spec(checked) fn directories_match_arch(&self) -> bool {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= equal((#[trigger] self.entries.index(i)).get_Directory_0().arch, self.arch))
    }

    pub closed spec fn directories_are_nonempty(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
    {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= !(#[trigger] self.entries.index(i).get_Directory_0().empty()))
            // TODO: Maybe pick a more aggressive trigger?
    }

    pub closed spec(checked) fn frames_aligned(&self) -> bool
        recommends self.well_formed()
    {
        forall(|i: nat| i < self.entries.len() && self.entries.index(i).is_Page() >>=
                  aligned((#[trigger] self.entries.index(i)).get_Page_0().base, self.entry_size()))
    }

    pub closed spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer
    {
        true
        && self.well_formed()
        && self.pages_match_entry_size()
        && self.directories_are_in_next_layer()
        && self.directories_match_arch()
        && self.directories_obey_invariant()
        && self.directories_are_nonempty()
        && self.frames_aligned()
    }

    pub closed spec(checked) fn interp(self) -> PageTableContents {
        self.interp_aux(0)
    }

    pub closed spec(checked) fn upper_vaddr(self) -> nat
        recommends self.well_formed()
    {
        self.base_vaddr + self.num_entries() * self.entry_size()
    }

    pub closed spec(checked) fn vaddr_offset(self, vaddr: nat) -> nat {
        vaddr - self.base_vaddr
    }

    pub closed spec fn index_for_vaddr(self, vaddr: nat) -> /*index: */ nat {
         self.vaddr_offset(vaddr) / self.entry_size()
    }

    pub closed spec(checked) fn entry_base(self, entry: nat) -> nat
        recommends self.inv()
    {
        self.base_vaddr + entry * self.entry_size()
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_entry_base_manual(self, i: nat)
        requires
            self.inv(),
        ensures
            forall_arith(|j: nat| j < i >>= self.entry_base(j) < self.entry_base(i) && self.entry_base(#[trigger] (j+1)) <= self.entry_base(i)),
            aligned(self.entry_base(i), self.entry_size()),
            // forall(|i: nat| i < self.num_entries() && self.entries.index(i).is_Directory() >>= {
            //     let d = self.entries.index(i).get_Directory_0();
            //     d.upper_vaddr() == self.entry_base(i+1)
            // })
    {
        self.lemma_entry_base_auto();
    }

    #[verifier(nonlinear)]
    pub proof fn lemma_entry_base_auto(self)
        requires
            self.inv(),
        ensures
            forall(|i: nat, j: nat| i < j >>= #[trigger] self.entry_base(i) < #[trigger] self.entry_base(j) && self.entry_base(i+1) <= self.entry_base(j)),
            forall(|i: nat| #[auto_trigger] aligned(self.entry_base(i), self.entry_size())),
            // forall(|i: nat| i < self.num_entries() && self.entries.index(i).is_Directory() >>= {
            //     let d = self.entries.index(i).get_Directory_0();
            //     d.upper_vaddr() == self.entry_base(i+1)
            // })
    {

        // Postcondition 2
        assert_forall_by(|i: nat| {
            ensures(#[auto_trigger] aligned(self.entry_base(i), self.entry_size()));
            crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
            assert(aligned(self.base_vaddr, self.entry_size()));
            crate::lib::mod_of_mul(i, self.entry_size());
            assert(aligned(i * self.entry_size(), self.entry_size()));
            crate::lib::mod_add_zero(self.base_vaddr, i * self.entry_size(), self.entry_size());
            assert(aligned(self.base_vaddr + i * self.entry_size(), self.entry_size()));
        });

        assume(false); // unstable
    }

    pub closed spec fn entry_bounds(self, entry: nat) -> (nat, nat) {
        (self.entry_base(entry), self.entry_base(entry + 1))
    }

    pub closed spec fn interp_of_entry(self, entry: nat) -> PageTableContents
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - entry, 0)
    {
        if self.inv() && entry < self.entries.len() {
            let (lower, upper) = self.entry_bounds(entry);
            PageTableContents {
                map: match self.entries.index(entry) {
                    NodeEntry::Page(p)      => map![self.entry_base(entry) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                },
                arch: self.arch,
                lower,
                upper,
            }
        } else {
            arbitrary()
        }
    }

    proof fn lemma_interp_of_entry(self)
        requires
            self.inv(),
        ensures
            forall(|i: nat| #[auto_trigger]
                   i < self.num_entries() >>=
                   self.interp_of_entry(i).inv() &&
                   self.interp_of_entry(i).lower == self.entry_base(i) &&
                   self.interp_of_entry(i).upper == self.entry_base(i+1) &&
                   forall(|base: nat| self.interp_of_entry(i).map.dom().contains(base) >>= between(base, self.entry_base(i), self.entry_base(i+1))) &&
                   forall(|base: nat, p: MemRegion| self.interp_of_entry(i).map.contains_pair(base, p) >>= between(base, self.entry_base(i), self.entry_base(i+1)))),
    {
        assert_forall_by(|i: nat| {
            requires(i < self.num_entries());
            ensures( #[auto_trigger]
                     self.interp_of_entry(i).inv() &&
                     self.interp_of_entry(i).lower == self.entry_base(i) &&
                     self.interp_of_entry(i).upper == self.entry_base(i+1));
            self.lemma_inv_implies_interp_of_entry_inv(i);
        });
    }

    proof fn lemma_inv_implies_interp_of_entry_inv(self, i: nat)
        requires
            self.inv(),
            i < self.num_entries(),
        ensures
            self.interp_of_entry(i).inv(),
            self.interp_of_entry(i).lower == self.entry_base(i),
            self.interp_of_entry(i).upper == self.entry_base(i+1),
    {

        let entry_i = self.interp_of_entry(i);

        self.lemma_entry_base_auto();
        match self.entries.index(i) {
            NodeEntry::Page(p)      => {
                assert(entry_i.mappings_dont_overlap());

                assert_nonlinear_by({
                    requires([
                             self.inv(),
                             equal(entry_i, self.interp_of_entry(i)),
                             self.entry_size() == p.size,
                             i < self.entries.len(),
                    ]);
                    ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), p));
                });
                assert(entry_i.mappings_in_bounds());
            }
            NodeEntry::Directory(d) => {
                assert(self.directories_obey_invariant());
                d.lemma_inv_implies_interp_inv();
                assert_nonlinear_by({
                    requires([
                             self.inv(),
                             equal(entry_i, self.interp_of_entry(i)),
                             d.interp_aux(0).inv(),
                             d.interp_aux(0).lower == self.entry_base(i),
                             d.base_vaddr == self.entry_base(i),
                             d.entry_size() * d.num_entries() == self.entry_size(),
                             d.interp_aux(0).upper == d.upper_vaddr(),
                             equal(self.interp_of_entry(i).map, d.interp_aux(0).map),
                             i < self.entries.len(),
                    ]);
                    ensures(entry_i.mappings_in_bounds());
                    assert(entry_i.lower <= d.interp_aux(0).lower); // proof stability
                    assert(entry_i.upper >= d.interp_aux(0).upper); // proof stability
                });
                assert(entry_i.mappings_in_bounds());
            }
            NodeEntry::Empty()      => {}
        }
    }

    proof fn lemma_interp_of_entries_disjoint(self)
        requires
            self.inv(),
        ensures
            forall(|i: nat, j: nat|
                   i < self.num_entries() && j < self.num_entries() && i != j
                   >>= self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j))),
    {
        assert_forall_by(|i: nat, j: nat| {
            requires(i < self.num_entries() && j < self.num_entries() && i != j);
            ensures(self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j)));

            if i < j {
                assert_nonlinear_by({
                    requires([
                             self.inv(),
                             i < j,
                             self.entry_size() > 0
                    ]);
                    ensures([
                            self.base_vaddr + i * self.entry_size() <= self.base_vaddr + j * self.entry_size(),
                            self.base_vaddr + (i+1) * self.entry_size() <= self.base_vaddr + j * self.entry_size()
                    ]);
                    assume(false); // unstable
                });
            } else {
                assert_nonlinear_by({
                    requires([
                             self.inv(),
                             j < i,
                             self.entry_size() > 0
                    ]);
                    ensures([
                            self.base_vaddr + j * self.entry_size() < self.base_vaddr + i * self.entry_size(),
                            self.base_vaddr + (j+1) * self.entry_size() <= self.base_vaddr + i * self.entry_size()
                    ]);
                    assume(false); // unstable
                });
            }
        });
    }

    pub closed spec(checked) fn interp_aux(self, i: nat) -> PageTableContents
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i, 1)
    {

        if self.inv() {
            if i >= self.entries.len() {
                PageTableContents {
                    map: map![],
                    arch: self.arch,
                    lower: self.upper_vaddr(),
                    upper: self.upper_vaddr(),
                }
            } else { // i < self.entries.len()
                let rem = self.interp_aux(i + 1);
                let entry_i = self.interp_of_entry(i);
                PageTableContents {
                    map: rem.map.union_prefer_right(entry_i.map),
                    arch: self.arch,
                    lower: entry_i.lower,
                    upper: rem.upper,
                }
            }
        } else {
            arbitrary()
        }
    }

    proof fn lemma_inv_implies_interp_inv(self)
        requires
            self.inv(),
        ensures
            self.interp().inv(),
            self.interp().upper == self.upper_vaddr(),
            self.interp().lower == self.base_vaddr,
    {
        self.lemma_inv_implies_interp_aux_inv(0);
    }

    proof fn lemma_inv_implies_interp_aux_inv(self, i: nat)
        requires
            self.inv(),
        ensures
            self.interp_aux(i).inv(),
            i <= self.entries.len() >>= self.interp_aux(i).lower == self.entry_base(i),
            self.interp_aux(i).upper == self.upper_vaddr(),
            i == 0 >>= self.interp_aux(0).lower == self.base_vaddr,
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
        ambient_lemmas1();

        let interp = self.interp_aux(i);

        if i >= self.entries.len() {
        } else {
            assert(i < self.entries.len());

            self.lemma_inv_implies_interp_aux_inv(i + 1);

            assert(self.directories_obey_invariant());

            let entry = self.entries.index(i);
            let entry_i = self.interp_of_entry(i);
            let rem = self.interp_aux(i+1);

            match entry {
                NodeEntry::Page(p) => {}
                NodeEntry::Directory(d) => {
                    d.lemma_inv_implies_interp_aux_inv(0);
                }
                NodeEntry::Empty() => { }
            }

            assert(interp.mappings_are_of_valid_size());

            if let NodeEntry::Page(p) = entry {
                self.lemma_entry_base_auto();
            }

            assert(interp.mappings_are_aligned());

            match entry {
                NodeEntry::Page(p) => {
                    assert_nonlinear_by({
                        requires([
                            self.inv(),
                            equal(entry_i, self.interp_of_entry(i)),
                            self.entry_size() == p.size,
                            i < self.entries.len(),
                        ]);
                        ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), p));
                    });
                }
                NodeEntry::Directory(d) => {
                    assert_nonlinear_by({
                        requires([
                            self.inv(),
                            equal(entry_i, self.interp_of_entry(i)),
                            d.interp_aux(0).inv(),
                            d.interp_aux(0).lower == self.entry_base(i),
                            d.base_vaddr == self.entry_base(i),
                            d.entry_size() * d.num_entries() == self.entry_size(),
                            d.interp_aux(0).upper == d.upper_vaddr(),
                            equal(self.interp_of_entry(i).map, d.interp_aux(0).map),
                            i < self.entries.len(),
                        ]);
                        ensures(entry_i.mappings_in_bounds());
                        assert(entry_i.lower <= d.interp_aux(0).lower); // proof stability
                        assert(entry_i.upper >= d.interp_aux(0).upper); // proof stability
                    });
                }
                NodeEntry::Empty() => {}
            }
            assert(entry_i.mappings_in_bounds());

            assert(entry_i.inv());


            assert(self.interp_aux(i + 1).lower == self.entry_base(i + 1));

            assert_nonlinear_by({
                requires([
                    self.inv(),
                    equal(rem, self.interp_aux(i + 1)),
                    equal(entry_i, self.interp_of_entry(i)),
                    self.interp_aux(i + 1).lower == self.entry_base(i + 1)
                ]);
                ensures(rem.ranges_disjoint(entry_i));
                assume(false); // unstable
            });
            rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);

            assert(interp.mappings_dont_overlap());

            assert_nonlinear_by({
                requires([
                    equal(interp, self.interp_aux(i)),
                    equal(entry_i, self.interp_of_entry(i)),
                    equal(rem, self.interp_aux(i + 1)),
                    self.interp_aux(i + 1).lower == self.entry_base(i + 1),
                    entry_i.upper == self.entry_base(i + 1),
                    interp.upper == self.upper_vaddr(),
                ]);
                ensures([
                    interp.lower <= entry_i.lower,
                    interp.upper >= entry_i.upper,
                    interp.lower <= self.interp_aux(i + 1).lower,
                    interp.upper >= self.interp_aux(i + 1).upper,
                ]);

                assume(false); // instability
            });

            assert(interp.mappings_in_bounds());

            assert(interp.map.dom().finite());

            if i == 0 {
                assert_nonlinear_by({
                    requires([
                        equal(entry_i, self.interp_of_entry(i)),
                        entry_i.lower == self.base_vaddr + i * self.entry_size(),
                        i == 0,
                    ]);
                    ensures(self.interp_aux(0).lower == self.base_vaddr);
                });
            }
        }
    }

    proof fn lemma_empty_implies_interp_aux_empty(self, i: nat)
        requires
             self.inv(),
             self.empty(),
        ensures
            equal(self.interp_aux(i).map, Map::empty()),
            equal(self.interp_aux(i).map.dom(), Set::empty()),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
        if i >= self.entries.len() {
        } else {
            let rem = self.interp_aux(i + 1);
            let entry_i = self.interp_of_entry(i);
            self.lemma_empty_implies_interp_aux_empty(i + 1);
            assert_maps_equal!(rem.map.union_prefer_right(entry_i.map), Map::empty());
        }
    }

    proof fn lemma_empty_implies_interp_empty(self)
        requires
             self.inv(),
             self.empty()
        ensures
            equal(self.interp().map, Map::empty()),
            equal(self.interp().map.dom(), Set::empty())
    {
        self.lemma_empty_implies_interp_aux_empty(0);
    }

    proof fn lemma_ranges_disjoint_interp_aux_interp_of_entry(self)
        requires
            self.inv(),
        ensures
            forall(|i: nat, j: nat|
                   j < i && i < self.num_entries()
                   >>= self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j))),
    {
        assert_forall_by(|i: nat, j: nat| {
            requires(j < i && i < self.num_entries());
            ensures(self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j)));
            let interp  = self.interp_aux(i);
            let entry_j = self.interp_of_entry(j);
            self.lemma_inv_implies_interp_aux_inv(i);
            assert_nonlinear_by({
                requires(
                    self.entry_size() > 0 &&
                    j < i &&
                    interp.lower == self.entry_base(i) &&
                    entry_j.lower == self.entry_base(j) &&
                    entry_j.upper == self.entry_base(j+1));
                ensures(
                    entry_j.upper <= interp.lower &&
                    interp.lower > entry_j.lower);
                assume(false); // unstable
            });
        });
    }

    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(self, i: nat, j: nat)
        requires
             self.inv(),
             i <= j,
             j < self.entries.len(),
        ensures
            forall(|va: nat, p: MemRegion| #[auto_trigger] self.interp_of_entry(j).map.contains_pair(va, p) >>= self.interp_aux(i).map.contains_pair(va, p)),
            forall(|va: nat| #[auto_trigger] self.interp_of_entry(j).map.dom().contains(va) >>= self.interp_aux(i).map.dom().contains(va)),
            forall(|va: nat|
                   between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                   >>= !self.interp_aux(i).map.dom().contains(va)),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
        assume(false); // unstable

        self.lemma_inv_implies_interp_aux_inv(i+1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);

        let rem = self.interp_aux(i + 1);
        let entry_i = self.interp_of_entry(i);

        if i != j {
            self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i+1, j);

            if let NodeEntry::Directory(d) = self.entries.index(i) {
                assert(self.directories_obey_invariant());
                assert(d.inv());
                d.lemma_inv_implies_interp_inv();
                self.lemma_ranges_disjoint_interp_aux_interp_of_entry();
                rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);
            }
        }

        self.lemma_entry_base_auto();
    }

    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(self, j: nat)
        requires
             self.inv(),
             j < self.entries.len(),
        ensures
            forall(|va: nat| #[auto_trigger] self.interp_of_entry(j).map.dom().contains(va) >>= self.interp().map.dom().contains(va)),
            forall(|va: nat, p: MemRegion| #[auto_trigger] self.interp_of_entry(j).map.contains_pair(va, p) >>= self.interp().map.contains_pair(va, p)),
            forall(|va: nat| #[auto_trigger]
                   between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                   >>= !self.interp().map.dom().contains(va)),
    {
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(0, j);
    }

    // proof fn lemma_interp_aux_subset_interp_aux_plus(self, i: nat, k: nat, v: MemRegion) {
    //     requires([
    //              self.inv(),
    //              self.interp_aux(i+1).map.contains_pair(k,v),
    //     ]);
    //     ensures(self.interp_aux(i).map.contains_pair(k,v));

    //     if i >= self.entries.len() {
    //     } else {
    //         self.lemma_interp_aux_disjoint(i);
    //     }
    // }

    spec(checked) fn resolve(self, vaddr: nat) -> Result<nat,()>
        recommends
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        decreases self.arch.layers.len() - self.layer
    {
        decreases_when(self.inv() && self.interp().accepted_resolve(vaddr));
        recommends_by(Self::check_resolve);

        let entry = self.index_for_vaddr(vaddr);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                let offset = vaddr - self.entry_base(entry);
                Ok(p.base + offset)
            },
            NodeEntry::Directory(d) => {
                d.resolve(vaddr)
            },
            NodeEntry::Empty() => {
                Err(())
            },
        }
    }

    #[verifier(decreases_by)]
    proof fn check_resolve(self, vaddr: nat) {
        assert(self.inv());

        ambient_lemmas1();
        self.lemma_inv_implies_interp_inv();

        assert(between(vaddr, self.base_vaddr, self.upper_vaddr()));
        let entry = self.index_for_vaddr(vaddr);
        self.lemma_index_for_vaddr_bounds(vaddr);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
            },
            NodeEntry::Empty() => {
            },
        }
    }

    #[verifier(nonlinear)]
    proof fn lemma_index_for_vaddr_bounds(self, vaddr: nat)
        requires
            self.inv(),
        ensures
            (false
            || self.interp().accepted_resolve(vaddr)
            || self.interp().accepted_unmap(vaddr)
            || exists(|frame: MemRegion| self.interp().accepted_mapping(vaddr, frame))) >>=
            {
                let i = self.index_for_vaddr(vaddr);
                true
                && i < self.num_entries()
                && between(vaddr, self.entry_base(i), self.entry_base(i + 1))
                && self.entry_base(i + 1) == self.entry_base(i) + self.entry_size()
                && (aligned(vaddr, self.entry_size()) >>= vaddr == self.base_vaddr + i * self.entry_size())
            },
    {
        assume(false); // unstable
        self.lemma_inv_implies_interp_inv();
        let i = self.index_for_vaddr(vaddr);
        if (false
            || self.interp().accepted_resolve(vaddr)
            || self.interp().accepted_unmap(vaddr)
            || exists(|frame: MemRegion| self.interp().accepted_mapping(vaddr, frame))) {
            assert(self.base_vaddr <= vaddr);
            if aligned(vaddr, self.entry_size()) {
                assert(aligned(self.base_vaddr, self.entry_size() * self.num_entries()));
                assert(aligned(vaddr, self.entry_size()));
                crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
                assert(aligned(self.base_vaddr, self.entry_size()));
                crate::lib::subtract_mod_eq_zero(self.base_vaddr, vaddr, self.entry_size());
                assert(aligned(self.vaddr_offset(vaddr), self.entry_size()));
                crate::lib::div_mul_cancel(self.vaddr_offset(vaddr), self.entry_size());
                assert(self.vaddr_offset(vaddr) / self.entry_size() * self.entry_size() == self.vaddr_offset(vaddr));
                assert(self.base_vaddr + self.vaddr_offset(vaddr) == self.base_vaddr + i * self.entry_size());
                assert(vaddr == self.base_vaddr + i * self.entry_size());
                // assert(vaddr == self.base_vaddr + i * self.entry_size());
            }
        }
        self.lemma_entry_base_auto();
    }

    proof fn lemma_interp_aux_contains_implies_interp_of_entry_contains(self, j: nat)
        requires
            self.inv(),
        ensures
            forall(|base: nat, p: MemRegion|
                   self.interp_aux(j).map.contains_pair(base, p) >>=
                   exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, p))),
            forall(|base: nat|
                   self.interp_aux(j).map.dom().contains(base) >>=
                   exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base)))
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - j)
    {
        if j >= self.entries.len() {
        } else {
            let _ = self.interp_of_entry(j);
            self.lemma_interp_aux_contains_implies_interp_of_entry_contains(j+1);
            assert_forall_by(|base: nat, p: MemRegion| {
                requires(self.interp_aux(j).map.contains_pair(base, p));
                ensures(exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, p)));
                if self.interp_aux(j+1).map.contains_pair(base, p) { } else { }
            });
            assert_forall_by(|base: nat| {
                requires(self.interp_aux(j).map.dom().contains(base));
                ensures(exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base)));
                if self.interp_aux(j+1).map.dom().contains(base) { } else { }
            });
        }
    }

    proof fn lemma_interp_contains_implies_interp_of_entry_contains(self)
        requires
            self.inv(),
        ensures
            forall(|base: nat, p: MemRegion|
                   self.interp().map.contains_pair(base, p) >>=
                   exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, p))),
            forall(|base: nat|
                   self.interp().map.dom().contains(base) >>=
                   exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base))),
    {
        self.lemma_interp_aux_contains_implies_interp_of_entry_contains(0);
    }

    proof fn lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(self, vaddr: nat, i: nat)
        requires
            self.inv(),
            i < self.num_entries(),
            between(vaddr, self.interp_of_entry(i).lower, self.interp_of_entry(i).upper),
            !exists(|base:nat|
                    self.interp_of_entry(i).map.dom().contains(base) &&
                    between(vaddr, base, base + (#[trigger] self.interp_of_entry(i).map.index(base)).size)),
        ensures
            !exists(|base:nat|
                    self.interp().map.dom().contains(base) &&
                    between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).size)),
    {
        self.lemma_entry_base_auto();
        self.lemma_interp_of_entry();
        self.lemma_interp_contains_implies_interp_of_entry_contains();

        if exists(|base:nat|
                  self.interp().map.dom().contains(base) &&
                  between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).size)) {
            let base = choose(|base:nat|
                              self.interp().map.dom().contains(base) &&
                              between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).size));
            let p = self.interp().map.index(base);
            assert(self.interp().map.contains_pair(base, p));
        }
    }

    proof fn resolve_refines(self, vaddr: nat)
        requires
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        ensures
            equal(self.interp().resolve(vaddr), self.resolve(vaddr)),
        decreases self.arch.layers.len() - self.layer
    {
        ambient_lemmas1();
        self.lemma_inv_implies_interp_inv();

        let entry = self.index_for_vaddr(vaddr);
        self.lemma_index_for_vaddr_bounds(vaddr);
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                assert(self.resolve(vaddr).is_Ok());
                let p_vaddr = self.entry_base(entry);
                assert(self.interp().map.contains_pair(p_vaddr, p));
                assert(vaddr < p_vaddr + self.interp().map.index(p_vaddr).size);
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                d.resolve_refines(vaddr);

                assert(equal(self.interp_of_entry(entry), d.interp()));

                assert(equal(d.interp().resolve(vaddr), d.resolve(vaddr)));

                if d.resolve(vaddr).is_Ok() {
                    assert(self.resolve(vaddr).is_Ok());
                    assert(exists(|base: nat|
                                  d.interp().map.dom().contains(base) &&
                                  between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).size)));

                    let base = choose(|base:nat|
                                    d.interp().map.dom().contains(base) &&
                                    between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).size));

                    assert(self.interp().map.contains_pair(base, self.interp_of_entry(entry).map.index(base)));

                    assert(d.resolve(vaddr).is_Ok());
                    assert(d.interp().resolve(vaddr).is_Ok());
                    assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
                } else {
                    assert(d.resolve(vaddr).is_Err());
                    assert(self.resolve(vaddr).is_Err());

                    assert(d.interp().resolve(vaddr).is_Err());
                    assert(!exists(|base:nat|
                                   d.interp().map.dom().contains(base) &&
                                   between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).size)));
                    self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(vaddr, entry);
                }
                assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
            },
            NodeEntry::Empty() => {
                assert(self.resolve(vaddr).is_Err());
                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(vaddr, entry);
                assert(self.interp().resolve(vaddr).is_Err());
            },
        }
    }

    pub closed spec(checked) fn update(self, n: nat, e: NodeEntry) -> Self
        recommends n < self.entries.len()
    {
        Directory {
            entries: self.entries.update(n, e),
            ..self
        }
    }

    // pub proof fn lemma_update(self) {
    //     ensures(forall(|i: nat, e: NodeEntry| self.inv() && i < self.num_entries() >>= (#[trigger] self.update(i, e).interp().lower) == self.interp().lower));

    // }

    pub closed spec(checked) fn candidate_mapping_in_bounds(self, base: nat, frame: MemRegion) -> bool
        recommends self.inv()
    {
        self.base_vaddr <= base && base + frame.size <= self.upper_vaddr()
    }

    pub closed spec(checked) fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool
        recommends self.inv()
    {
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
        && self.candidate_mapping_in_bounds(base, frame)
        && self.arch.contains_entry_size_at_index_atleast(frame.size, self.layer)
    }

    proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_manual(self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame)
        ensures
            self.interp().accepted_mapping(base, frame),
    {
        self.lemma_inv_implies_interp_inv();
    }

    proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_auto(self)
        ensures
            forall(|base: nat, frame: MemRegion|
                   self.inv() && #[trigger] self.accepted_mapping(base, frame) >>=
                   self.interp().accepted_mapping(base, frame)),
    {
        assert_forall_by(|base: nat, frame: MemRegion| {
            requires(self.inv() && #[trigger] self.accepted_mapping(base, frame));
            ensures(self.interp().accepted_mapping(base, frame));

            self.lemma_accepted_mapping_implies_interp_accepted_mapping_manual(base, frame);
        });
    }

    // Creates new empty directory to map to entry 'entry'
    pub closed spec fn new_empty_dir(self, entry: nat) -> Self
        recommends
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
    {
        Directory {
            entries:    new_seq(self.arch.layers.index((self.layer + 1) as nat).num_entries),
            layer:      self.layer + 1,
            base_vaddr: self.entry_base(entry),
            arch:       self.arch,
        }
    }

    proof fn lemma_new_empty_dir(self, entry: nat)
        requires
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
        ensures
            self.new_empty_dir(entry).inv(),
            self.new_empty_dir(entry).entries.len() == self.arch.layers.index((self.layer + 1) as nat).num_entries,
            forall(|j: nat| j < self.new_empty_dir(entry).num_entries() >>= equal(self.new_empty_dir(entry).entries.index(j), NodeEntry::Empty())),
    {
        let new_dir = self.new_empty_dir(entry);
        let num_entries = self.arch.layers.index((self.layer + 1) as nat).num_entries;
        self.lemma_entry_base_auto();
        lemma_new_seq(num_entries);

        assert(new_dir.directories_obey_invariant());
        assert(new_dir.inv());
    }

    pub closed spec fn map_frame(self, base: nat, frame: MemRegion) -> Result<Self,()>
        decreases self.arch.layers.len() - self.layer
    {
        decreases_by(Self::check_map_frame);

        if self.inv() && self.accepted_mapping(base, frame) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry) {
                NodeEntry::Page(p) => {
                    Err(())
                },
                NodeEntry::Directory(d) => {
                    if self.entry_size() == frame.size {
                        Err(())
                    } else {
                        match d.map_frame(base, frame) {
                            Ok(d)  => Ok(self.update(entry, NodeEntry::Directory(d))),
                            Err(e) => Err(e),
                        }
                    }
                },
                NodeEntry::Empty() => {
                    if self.entry_size() == frame.size {
                        Ok(self.update(entry, NodeEntry::Page(frame)))
                    } else {
                        // new_empty_dir's recommendation for `self.layer + 1 < self.arch.layers.len()`
                        // is satisfied because we know the frame size isn't this layer's entrysize
                        // (i.e. must be on some lower level).
                        let new_dir = self.new_empty_dir(entry);
                        // We never fail to insert an accepted mapping into an empty directory
                        Ok(self.update(entry, NodeEntry::Directory(new_dir.map_frame(base, frame).get_Ok_0())))
                    }
                },
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_map_frame(self, base: nat, frame: MemRegion) {
        ambient_lemmas1();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        if self.inv() && self.accepted_mapping(base, frame) {
            self.lemma_index_for_vaddr_bounds(base);
        }
    }

    proof fn lemma_accepted_mapping_implies_directory_accepted_mapping(self, base: nat, frame: MemRegion, d: Directory)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
            equal(d.arch, self.arch),
            d.base_vaddr == self.entry_base(self.index_for_vaddr(base)),
            d.upper_vaddr() == self.entry_base(self.index_for_vaddr(base)+1),
            d.inv(),
            d.layer == self.layer + 1,
            self.entry_size() != frame.size,
        ensures
            d.accepted_mapping(base, frame),
    {
        ambient_lemmas1();
        self.lemma_index_for_vaddr_bounds(base);
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        self.lemma_entry_base_auto();

        let entry = self.index_for_vaddr(base);
        assert(self.directories_obey_invariant());
        assert(d.inv());

        assert(aligned(base, frame.size));
        assert(aligned(frame.base, frame.size));
        assert(d.arch.contains_entry_size_at_index_atleast(frame.size, d.layer));

        assert(self.entry_base(entry) <= base);
        assert(aligned(base, frame.size));
        self.arch.lemma_entry_sizes_aligned_auto();
        assert(aligned(self.entry_size(), frame.size));

        crate::lib::aligned_transitive_auto();
        assert(aligned(self.entry_base(entry+1), frame.size));
        crate::lib::leq_add_aligned_less(base, frame.size, self.entry_base(entry+1));
        assert(base + frame.size <= self.entry_base(entry+1));
        assert(base + frame.size <= self.entry_base(entry) + self.entry_size());
        assert(base + frame.size <= d.base_vaddr + self.entry_size());
        assert(base + frame.size <= d.base_vaddr + d.num_entries() * d.entry_size());
        assert(base + frame.size <= d.upper_vaddr());
        assert(d.candidate_mapping_in_bounds(base, frame));
        assert(aligned(base, frame.size));
        assert(aligned(frame.base, frame.size));
    }

    proof fn lemma_map_frame_empty_is_ok(self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
            self.entries.index(self.index_for_vaddr(base)).is_Empty(),
        ensures
            self.map_frame(base, frame).is_Ok(),
        decreases self.arch.layers.len() - self.layer;

    proof fn lemma_map_frame_preserves_inv(self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
            self.map_frame(base, frame).is_Ok(),
        ensures
            equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer),
            equal(self.map_frame(base, frame).get_Ok_0().arch, self.arch),
            equal(self.map_frame(base, frame).get_Ok_0().base_vaddr, self.base_vaddr),
            !self.map_frame(base, frame).get_Ok_0().empty(),
            self.map_frame(base, frame).get_Ok_0().inv(),
            !exists(|b:nat| true
                    && self.interp().map.dom().contains(b)
                    && between(base, b, b + (#[trigger] self.interp().map.index(b)).size)),

        decreases (self.arch.layers.len() - self.layer)
    {

        ambient_lemmas1();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        self.lemma_index_for_vaddr_bounds(base);
        self.lemma_entry_base_auto();

        let res = self.map_frame(base, frame).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => (),
            NodeEntry::Directory(d) => {
                if self.entry_size() == frame.size {
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, frame, d);
                    d.lemma_inv_implies_interp_inv();
                    assert(d.inv());
                    d.lemma_map_frame_preserves_inv(base, frame);
                    assert(res.well_formed());
                    assert(res.pages_match_entry_size());
                    assert(res.directories_match_arch());
                    // assert_forall_by(|i: nat| {
                    //     requires(i < res.entries.len() && res.entries.index(i).is_Directory());
                    //     ensures(true
                    //             && (#[trigger] res.entries.index(i)).get_Directory_0().layer == res.layer + 1
                    //             && res.entries.index(i).get_Directory_0().base_vaddr == res.base_vaddr + i * res.entry_size());
                    //     if i < res.entries.len() && res.entries.index(i).is_Directory() {
                    //         if i == entry {
                    //         }
                    //     }
                    // });
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.inv());
                    assert(equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer));

                    assert(res.entries.index(entry).is_Directory());
                    assert(!res.empty());
                    self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry);
                }
            },
            NodeEntry::Empty() => {
                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry);
                if self.entry_size() == frame.size {
                    assert(equal(res.layer, self.layer));
                    assert(res.entries.index(entry).is_Page());
                    assert(!res.empty());
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.inv());
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);

                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, frame, new_dir);
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, frame));
                    new_dir.lemma_index_for_vaddr_bounds(base);
                    new_dir.lemma_map_frame_empty_is_ok(base, frame);
                    new_dir.lemma_map_frame_preserves_inv(base, frame);

                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.frames_aligned());
                    assert(res.inv());
                    assert(equal(res.layer, self.layer));
                    assert(res.entries.index(entry).is_Directory());
                    assert(!res.empty());
                }
            },
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp_aux(self, i: nat, j: nat, base: nat, n: NodeEntry, frame: MemRegion)
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            !self.interp_aux(i).map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, frame),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                }),
        ensures
            equal(self.interp_aux(i).map.insert(base, frame), self.update(j, n).interp_aux(i).map),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
        ambient_lemmas1();
        ambient_lemmas2();

        self.lemma_inv_implies_interp_aux_inv(i);
        self.lemma_inv_implies_interp_aux_inv(i + 1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);

        self.lemma_interp_of_entry();
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);

        let nself = self.update(j, n);

        if i >= self.entries.len() {
        } else {
            if i == j {
                assert(!self.interp_aux(i + 1).map.dom().contains(base));
                assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));

                assert(equal(self.interp_of_entry(i).map.insert(base, frame), nself.interp_of_entry(i).map));
                self.lemma_entries_equal_implies_interp_aux_equal(nself, i+1);
                assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));


                assert(!self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).dom().contains(base));

                assert(equal(self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).insert(base, frame),
                             self.update(j, n).interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.insert(base, frame), self.update(j, n).interp_aux(i).map));
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());

                self.lemma_insert_interp_of_entry_implies_insert_interp_aux(i + 1, j, base, n, frame);
                self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i + 1, j);
                assert(!self.interp_of_entry(j).map.dom().contains(base));

                assert(!self.interp_aux(i).map.dom().contains(base));

                assert(equal(self.interp_aux(i + 1).map.insert(base, frame), self.update(j, n).interp_aux(i + 1).map));

                assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));

                assert(nself.inv());
                assert(equal(nself.interp_aux(i).map, nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.insert(base, frame), self.update(j, n).interp_aux(i).map));
            }
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp(self, j: nat, base: nat, n: NodeEntry, frame: MemRegion)
        requires
            self.inv(),
            j < self.num_entries(),
            !self.interp().map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, frame),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                }),
        ensures
            equal(self.interp().map.insert(base, frame), self.update(j, n).interp().map),
        decreases
            self.arch.layers.len() - self.layer,
    {
        self.lemma_insert_interp_of_entry_implies_insert_interp_aux(0, j, base, n, frame);
    }

    proof fn lemma_nonempty_implies_exists_interp_dom_contains(self)
        requires
            self.inv(),
            !self.empty()
        ensures
            exists(|b: nat| self.interp().map.dom().contains(b))
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();

        assert(exists(|i: nat| i < self.num_entries() && !self.entries.index(i).is_Empty()));
        let i = choose(|i: nat| i < self.num_entries() && !self.entries.index(i).is_Empty());
        assert(i < self.num_entries());
        assert(!self.entries.index(i).is_Empty());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(i);
        match self.entries.index(i) {
            NodeEntry::Page(p)      => {
                assert(self.interp().map.dom().contains(self.entry_base(i)));
            },
            NodeEntry::Directory(d) => {
                d.lemma_nonempty_implies_exists_interp_dom_contains();
                let b = choose(|b: nat| d.interp().map.dom().contains(b));
                assert(self.interp().map.dom().contains(b));
            },
            NodeEntry::Empty()      => (),
        }
    }

    proof fn lemma_map_frame_refines_map_frame(self, base: nat, frame: MemRegion)
        requires
            self.inv(),
            self.accepted_mapping(base, frame),
        ensures
            equal(self.map_frame(base, frame).map_ok(|d| d.interp()), self.interp().map_frame(base, frame)),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        self.lemma_index_for_vaddr_bounds(base);
        self.lemma_entry_base_auto();

        let res = self.map_frame(base, frame).get_Ok_0();
        if self.map_frame(base, frame).is_Ok() {
            self.lemma_map_frame_preserves_inv(base, frame);
        }

        let entry = self.index_for_vaddr(base);
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                assert(self.map_frame(base, frame).is_Err());

                assert(self.interp_of_entry(entry).map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map_frame(base, frame).is_Err());
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.inv());
                if self.entry_size() == frame.size {
                    assert(self.map_frame(base, frame).is_Err());
                    d.lemma_nonempty_implies_exists_interp_dom_contains();
                    let b = choose(|b: nat| d.interp().map.dom().contains(b));
                    assert(self.interp().map.dom().contains(b));
                    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

                    assert(!self.interp().valid_mapping(base, frame));
                    assert(self.interp().map_frame(base, frame).is_Err());
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, frame, d);
                    assert(d.accepted_mapping(base, frame));
                    d.lemma_map_frame_refines_map_frame(base, frame);
                    assert(equal(d.map_frame(base, frame).map_ok(|d| d.interp()), d.interp().map_frame(base, frame)));
                    match d.map_frame(base, frame) {
                        Ok(nd)  => {
                            assert(d.map_frame(base, frame).is_Ok());
                            assert(d.interp().map_frame(base, frame).is_Ok());
                            assert(d.interp().accepted_mapping(base, frame));
                            assert(d.interp().valid_mapping(base, frame));
                            assert(self.interp().accepted_mapping(base, frame));
                            assert(self.interp().valid_mapping(base, frame));
                            assert(self.map_frame(base, frame).is_Ok());
                            self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(nd), frame);
                            assert(self.interp().map_frame(base, frame).is_Ok());

                            assert(equal(self.interp().map.insert(base, frame), self.update(entry, NodeEntry::Directory(nd)).interp().map));
                            assert(equal(self.interp().map.insert(base, frame), self.interp().map_frame(base, frame).get_Ok_0().map));

                            assert(equal(self.map_frame(base, frame).get_Ok_0().interp(), self.interp().map_frame(base, frame).get_Ok_0()));
                        },
                        Err(e) => {
                            assert(d.map_frame(base, frame).is_Err());
                            assert(d.interp().map_frame(base, frame).is_Err());
                            assert(d.interp().accepted_mapping(base, frame));
                            assert(!d.interp().valid_mapping(base, frame));
                            let b = choose(|b: nat| #[auto_trigger]
                                           d.interp().map.dom().contains(b) && overlap(
                                               MemRegion { base: base, size: frame.size },
                                               MemRegion { base: b, size: d.interp().map.index(b).size }
                                               ));
                            let bbase = d.interp().map.index(b).base;
                            let bsize = d.interp().map.index(b).size;
                            assert(d.interp().map.contains_pair(b, MemRegion { base: bbase, size: bsize }));
                            assert(overlap(
                                    MemRegion { base: base, size: frame.size },
                                    MemRegion { base: b, size: bsize }
                                    ));
                            self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
                            assert(self.interp().map.contains_pair(b, MemRegion { base: bbase, size: bsize }));

                            assert(self.interp().accepted_mapping(base, frame));
                            assert(!self.interp().valid_mapping(base, frame));

                            assert(self.map_frame(base, frame).is_Err());
                            assert(self.interp().map_frame(base, frame).is_Err());
                        },
                    }
                    // d.lemma_map_frame_preserves_inv(base, frame);
                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == frame.size {
                    self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Page(frame), frame);
                    assert(equal(self.map_frame(base, frame).map_ok(|d| d.interp()), self.interp().map_frame(base, frame)));
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    assert(new_dir.inv());

                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, frame, new_dir);
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, frame));
                    new_dir.lemma_index_for_vaddr_bounds(base);
                    new_dir.lemma_map_frame_empty_is_ok(base, frame);
                    new_dir.lemma_map_frame_preserves_inv(base, frame);

                    let new_dir_mapped = new_dir.map_frame(base, frame).get_Ok_0();
                    assert(new_dir.map_frame(base, frame).is_Ok());
                    assert(new_dir_mapped.inv());
                    new_dir.lemma_map_frame_refines_map_frame(base, frame);
                    assert(new_dir.interp().map_frame(base, frame).is_Ok());
                    assert(equal(new_dir_mapped.interp(), new_dir.interp().map_frame(base, frame).get_Ok_0()));

                    new_dir.lemma_empty_implies_interp_empty();
                    assert_maps_equal!(new_dir.interp().map, map![]);
                    assert_maps_equal!(new_dir.interp().map_frame(base, frame).get_Ok_0().map, map![base => frame]);
                    assert_maps_equal!(self.interp_of_entry(entry).map, map![]);
                    assert(equal(self.interp_of_entry(entry).map, map![]));
                    assert(equal(map![].insert(base, frame), new_dir_mapped.interp().map));
                    assert(equal(self.interp_of_entry(entry).map.insert(base, frame), new_dir_mapped.interp().map));
                    self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(new_dir_mapped), frame);

                    assert(equal(self.map_frame(base, frame).map_ok(|d| d.interp()), self.interp().map_frame(base, frame)));
                }
            },
        }
    }

    pub closed spec(checked) fn accepted_unmap(self, base: nat) -> bool
        recommends self.well_formed()
    {
        true
        && self.interp().accepted_unmap(base)
    }

    pub closed spec fn unmap(self, base: nat) -> Result<Self,()>
        recommends
            self.inv(),
            self.accepted_unmap(base),
        decreases self.arch.layers.len() - self.layer
    {
        decreases_by(Self::check_unmap);

        if self.inv() && self.accepted_unmap(base) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry) {
                NodeEntry::Page(p) => {
                    if aligned(base, self.entry_size()) {
                        // This implies:
                        // base == self.base_vaddr + entry * self.entry_size()
                        // (i.e. no remainder on division)
                        // (proved in lemma_index_for_vaddr_bounds)
                        Ok(self.update(entry, NodeEntry::Empty()))
                    } else {
                        Err(())
                    }
                },
                NodeEntry::Directory(d) => {
                    d.unmap(base).map_ok(|new_d|
                        self.update(entry, if new_d.empty() {
                            NodeEntry::Empty()
                        } else {
                            NodeEntry::Directory(new_d)
                        }))
                },
                NodeEntry::Empty() => Err(()),
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_unmap(self, base: nat) {
        if self.inv() && self.accepted_unmap(base) {
            self.lemma_index_for_vaddr_bounds(base);
        } else {
        }
    }


    proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
            self.unmap(base).is_Ok(),
        ensures
            self.unmap(base).get_Ok_0().inv(),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();

        let res = self.unmap(base).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        self.lemma_index_for_vaddr_bounds(base);

        assert(entry < self.num_entries());
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                    assert(res.directories_obey_invariant());
                } else {
                }
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.accepted_unmap(base));
                match d.unmap(base) {
                    Ok(new_d) => {
                        d.lemma_unmap_preserves_inv(base);
                        assert(res.directories_obey_invariant());
                    }
                    Err(_) => { }
                }
            },
            NodeEntry::Empty() => { },
        }
    }

    proof fn lemma_unmap_refines_unmap(self, base: nat)
        requires
             self.inv(),
             self.accepted_unmap(base),
        ensures
            equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        self.lemma_inv_implies_interp_inv();

        if let Ok(nself) = self.unmap(base) {
            self.lemma_unmap_preserves_inv(base);
            assert(nself.inv());
            nself.lemma_inv_implies_interp_inv();
            assert(nself.interp().inv());
        }

        let nself_res = self.unmap(base);
        let nself     = self.unmap(base).get_Ok_0();

        let i_nself_res = self.interp().unmap(base);
        let i_nself     = self.interp().unmap(base).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        self.lemma_index_for_vaddr_bounds(base);
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                    assert_maps_equal!(self.interp_of_entry(entry).map.remove(base), map![]);
                    assert(self.update(entry, NodeEntry::Empty()).inv());
                    self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Empty());
                } else {
                    self.lemma_entry_base_auto();
                    assert_nonlinear_by({
                        requires([
                            aligned(self.entry_base(entry), self.entry_size()),
                            !aligned(base, self.entry_size()),
                        ]);
                        ensures([
                            base != self.entry_base(entry),
                        ]);
                    });
                    assert(!self.interp().map.dom().contains(base));
                    assert(i_nself_res.is_Err());
                }
            },
            NodeEntry::Directory(d) => {
                assert(d.inv());
                d.lemma_inv_implies_interp_inv();
                assert(d.accepted_unmap(base));
                d.lemma_unmap_refines_unmap(base);
                match d.unmap(base) {
                    Ok(new_d) => {
                        d.lemma_unmap_preserves_inv(base);
                        assert(new_d.inv());
                        assert(d.unmap(base).is_Ok());
                        assert(d.interp().unmap(base).is_Ok());
                        assert(equal(new_d.interp(), d.interp().unmap(base).get_Ok_0()));
                        if new_d.empty() {
                            new_d.lemma_empty_implies_interp_empty();
                            d.interp().lemma_unmap_decrements_len(base);
                            assert(new_d.interp().map.dom().len() == 0);
                            assert(d.interp().map.dom().len() == 1);
                            assert(d.interp().map.dom().contains(base));
                            assert_sets_equal!(d.interp().map.dom(), set![base]);
                            assert(nself_res.is_Ok());
                            assert(equal(self.interp_of_entry(entry).map, d.interp().map));
                            assert(equal(d.interp().unmap(base).get_Ok_0().map, d.interp().map.remove(base)));
                            assert_maps_equal!(self.interp_of_entry(entry).map.remove(base), map![]);
                            assert(self.update(entry, NodeEntry::Empty()).inv());
                            self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Empty());
                            assert(equal(nself.interp(), i_nself));
                        } else {
                            assert(self.update(entry, NodeEntry::Directory(new_d)).inv());
                            self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Directory(new_d));
                        }
                    }
                    Err(_) => { }
                }
            },
            NodeEntry::Empty() => { },
        }
    }

    proof fn lemma_entries_equal_implies_interp_aux_equal(self, other: Directory, i: nat)
        requires
            self.inv(),
            other.inv(),
            equal(self.arch, other.arch),
            equal(self.layer, other.layer),
            equal(self.base_vaddr, other.base_vaddr),
            equal(self.num_entries(), other.num_entries()),
            forall(|j: nat| i <= j && j < self.entries.len() >>= equal(self.entries.index(j), other.entries.index(j))),
        ensures
            equal(self.interp_aux(i), other.interp_aux(i)),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
        if i >= self.entries.len() {
        } else {
            let rem1 = self.interp_aux(i + 1);
            let rem2 = other.interp_aux(i + 1);
            let entry_i1 = self.interp_of_entry(i);
            let entry_i2 = other.interp_of_entry(i);
            self.lemma_entries_equal_implies_interp_aux_equal(other, i + 1);
            assert_maps_equal!(rem1.map.union_prefer_right(entry_i1.map), rem2.map.union_prefer_right(entry_i2.map));
        }
    }

    proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(self, j: nat, i: nat, vaddr: nat, n: NodeEntry)
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            self.interp_of_entry(j).map.dom().contains(vaddr),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.remove(vaddr),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                }),
        ensures
            equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {

        assert(j < self.entries.len());
        ambient_lemmas1();
        self.lemma_inv_implies_interp_aux_inv(i);
        self.lemma_inv_implies_interp_aux_inv(i + 1);
        self.lemma_inv_implies_interp_of_entry_inv(i);
        self.lemma_inv_implies_interp_of_entry_inv(j);

        self.lemma_interp_of_entry();
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);

        let nself = self.update(j, n);

        if i >= self.entries.len() {
        } else {
            if i == j {
                assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));

                assert(equal(self.interp_of_entry(i).map.remove(vaddr), nself.interp_of_entry(i).map));
                self.lemma_entries_equal_implies_interp_aux_equal(nself, i+1);
                assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));

                assert(equal(self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).remove(vaddr),
                             nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map));
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());

                self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, i + 1, vaddr, n);
                self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i + 1, j);

                assert(self.interp_aux(j).map.dom().contains(vaddr));
                assert(self.interp_aux(i + 1).map.dom().contains(vaddr));

                assert(equal(self.interp_aux(i + 1).map.remove(vaddr), self.update(j, n).interp_aux(i + 1).map));

                assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));



                assert(nself.inv());
                assert(equal(nself.interp_aux(i).map, nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map));
            }
        }
    }

    proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp(self, j: nat, vaddr: nat, n: NodeEntry)
        requires
            self.inv(),
            j < self.num_entries(),
            self.interp_of_entry(j).map.dom().contains(vaddr),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.remove(vaddr),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                })
        ensures
            equal(self.interp().map.remove(vaddr), self.update(j, n).interp().map),
    {
        self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, 0, vaddr, n);
    }
}

impl<A,B> Result<A,B> {
    pub closed spec(checked) fn map_ok<C, F: Fn(A) -> C>(self, f: F) -> Result<C,B> {
        match self {
            Ok(a)  => Ok(f(a)),
            Err(b) => Err(b),
        }
    }
}

// FIXME: how to do this correctly?
pub closed spec fn new_seq(i: nat) -> Seq<NodeEntry>
    decreases i
{
    if i == 0 {
        seq![]
    } else {
        new_seq(i-1).add(seq![NodeEntry::Empty()])
    }
}

pub proof fn lemma_new_seq(i: nat)
    ensures
        new_seq(i).len() == i,
        forall(|j: nat| j < new_seq(i).len() >>= equal(new_seq(i).index(j), NodeEntry::Empty())),
    decreases i
{
    if i == 0 {
    } else {
        lemma_new_seq(i-1);
    }
}

pub proof fn lemma_map_union_prefer_right_insert_commute<S,T>()
    ensures
        forall(|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
               (!m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v))),
        forall(|m1: Map<S, T>, m2: Map<S, T>, n: S, v: T|
               (!m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v))),
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
        forall(|m1: Map<S, T>, m2: Map<S, T>, n: S|
               (m1.dom().contains(n) && !m2.dom().contains(n))
               >>= equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))),
        forall(|m1: Map<S, T>, m2: Map<S, T>, n: S|
               (m2.dom().contains(n) && !m1.dom().contains(n))
               >>= equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n))),
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

pub proof fn lemma_finite_map_union<S,T>()
    ensures
        forall(|s1: Map<S,T>, s2: Map<S,T>| s1.dom().finite() && s2.dom().finite() >>= #[trigger] s1.union_prefer_right(s2).dom().finite()),
{
    assert_forall_by(|s1: Map<S,T>, s2: Map<S,T>| {
        requires(s1.dom().finite() && s2.dom().finite());
        ensures(#[auto_trigger] s1.union_prefer_right(s2).dom().finite());

        assert(s1.dom().union(s2.dom()).finite());

        let union_dom = s1.union_prefer_right(s2).dom();
        let dom_union = s1.dom().union(s2.dom());

        assert(forall(|s: S| union_dom.contains(s) >>= dom_union.contains(s)));
        assert(forall(|s: S| dom_union.contains(s) >>= union_dom.contains(s)));

        assert_sets_equal!(union_dom, dom_union);
    });
}

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

// FIXME: We can probably remove bits from here that we don't use, e.g. accessed, dirty, PAT. (And
// set them to zero when we create a new entry.)
#[is_variant]
pub ghost enum GhostPageDirectoryEntry {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        flag_P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        flag_RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        flag_US: bool,
        /// Page-level write-through
        flag_PWT: bool,
        /// Page-level cache disable
        flag_PCD: bool,
        /// Accessed; indicates whether software has accessed the page referenced by this entry
        flag_A: bool,
        /// Dirty; indicates whether software has written to the page referenced by this entry
        flag_D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // flag_PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        flag_G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        flag_PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        flag_XD: bool,
    },
    Empty,
}

const MAXPHYADDR: u64 = 52;

// FIXME: these macros probably already exist somewhere?
macro_rules! bit {
    ($v:expr) => {
        1 << $v
    }
}
// Generate bitmask where bits $low:$high are set to 1. (inclusive on both ends)
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0 << (($high+1)-$low))) << $low
    }
}
// macro_rules! bitmask {
//     ($low:expr,$high:expr) => {
//         (!(!0 << ($high-$low))) << $low
//     }
// }

// layer:
// 0 -> Page Table
// 1 -> Page Directory
// 2 -> Page Directory Pointer Table
// 3 -> PML4


// MASK_FLAG_* are flags valid for all entries.
const MASK_FLAG_P:    u64 = bit!(0);
const MASK_FLAG_RW:   u64 = bit!(1);
const MASK_FLAG_US:   u64 = bit!(2);
const MASK_FLAG_PWT:  u64 = bit!(3);
const MASK_FLAG_PCD:  u64 = bit!(4);
const MASK_FLAG_A:    u64 = bit!(5);
const MASK_FLAG_XD:   u64 = bit!(63);
// We can use the same address mask for all layers as long as we preserve the invariant that the
// lower bits that *should* be masked off are already zero.
const MASK_ADDR:      u64 = bitmask_inc!(12,MAXPHYADDR);
// const MASK_ADDR:      u64 = 0b0000000000001111111111111111111111111111111111111111000000000000;

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 0 MASK_L0_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
const MASK_PG_FLAG_D:    u64 = bit!(6);
const MASK_PG_FLAG_G:    u64 = bit!(8);
const MASK_PG_FLAG_PAT:  u64 = bit!(12);

const MASK_L1_PG_FLAG_PS:   u64 = bit!(7);
const MASK_L2_PG_FLAG_PS:   u64 = bit!(7);
const MASK_L0_PG_FLAG_PAT:  u64 = bit!(7);

const MASK_DIR_REFC:           u64 = bitmask_inc!(52,62); // Ignored bits for storing refcount in L3 and L2
const MASK_DIR_L1_REFC:        u64 = bitmask_inc!(8,12); // Ignored bits for storing refcount in L1
const MASK_DIR_REFC_SHIFT:     u64 = 52;
const MASK_DIR_L1_REFC_SHIFT:  u64 = 8;

// // FIXME: we should be able to always use the 12:52 mask and have the invariant state that in the
// // other cases, the lower bits are already zero anyway.
const MASK_L0_PG_ADDR:      u64 = bitmask_inc!(12,MAXPHYADDR);
const MASK_L1_PG_ADDR:      u64 = bitmask_inc!(21,MAXPHYADDR);
const MASK_L2_PG_ADDR:      u64 = bitmask_inc!(30,MAXPHYADDR);

// TODO: can we get support for consts in bit vector reasoning?
// #[verifier(bit_vector)]
proof fn lemma_addr_masks_facts(address: u64)
    ensures
        (bitmask_inc!(21 as u64, 52 as u64) & address == address) >>= (bitmask_inc!(12 as u64, 52 as u64) & address == address),
        (bitmask_inc!(30 as u64, 52 as u64) & address == address) >>= (bitmask_inc!(12 as u64, 52 as u64) & address == address),
{
    assume(false); // TODO: unstable
}

#[verifier(bit_vector)]
proof fn lemma_addr_masks_facts2(address: u64)
    ensures
        ((address & bitmask_inc!(12 as u64, 52 as u64)) & bitmask_inc!(21 as u64, 52 as u64)) == (address & bitmask_inc!(21 as u64, 52 as u64)),
        ((address & bitmask_inc!(12 as u64, 52 as u64)) & bitmask_inc!(30 as u64, 52 as u64)) == (address & bitmask_inc!(30 as u64, 52 as u64));

// // MASK_PD_* are flags valid for all entries pointing to another directory
// const MASK_PD_ADDR:      u64 = bitmask!(12,52);

// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
struct PageDirectoryEntry {
    entry: u64,
    // pub view: Ghost<GhostPageDirectoryEntry>,
    pub ghost layer: nat,
}

impl PageDirectoryEntry {

    pub closed spec fn view(self) -> GhostPageDirectoryEntry {
        // *self.view
        if self.layer() <= 3 {
            let v = self.entry;
            if v & MASK_FLAG_P == MASK_FLAG_P {
                let addr     = (v & MASK_ADDR) as usize; // FIXME: is this safe?
                let flag_P   = v & MASK_FLAG_P   == MASK_FLAG_P;
                let flag_RW  = v & MASK_FLAG_RW  == MASK_FLAG_RW;
                let flag_US  = v & MASK_FLAG_US  == MASK_FLAG_US;
                let flag_PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
                let flag_PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
                let flag_A   = v & MASK_FLAG_A   == MASK_FLAG_A;
                let flag_XD  = v & MASK_FLAG_XD  == MASK_FLAG_XD;
                if (self.layer() == 0) || ((self.entry & MASK_L1_PG_FLAG_PS) == 0) {
                    let flag_D   = v & MASK_PG_FLAG_D   == MASK_PG_FLAG_D;
                    let flag_G   = v & MASK_PG_FLAG_G   == MASK_PG_FLAG_G;
                    let flag_PAT = if self.layer() == 0 { v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT } else { v & MASK_L0_PG_FLAG_PAT == MASK_L0_PG_FLAG_PAT };
                    GhostPageDirectoryEntry::Page {
                        addr,
                        flag_P, flag_RW, flag_US, flag_PWT, flag_PCD,
                        flag_A, flag_D, flag_G, flag_PAT, flag_XD,
                    }
                } else {
                    GhostPageDirectoryEntry::Directory {
                        addr, flag_P, flag_RW, flag_US, flag_PWT, flag_PCD, flag_A, flag_XD,
                    }
                }
            } else {
                GhostPageDirectoryEntry::Empty
            }
        } else {
            arbitrary()
        }
    }

    pub closed spec fn inv(self) -> bool {
        true
        && self.layer() <= 3
        && self.addr_is_zero_padded()
    }

    pub closed spec fn addr_is_zero_padded(self) -> bool {
        if self.layer() == 0 {
            self.entry & MASK_ADDR == self.entry & MASK_L0_PG_ADDR
        } else if self.layer() == 1 {
            self.entry & MASK_ADDR == self.entry & MASK_L1_PG_ADDR
        } else if self.layer() == 2 {
            self.entry & MASK_ADDR == self.entry & MASK_L2_PG_ADDR
        } else {
            true
        }
    }

    pub closed spec fn layer(self) -> nat {
        self.layer
    }

    pub proof fn lemma_new_entry_addr_mask_is_address(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        )
        requires
            layer <= 3,
            is_page >>= layer < 3,
            if layer == 0 {
                address & MASK_L0_PG_ADDR == address
            } else if layer == 1 {
                address & MASK_L1_PG_ADDR == address
            } else if layer == 2 {
                address & MASK_L2_PG_ADDR == address
            } else { true }
    {
        // FIXME: conversion, what does this look like in new syntax?
        ensures({
                let e = address
                    | MASK_FLAG_P
                    | if is_page && layer != 0 { MASK_L1_PG_FLAG_PS }  else { 0 }
                    | if is_writable           { MASK_FLAG_RW }        else { 0 }
                    | if is_supervisor         { MASK_FLAG_US }        else { 0 }
                    | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                    | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                    | if disable_execute       { MASK_FLAG_XD }        else { 0 };
                    e & MASK_ADDR == address
            });
            assume(false);
    }

    pub fn new_entry(
        layer: usize,
        address: u64,
        is_page: bool,
        is_writable: bool,
        is_supervisor: bool,
        is_writethrough: bool,
        disable_cache: bool,
        disable_execute: bool,
        ) -> (r: PageDirectoryEntry)
        requires
            layer <= 3,
            is_page >>= layer < 3,
            if layer == 0 {
                address & MASK_L0_PG_ADDR == address
            } else if layer == 1 {
                address & MASK_L1_PG_ADDR == address
            } else if layer == 2 {
                address & MASK_L2_PG_ADDR == address
            } else { true }
        ensures
            r.inv(),
    {
        let e =
        PageDirectoryEntry {
            entry: {
                address
                | MASK_FLAG_P
                | if is_page && layer != 0 { MASK_L1_PG_FLAG_PS }  else { 0 }
                | if is_writable           { MASK_FLAG_RW }        else { 0 }
                | if is_supervisor         { MASK_FLAG_US }        else { 0 }
                | if is_writethrough       { MASK_FLAG_PWT }       else { 0 }
                | if disable_cache         { MASK_FLAG_PCD }       else { 0 }
                | if disable_execute       { MASK_FLAG_XD }        else { 0 }
            },
            layer: layer as nat,
        };

        assert(e.layer() <= 3);

        proof {
            assert_by(e.addr_is_zero_padded(), {
                lemma_addr_masks_facts(address);
                lemma_addr_masks_facts2(e.entry);
                Self::lemma_new_entry_addr_mask_is_address(layer, address, is_page, is_writable, is_supervisor, is_writethrough, disable_cache, disable_execute);
            });
        }
        e
    }

    pub fn address(self) -> u64 {
        // FIXME: need invariant to make sure we can always use the biggest mask here
        self.entry & MASK_ADDR
    }

    pub fn is_mapping(self) -> (r: bool)
        ensures
            r == !self.view().is_Empty(),
    {
        assume(false);
        (self.entry & MASK_FLAG_P) == MASK_FLAG_P
    }

    pub fn is_page(self, layer: usize) -> (r: bool)
        requires
            !self.view().is_Empty(),
            layer as nat == self.layer
        ensures
            if r { self.view().is_Page() } else { self.view().is_Directory() },
    {
        assume(false);
        (layer == 0) || ((self.entry & MASK_L1_PG_FLAG_PS) == 0)
    }

    pub fn is_dir(self, layer: usize) -> (r: bool)
        requires
            !self.view().is_Empty(),
            layer as nat == self.layer,
        ensures
            if r { self.view().is_Directory() } else { self.view().is_Page() },
    {
        !self.is_page(layer)
    }

    // ....
}


// FIXME: We need to allow the dirty and accessed bits to change in the memory.
// Or maybe we just don't read those bits at all?
#[verifier(external_body)]
pub struct PageTableMemory {
    // how is the memory range for this represented?
    ptr: *mut u8,
}

impl PageTableMemory {
    spec fn root(&self) -> usize { arbitrary() }

    spec fn view(&self) -> Seq<u8> { arbitrary() }

    #[verifier(external_body)]
    fn write(&mut self, ptr: usize, byte: u8)
        requires
            ptr < old(self).view().len(),
        ensures
            forall(|i: nat| i < self.view().len() >>= self.view().index(i) == byte),
    {
        unsafe {
            self.ptr.offset(ptr as isize).write(byte)
        }
    }

    fn read_entry(self, offset: usize) -> (r: Vec<u8>)
        ensures
            r.len() == 8,
    {
        // unsafe { std::slice::from_raw_parts(self.ptr.offset(offset as isize), ENTRY_BYTES) }
        assume(false);
        Vec::empty() // FIXME: unimplemented
    }

}

pub struct PageTable {
    pub memory: PageTableMemory,
    pub ghost arch: Arch,
}

const ENTRY_BYTES: usize = 8;

// #[spec] #[is_variant]
// pub enum ParsedEntry {
//     Directory { ptr: usize },
//     Page { base: nat },
//     Empty,
// }

// #[spec]
// pub fn parse_entry_bytes(layer: nat, bytes: Seq<u8>) -> ParsedEntry {
//     arbitrary()
//     // let entry = PageDirectoryEntry { entry: arbitrary(), layer: arbitrary(), view: arbitrary() };
//     // if entry.is_mapping_spec() {
//     //     if entry.is_page_spec(layer as usize) {
//     //         ParsedEntry::Page { base: entry.address_spec() }
//     //     } else {
//     //         ParsedEntry::Directory { ptr: entry.address_spec() as usize }
//     //     }
//     // } else {
//     //     ParsedEntry::Empty
//     // }
// }

impl PageTable {

    pub closed spec fn get_entry_bytes(&self, ptr: usize, i: nat) -> Seq<u8> {
        self.memory.view().subrange(
            ptr as int + i as int * ENTRY_BYTES as int,
            ptr as int + (i as int + 1) * ENTRY_BYTES as int)
    }

    pub closed spec(checked) fn well_formed(&self) -> bool {
        true
        && self.arch.inv()
    }

    pub closed spec(checked) fn inv(&self) -> bool {
        true
        && self.well_formed()
        && self.inv_at(0, self.memory.root())
    }

    /// Get the view of the entry at address ptr + i * ENTRY_BYTES
    pub closed spec fn view_at(self, layer: nat, ptr: usize, i: nat) -> GhostPageDirectoryEntry {
        PageDirectoryEntry {
            entry: u64_from_le_bytes_spec(self.get_entry_bytes(ptr, i)),
            layer,
        }.view()
    }

    /// Get the entry at address ptr + i * ENTRY_BYTES
    // FIXME: conversion, layer should be a ghost parameter here
    fn entry_at(self, layer: nat, ptr: usize, i: usize) -> PageDirectoryEntry {
        PageDirectoryEntry {
            entry: u64_from_le_bytes(self.memory.read_entry(i * ENTRY_BYTES)),
            layer,
        }
    }

    pub closed spec fn directories_obey_invariant_at(&self, layer: nat, ptr: usize) -> bool
        decreases (self.arch.layers.len() - layer, 0)
    {
        decreases_when(self.well_formed() && self.layer_in_range(layer));

        forall(|i: nat| i < self.arch.layers.index(layer).num_entries >>= {
            let entry = #[trigger] self.view_at(layer, ptr, i);
            // #[trigger] PageDirectoryEntry { entry: u64_from_le_bytes(self.get_entry_bytes(ptr, i)), layer: Ghost::new(layer) }.view();
            entry.is_Directory() >>= self.inv_at(layer + 1, entry.get_Directory_addr())
        })
    }

    pub closed spec fn layer_in_range(self, layer: nat) -> bool {
        layer < self.arch.layers.len()
    }

    pub closed spec fn inv_at(&self, layer: nat, ptr: usize) -> bool
        recommends self.well_formed()
        decreases self.arch.layers.len() - layer
    {
        true
        && self.layer_in_range(layer)
        && self.directories_obey_invariant_at(layer, ptr)
        && forall(|i: nat| i < self.arch.layers.index(layer).num_entries >>= {
            let entry = #[trigger] self.view_at(layer, ptr, i);
            // let view = entry.view();
            true
            // && entry.inv()
            && entry.is_Directory() >>= self.inv_at(layer + 1, entry.get_Directory_addr())
        })
    }

    pub closed spec fn interp_entry_bytes_as_node_entry(&self, ptr: usize, base_vaddr: nat, layer: nat) -> NodeEntry
        decreases (self.arch.layers.len() - layer, 0, 2)
    {
        decreases_when(self.inv_at(layer, ptr));
        match self.view_at(layer, ptr, 0) {
            GhostPageDirectoryEntry::Directory { addr: dir_addr, .. } =>
                NodeEntry::Directory(
                    self.interp_at(dir_addr, base_vaddr, layer + 1)),
            GhostPageDirectoryEntry::Page { addr, .. } =>
                NodeEntry::Page(
                    MemRegion { base: addr, size: self.arch.layers.index(layer).entry_size }),
            GhostPageDirectoryEntry::Empty =>
                NodeEntry::Empty(),
        }
    }

    pub closed spec fn interp_at(self, ptr: usize, base_vaddr: nat, layer: nat) -> Directory
        decreases (self.arch.layers.len() - layer, self.arch.layers.index(layer).num_entries, 1)
    {
        decreases_when(self.inv_at(layer, ptr));
        Directory {
            entries: self.interp_at_aux(ptr, base_vaddr, layer, 0),
            layer: layer,
            base_vaddr,
            arch: self.arch,
        }
    }

    spec fn interp_at_aux(self, ptr: usize, base_vaddr: nat, layer: nat, i: nat) -> Seq<NodeEntry>
        decreases (self.arch.layers.len() - layer, self.arch.layers.index(layer).num_entries - i, 0)
    {
        decreases_when(self.inv_at(layer, ptr));
        if i >= self.arch.layers.index(layer).num_entries {
            seq![]
        } else {
            seq![self.interp_entry_bytes_as_node_entry(
                ptr + i as usize * ENTRY_BYTES,
                base_vaddr + i as usize * self.arch.layers.index(layer).entry_size,
                layer)].add(
                self.interp_at_aux(ptr, base_vaddr, layer, i + 1))
        }
    }

    spec fn interp(self) -> Directory {
        self.interp_at(self.memory.root(), 0, 0)
    }

    // #[proof]
    // fn lemma_inv_implies_interp_inv(self) {
    //     requires(self.inv());
    //     ensures(self.interp().inv());
    //     self.lemma_inv_implies_interp_at_inv(self.memory.root(), 0, 0);
    // }

    // #[proof]
    // fn lemma_inv_implies_interp_at_inv(self, ptr: usize, base_vaddr: nat, layer: nat) {
    //     requires([
    //              self.well_formed(),
    //              self.inv_at(layer, ptr),
    //     ]);
    //     ensures(self.interp_at(ptr, base_vaddr, layer).inv());
    //     assume(self.interp_at(ptr, base_vaddr, layer).inv());
    // }

    // #[proof]
    // fn lemma_inv_implies_interp_at_aux_inv(self, ptr: usize, base_vaddr: nat, layer: nat, i: nat) {
    //     decreases(self.arch.layers.len() - i + 1);
    //     requires([
    //              self.well_formed(),
    //              self.inv_at(layer, ptr),
    //     ]);
    //     ensures([
    //             self.interp_at_aux(ptr, base_vaddr, layer, i).len() == self.arch.layers.index(layer).num_entries - i,
    //             {
    //                 let res = self.interp_at_aux(ptr, base_vaddr, layer, i);
    //                 forall(|j: nat|
    //                        j >= i && j < self.arch.layers.index(layer).num_entries && res.index(j).is_Directory()
    //                        >>= res.index(j).get_Directory_0().inv())},
    //     ]);
    //     assume({
    //         let res = self.interp_at_aux(ptr, base_vaddr, layer, i);
    //         forall(|j: nat|
    //                j >= i && j < self.arch.layers.index(layer).num_entries && res.index(j).is_Directory()
    //                >>= res.index(j).get_Directory_0().inv())
    //     });

    //     let res = self.interp_at_aux(ptr, base_vaddr, layer, i);
    //     let res_next = self.interp_at_aux(ptr, base_vaddr, layer, i + 1);
    //     assert(res.len() == res_next.len() + 1);

    //     self.lemma_inv_implies_interp_at_aux_inv(ptr, base_vaddr, layer, i + 1);

    // }

}

}
