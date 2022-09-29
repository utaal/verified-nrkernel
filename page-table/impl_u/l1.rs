#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use modes::*;
use seq::*;
use seq_lib::*;
use option::{*, Option::*};
use map::*;
use set::*;
use set_lib::*;
use vec::*;
use crate::definitions_t::{new_seq, lemma_new_seq};
use crate::impl_u::lib;
use crate::impl_u::indexing;

use result::{*, Result::*};

use crate::definitions_t::{ MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS, MAX_ENTRY_SIZE };
use crate::definitions_t::{ MemRegion, overlap, Arch, between, aligned, PageTableEntry, Flags };
use crate::impl_u::l0::{ self, ambient_arith, ambient_lemmas1 };

verus! {

pub proof fn ambient_lemmas2()
    ensures
        forall|d: Directory, i: nat|
            #![trigger d.inv(), d.entries.index(i)]
            d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory() ==> d.entries.index(i).get_Directory_0().inv(),
        forall|d: Directory| d.inv() ==> (#[trigger] d.interp()).upper == d.upper_vaddr(),
        forall|d: Directory| d.inv() ==> (#[trigger] d.interp()).lower == d.base_vaddr,
{
    assert_forall_by(|d: Directory, i: nat| {
        requires(d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
        ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
        assert(d.directories_obey_invariant());
    });
    assert_forall_by(|d: Directory| {
        requires(d.inv());
        ensures(#[auto_trigger] d.interp().upper == d.upper_vaddr() && d.interp().lower == d.base_vaddr);
        d.lemma_inv_implies_interp_inv();
    });
}

// Simply uncommenting this thing slows down verification of this file by 2.5x
// #[proof]
// fn ambient_lemmas3() {
//     ensures([
//             forall(|d: Directory, base: nat, pte: PageTableEntry|
//                    d.inv() && #[trigger] d.accepted_mapping(base, pte) ==>
//                    d.interp().accepted_mapping(base, pte)),
//     ]);
//     assert_forall_by(|d: Directory, base: nat, pte: PageTableEntry| {
//         requires(d.inv() && #[trigger] d.accepted_mapping(base, pte));
//         ensures(d.interp().accepted_mapping(base, pte));
//         d.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
//     });
// }

#[is_variant]
pub enum NodeEntry {
    Directory(Directory),
    Page(PageTableEntry),
    Empty(),
}

pub struct Directory {
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

    pub open spec(checked) fn well_formed(&self) -> bool {
        &&& self.arch.inv()
        &&& self.layer < self.arch.layers.len()
        &&& aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        &&& self.entries.len() == self.num_entries()
    }

    pub open spec(checked) fn entry_size(&self) -> nat
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.entry_size(self.layer)
    }

    pub open spec(checked) fn num_entries(&self) -> nat // number of entries
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.num_entries(self.layer)
    }

    pub open spec(checked) fn empty(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.num_entries() ==> self.entries.index(i).is_Empty()
    }

    pub open spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i).is_Page())
            ==> (#[trigger] self.entries.index(i)).get_Page_0().frame.size == self.entry_size()
    }

    pub open spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
            ==> {
                let directory = (#[trigger] self.entries.index(i)).get_Directory_0();
                &&& directory.layer == self.layer + 1
                &&& directory.base_vaddr == self.base_vaddr + i * self.entry_size()
            }
    }

    pub open spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases (self.arch.layers.len() - self.layer, 0nat)
    {
        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
                ==> (#[trigger] self.entries.index(i)).get_Directory_0().inv()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn directories_match_arch(&self) -> bool {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
            ==> equal((#[trigger] self.entries.index(i)).get_Directory_0().arch, self.arch)
    }

    pub open spec fn directories_are_nonempty(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
    {
        forall|i: nat| i < self.entries.len() && self.entries.index(i).is_Directory()
            ==> !(#[trigger] self.entries.index(i).get_Directory_0().empty())
    }

    pub open spec(checked) fn frames_aligned(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.entries.len() && self.entries.index(i).is_Page() ==>
            aligned((#[trigger] self.entries.index(i)).get_Page_0().frame.base, self.entry_size())
    }

    pub open spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer
    {
        &&& self.well_formed()
        &&& self.pages_match_entry_size()
        &&& self.directories_are_in_next_layer()
        &&& self.directories_match_arch()
        &&& self.directories_obey_invariant()
        &&& self.directories_are_nonempty()
        &&& self.frames_aligned()
    }

    pub open spec(checked) fn interp(self) -> l0::PageTableContents {
        self.interp_aux(0)
    }

    pub open spec(checked) fn upper_vaddr(self) -> nat
        recommends self.well_formed()
    {
        self.arch.upper_vaddr(self.layer, self.base_vaddr)
    }

    pub open spec fn index_for_vaddr(self, vaddr: nat) -> nat {
        self.arch.index_for_vaddr(self.layer, self.base_vaddr, vaddr)
    }

    pub open spec(checked) fn entry_base(self, idx: nat) -> nat
        recommends self.inv()
    {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec(checked) fn next_entry_base(self, idx: nat) -> nat
        recommends self.inv()
    {
        self.arch.next_entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn entry_bounds(self, entry: nat) -> (nat, nat) {
        (self.entry_base(entry), self.entry_base(entry + 1))
    }

    pub open spec fn interp_of_entry(self, entry: nat) -> l0::PageTableContents
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - entry, 0nat)
    {
        if self.inv() && entry < self.entries.len() {
            let (lower, upper) = self.entry_bounds(entry);
            l0::PageTableContents {
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
            forall|i: nat| #![auto]
                i < self.num_entries() ==>
                self.interp_of_entry(i).inv() &&
                self.interp_of_entry(i).lower == self.entry_base(i) &&
                self.interp_of_entry(i).upper == self.entry_base(i+1) &&
                forall(|base: nat| self.interp_of_entry(i).map.dom().contains(base) ==> between(base, self.entry_base(i), self.entry_base(i+1))) &&
                forall(|base: nat, pte: PageTableEntry| self.interp_of_entry(i).map.contains_pair(base, pte) ==> between(base, self.entry_base(i), self.entry_base(i+1))),
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

        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, i, self.entry_size());
        match self.entries.index(i) {
            NodeEntry::Page(pte)      => {
                assert(entry_i.mappings_dont_overlap());

                assert_nonlinear_by({
                    requires([
                             self.inv(),
                             equal(entry_i, self.interp_of_entry(i)),
                             self.entry_size() == pte.frame.size,
                             i < self.entries.len(),
                    ]);
                    ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), pte));
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
                    // New instability with z3 4.10.1
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
            forall|i: nat, j: nat|
                i < self.num_entries() && j < self.num_entries() && i != j
                ==> self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j)),
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
                });
            }
        });
    }

    pub open spec(checked) fn interp_aux(self, i: nat) -> l0::PageTableContents
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i, 1nat)
    {

        if self.inv() {
            if i >= self.entries.len() {
                l0::PageTableContents {
                    map: map![],
                    arch: self.arch,
                    lower: self.upper_vaddr(),
                    upper: self.upper_vaddr(),
                }
            } else { // i < self.entries.len()
                let rem = self.interp_aux(i + 1);
                let entry_i = self.interp_of_entry(i);
                l0::PageTableContents {
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

    pub proof fn lemma_inv_implies_interp_inv(self)
        requires
            self.inv(),
        ensures
            self.interp().inv(),
            self.interp().upper == self.upper_vaddr(),
            self.interp().lower == self.base_vaddr,
    {
        self.lemma_inv_implies_interp_aux_inv(0);
    }

    pub proof fn lemma_inv_implies_interp_aux_inv(self, i: nat)
        requires
            self.inv(),
        ensures
            self.interp_aux(i).inv(),
            i <= self.entries.len() ==> self.interp_aux(i).lower == self.entry_base(i),
            self.interp_aux(i).upper == self.upper_vaddr(),
            i == 0 ==> self.interp_aux(0).lower == self.base_vaddr,
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

            if let NodeEntry::Page(pte) = entry {
                indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
                indexing::lemma_entry_base_from_index_support(self.base_vaddr, i, self.entry_size());
            }

            assert(interp.mappings_are_aligned());

            match entry {
                NodeEntry::Page(pte) => {
                    assert_nonlinear_by({
                        requires([
                            self.inv(),
                            equal(entry_i, self.interp_of_entry(i)),
                            self.entry_size() == pte.frame.size,
                            i < self.entries.len(),
                        ]);
                        ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), pte));
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
                        // New instability with z3 4.10.1
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

    pub proof fn lemma_empty_implies_interp_aux_empty(self, i: nat)
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
            forall|i: nat, j: nat|
                j < i && i < self.num_entries()
                ==> self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j)),
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
            });
        });
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(self, i: nat, j: nat)
        requires
             self.inv(),
             i <= j,
             j < self.entries.len(),
        ensures
            forall|va: nat, pte: PageTableEntry| #![auto] self.interp_of_entry(j).map.contains_pair(va, pte) ==> self.interp_aux(i).map.contains_pair(va, pte),
            forall|va: nat| #![auto] self.interp_of_entry(j).map.dom().contains(va) ==> self.interp_aux(i).map.dom().contains(va),
            forall|va: nat|
                between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                ==> !self.interp_aux(i).map.dom().contains(va),
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - i)
    {
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

        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index(self.base_vaddr, j, self.entry_size());
    }

    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(self, j: nat)
        requires
             self.inv(),
             j < self.entries.len(),
        ensures
            forall|va: nat| #![auto] self.interp_of_entry(j).map.dom().contains(va) ==> self.interp().map.dom().contains(va),
            forall|va: nat, pte: PageTableEntry| #![auto] self.interp_of_entry(j).map.contains_pair(va, pte) ==> self.interp().map.contains_pair(va, pte),
            forall|va: nat| #![auto]
                between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                ==> !self.interp().map.dom().contains(va),
    {
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(0, j);
    }

    // TODO restore spec(checked) when recommends_by is fixed
    pub open spec fn resolve(self, vaddr: nat) -> Result<(nat, PageTableEntry),()>
        recommends
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        decreases self.arch.layers.len() - self.layer
    {
        decreases_when(self.inv() && self.interp().accepted_resolve(vaddr));
        decreases_by(Self::check_resolve);

        let entry = self.index_for_vaddr(vaddr);
        match self.entries.index(entry) {
            NodeEntry::Page(pte) => {
                let offset = vaddr - self.entry_base(entry);
                Ok((self.entry_base(entry), pte))
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
        assert(self.inv() && self.interp().accepted_resolve(vaddr));

        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();

        assert(between(vaddr, self.base_vaddr, self.upper_vaddr()));
        let entry = self.index_for_vaddr(vaddr);
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());
        // TODO: This makes the recommends failure on the line below go away but not the one in the
        // corresponding spec function. wtf
        assert(0 <= entry < self.entries.len());
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.inv());
            },
            NodeEntry::Empty() => {
            },
        }
    }

    proof fn lemma_interp_aux_contains_implies_interp_of_entry_contains(self, j: nat)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.interp_aux(j).map.contains_pair(base, pte) ==>
                exists|i: nat| #![auto] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte),
            forall|base: nat|
                self.interp_aux(j).map.dom().contains(base) ==>
                exists|i: nat| #![auto] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base)
        decreases (self.arch.layers.len() - self.layer, self.num_entries() - j)
    {
        if j >= self.entries.len() {
        } else {
            let _ = self.interp_of_entry(j);
            self.lemma_interp_aux_contains_implies_interp_of_entry_contains(j+1);
            assert_forall_by(|base: nat, pte: PageTableEntry| {
                requires(self.interp_aux(j).map.contains_pair(base, pte));
                ensures(exists|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte));
                if self.interp_aux(j+1).map.contains_pair(base, pte) { } else { }
            });
            assert_forall_by(|base: nat| {
                requires(self.interp_aux(j).map.dom().contains(base));
                ensures(exists|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base));
                if self.interp_aux(j+1).map.dom().contains(base) { } else { }
            });
        }
    }

    proof fn lemma_interp_contains_implies_interp_of_entry_contains(self)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.interp().map.contains_pair(base, pte) ==>
                exists|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, pte),
            forall|base: nat|
                self.interp().map.dom().contains(base) ==>
                exists|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base),
    {
        self.lemma_interp_aux_contains_implies_interp_of_entry_contains(0);
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(self, vaddr: nat, i: nat)
        requires
            self.inv(),
            i < self.num_entries(),
            between(vaddr, self.interp_of_entry(i).lower, self.interp_of_entry(i).upper),
            !exists|base:nat|
                self.interp_of_entry(i).map.dom().contains(base) &&
                between(vaddr, base, base + (#[trigger] self.interp_of_entry(i).map.index(base)).frame.size),
        ensures
            !exists|base:nat|
                self.interp().map.dom().contains(base) &&
                between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).frame.size),
    {
        assert forall|idx: nat, idx2: nat, base: nat, layer: nat|
            layer < self.arch.layers.len() && idx < idx2
            implies self.arch.entry_base(layer, base, idx) <  self.arch.entry_base(layer, base, idx2) by
        {
            indexing::lemma_entry_base_from_index(base, idx, self.arch.entry_size(layer));
        };
        self.lemma_interp_of_entry();
        self.lemma_interp_contains_implies_interp_of_entry_contains();

        if exists|base:nat|
            self.interp().map.dom().contains(base) &&
            between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).frame.size) {
            let base = choose(|base:nat|
                              self.interp().map.dom().contains(base) &&
                              between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).frame.size));
            let p = self.interp().map.index(base);
            assert(self.interp().map.contains_pair(base, p));
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_resolve_structure_assertions(self, vaddr: nat, idx: nat)
        requires
            self.inv(),
            self.interp().accepted_resolve(vaddr),
            idx == self.index_for_vaddr(vaddr),
        ensures
            self.entries.index(idx).is_Directory() ==> {
                let d = self.entries.index(idx).get_Directory_0();
                &&& d.interp().accepted_resolve(vaddr)
                &&& d.inv()
            },
        decreases self.arch.layers.len() - self.layer
    {
        ambient_lemmas1();
        ambient_lemmas2();

        indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());

        match self.entries.index(idx) {
            NodeEntry::Page(p) => { },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.interp().accepted_resolve(vaddr));
            },
            NodeEntry::Empty() => { },
        }
    }

    #[verifier(spinoff_prover)]
    pub proof fn lemma_resolve_refines(self, vaddr: nat)
        requires
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        ensures
            equal(self.interp().resolve(vaddr), self.resolve(vaddr)),
        decreases self.arch.layers.len() - self.layer
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();

        let entry = self.index_for_vaddr(vaddr);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                assert(self.resolve(vaddr).is_Ok());
                let p_vaddr = self.entry_base(entry);
                assert(self.interp().map.contains_pair(p_vaddr, p));
                assert(vaddr < p_vaddr + self.interp().map.index(p_vaddr).frame.size);
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.interp().accepted_resolve(vaddr));
                d.lemma_resolve_refines(vaddr);

                assert(equal(self.interp_of_entry(entry), d.interp()));

                assert(equal(d.interp().resolve(vaddr), d.resolve(vaddr)));

                if d.resolve(vaddr).is_Ok() {
                    assert(self.resolve(vaddr).is_Ok());
                    assert(exists|base: nat|
                           d.interp().map.dom().contains(base) &&
                           between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size));

                    let base = choose(|base:nat|
                                    d.interp().map.dom().contains(base) &&
                                    between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size));

                    assert(self.interp().map.contains_pair(base, self.interp_of_entry(entry).map.index(base)));

                    assert(d.resolve(vaddr).is_Ok());
                    assert(d.interp().resolve(vaddr).is_Ok());
                    assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
                } else {
                    assert(d.resolve(vaddr).is_Err());
                    assert(self.resolve(vaddr).is_Err());

                    assert(d.interp().resolve(vaddr).is_Err());
                    assert(!exists|base:nat|
                           d.interp().map.dom().contains(base) &&
                           between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size)) by
                    {
                        assert(!exists|base:nat, pte:PageTableEntry|
                                    d.interp().map.contains_pair(base, pte) &&
                                    between(vaddr, base, base + pte.frame.size));
                        if exists|base:nat|
                           d.interp().map.dom().contains(base) &&
                           between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size) {
                           let base = choose|base:nat|
                               d.interp().map.dom().contains(base) &&
                               between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size);
                           let pte = d.interp().map.index(base);
                           assert(d.interp().map.contains_pair(base, pte));
                       }
                    };
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

    pub open spec(checked) fn update(self, n: nat, e: NodeEntry) -> Self
        recommends n < self.entries.len()
    {
        Directory {
            entries: self.entries.update(n, e),
            ..self
        }
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(self, base: nat, pte: PageTableEntry) -> bool
        recommends self.inv()
    {
        self.base_vaddr <= base && base + pte.frame.size <= self.upper_vaddr()
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PageTableEntry) -> bool
        recommends self.inv()
    {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size_at_index_atleast(pte.frame.size, self.layer)
    }

    pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_manual(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte)
        ensures
            self.interp().accepted_mapping(base, pte),
    {
        self.lemma_inv_implies_interp_inv();
    }

    pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_auto(self)
        ensures
            forall|base: nat, pte: PageTableEntry|
                self.inv() && #[trigger] self.accepted_mapping(base, pte) ==>
                self.interp().accepted_mapping(base, pte),
    {
        assert_forall_by(|base: nat, pte: PageTableEntry| {
            requires(self.inv() && #[trigger] self.accepted_mapping(base, pte));
            ensures(self.interp().accepted_mapping(base, pte));

            self.lemma_accepted_mapping_implies_interp_accepted_mapping_manual(base, pte);
        });
    }

    // Creates new empty directory to map to entry 'entry'
    pub open spec fn new_empty_dir(self, entry: nat) -> Self
        recommends
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
    {
        Directory {
            entries:    new_seq(self.arch.num_entries((self.layer + 1) as nat), NodeEntry::Empty()),
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
            self.new_empty_dir(entry).entries.len() == self.arch.num_entries((self.layer + 1) as nat),
            forall|j: nat| j < self.new_empty_dir(entry).num_entries() ==> equal(self.new_empty_dir(entry).entries.index(j), NodeEntry::Empty()),
    {
        let new_dir = self.new_empty_dir(entry);
        let num_entries = self.arch.num_entries((self.layer + 1) as nat);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        lemma_new_seq::<NodeEntry>(num_entries, NodeEntry::Empty());

        assert(new_dir.directories_obey_invariant());
        assert(new_dir.inv());
    }

    pub open spec fn map_frame(self, base: nat, pte: PageTableEntry) -> Result<Directory,Directory>
        decreases self.arch.layers.len() - self.layer
    {
        decreases_by(Self::check_map_frame);

        if self.inv() && self.accepted_mapping(base, pte) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry) {
                NodeEntry::Page(p) => {
                    Err(self)
                },
                NodeEntry::Directory(d) => {
                    if self.entry_size() == pte.frame.size {
                        Err(self)
                    } else {
                        match d.map_frame(base, pte) {
                            Ok(d)  => Ok(self.update(entry, NodeEntry::Directory(d))),
                            Err(d) => Err(self.update(entry, NodeEntry::Directory(d))),
                        }
                    }
                },
                NodeEntry::Empty() => {
                    if self.entry_size() == pte.frame.size {
                        Ok(self.update(entry, NodeEntry::Page(pte)))
                    } else {
                        // new_empty_dir's recommendation for `self.layer + 1 < self.arch.layers.len()`
                        // is satisfied because we know the frame size isn't this layer's entrysize
                        // (i.e. must be on some lower level).
                        let new_dir = self.new_empty_dir(entry);
                        // We never fail to insert an accepted mapping into an empty directory
                        Ok(self.update(entry, NodeEntry::Directory(new_dir.map_frame(base, pte).get_Ok_0())))
                    }
                },
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_map_frame(self, base: nat, pte: PageTableEntry) {
        ambient_lemmas1();
        ambient_lemmas2(); // TODO: unnecessary?
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        if self.inv() && self.accepted_mapping(base, pte) {
            indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
        }
    }

    pub proof fn lemma_accepted_mapping_implies_directory_accepted_mapping(self, base: nat, pte: PageTableEntry, d: Directory)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            equal(d.arch, self.arch),
            d.base_vaddr == self.entry_base(self.index_for_vaddr(base)),
            d.upper_vaddr() == self.entry_base(self.index_for_vaddr(base)+1),
            d.inv(),
            d.layer == self.layer + 1,
            self.entry_size() != pte.frame.size,
        ensures
            d.accepted_mapping(base, pte),
    {
        ambient_lemmas1();
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();

        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        assert(self.directories_obey_invariant());
        assert(d.inv());

        assert(aligned(base, pte.frame.size));
        assert(aligned(pte.frame.base, pte.frame.size));
        assert(d.arch.contains_entry_size_at_index_atleast(pte.frame.size, d.layer));

        assert(self.entry_base(entry) <= base);
        assert(aligned(base, pte.frame.size));
        self.arch.lemma_entry_sizes_aligned_auto();
        assert(aligned(self.entry_size(), pte.frame.size));

        lib::aligned_transitive_auto();
        assert(aligned(self.next_entry_base(entry), pte.frame.size));
        lib::leq_add_aligned_less(base, pte.frame.size, self.entry_base(entry+1));
        assert(base + pte.frame.size <= self.entry_base(entry+1));
        assert(base + pte.frame.size <= self.entry_base(entry) + self.entry_size());
        assert(base + pte.frame.size <= d.base_vaddr + self.entry_size());
        assert(base + pte.frame.size <= d.base_vaddr + d.num_entries() * d.entry_size());
        assert(base + pte.frame.size <= d.upper_vaddr());
        assert(d.candidate_mapping_in_bounds(base, pte));
        assert(aligned(base, pte.frame.size));
        assert(aligned(pte.frame.base, pte.frame.size));
    }

    proof fn lemma_map_frame_empty_is_ok(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            self.entries.index(self.index_for_vaddr(base)).is_Empty(),
        ensures
            self.map_frame(base, pte).is_Ok(),
            // self.new_empty_dir(self.index_for_vaddr(base)).map_frame(base, pte).is_Ok()
        decreases self.arch.layers.len() - self.layer;

    pub proof fn lemma_map_frame_preserves_inv(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            self.map_frame(base, pte).is_Ok(),
        ensures
            self.map_frame(base, pte).get_Ok_0().layer === self.layer,
            self.map_frame(base, pte).get_Ok_0().arch === self.arch,
            self.map_frame(base, pte).get_Ok_0().base_vaddr === self.base_vaddr,
            !self.map_frame(base, pte).get_Ok_0().empty(),
            self.map_frame(base, pte).get_Ok_0().inv(),
            !exists|b:nat| true
                && self.interp().map.dom().contains(b)
                && between(base, b, b + (#[trigger] self.interp().map.index(b)).frame.size),

        decreases (self.arch.layers.len() - self.layer)
    {

        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());

        let res = self.map_frame(base, pte).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        match self.entries.index(entry) {
            NodeEntry::Page(p) => (),
            NodeEntry::Directory(d) => {
                if self.entry_size() == pte.frame.size {
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    d.lemma_inv_implies_interp_inv();
                    assert(d.inv());
                    d.lemma_map_frame_preserves_inv(base, pte);
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
                    assert(equal(self.map_frame(base, pte).get_Ok_0().layer, self.layer));

                    assert(res.entries.index(entry).is_Directory());
                    assert(!res.empty());
                    self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry);
                }
            },
            NodeEntry::Empty() => {
                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry);
                if self.entry_size() == pte.frame.size {
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

                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir);
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());
                    new_dir.lemma_map_frame_empty_is_ok(base, pte);
                    new_dir.lemma_map_frame_preserves_inv(base, pte);

                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.frames_aligned());
                    assert(res.inv());
                    assert(equal(res.layer, self.layer));
                    assert(res.entries.index(entry).is_Directory());
                    assert(!res.empty());
                    assert(new_dir.map_frame(base, pte).is_Ok());
                }
            },
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp_aux(self, i: nat, j: nat, base: nat, n: NodeEntry, pte: PageTableEntry)
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            !self.interp_aux(i).map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, pte),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                }),
        ensures
            equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map),
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

                assert(equal(self.interp_of_entry(i).map.insert(base, pte), nself.interp_of_entry(i).map));
                self.lemma_entries_equal_implies_interp_aux_equal(nself, i+1);
                assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));


                assert(!self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).dom().contains(base));

                assert(equal(self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).insert(base, pte),
                             self.update(j, n).interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map));
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());

                self.lemma_insert_interp_of_entry_implies_insert_interp_aux(i + 1, j, base, n, pte);
                self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i + 1, j);
                assert(!self.interp_of_entry(j).map.dom().contains(base));

                assert(!self.interp_aux(i).map.dom().contains(base));

                assert(equal(self.interp_aux(i + 1).map.insert(base, pte), self.update(j, n).interp_aux(i + 1).map));

                assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));

                assert(nself.inv());
                assert(equal(nself.interp_aux(i).map, nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));

                assert(equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map));
            }
        }
    }

    proof fn lemma_insert_interp_of_entry_implies_insert_interp(self, j: nat, base: nat, n: NodeEntry, pte: PageTableEntry)
        requires
            self.inv(),
            j < self.num_entries(),
            !self.interp().map.dom().contains(base),
            self.update(j, n).inv(),
            equal(
                self.interp_of_entry(j).map.insert(base, pte),
                match n {
                    NodeEntry::Page(p)      => map![self.entry_base(j) => p],
                    NodeEntry::Directory(d) => d.interp_aux(0).map,
                    NodeEntry::Empty()      => map![],
                }),
        ensures
            equal(self.interp().map.insert(base, pte), self.update(j, n).interp().map),
        decreases
            self.arch.layers.len() - self.layer,
    {
        self.lemma_insert_interp_of_entry_implies_insert_interp_aux(0, j, base, n, pte);
    }

    proof fn lemma_nonempty_implies_exists_interp_dom_contains(self)
        requires
            self.inv(),
            !self.empty()
        ensures
            exists|b: nat| self.interp().map.dom().contains(b)
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();

        assert(exists|i: nat| i < self.num_entries() && !self.entries.index(i).is_Empty());
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

    pub proof fn lemma_map_frame_structure_assertions(self, base: nat, pte: PageTableEntry, idx: nat)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
            idx == self.index_for_vaddr(base),
        ensures
            match self.entries.index(idx) {
                NodeEntry::Page(p)      => true,
                NodeEntry::Directory(d) => {
                    &&& d.inv()
                    &&& if self.entry_size() == pte.frame.size {
                        true
                    } else {
                        d.accepted_mapping(base, pte)
                    }
                },
                NodeEntry::Empty()      => {
                    if self.entry_size() == pte.frame.size {
                        true
                    } else {
                        &&& ((self.layer + 1) as nat) < self.arch.layers.len()
                        &&& self.new_empty_dir(idx).inv()
                        &&& self.new_empty_dir(idx).accepted_mapping(base, pte)
                        &&& self.new_empty_dir(idx).map_frame(base, pte).is_Ok()
                    }
                },
            }
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());

        let res = self.map_frame(base, pte).get_Ok_0();
        if self.map_frame(base, pte).is_Ok() {
            self.lemma_map_frame_preserves_inv(base, pte);
        }

        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => { },
            NodeEntry::Directory(d) => {
                assert(d.inv());
                if self.entry_size() == pte.frame.size {
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    assert(d.accepted_mapping(base, pte));
                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == pte.frame.size {
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    assert(new_dir.inv());

                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir);
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());

                    new_dir.lemma_map_frame_refines_map_frame(base, pte);
                    assert(new_dir.interp().map_frame(base, pte).is_Ok());
                }
            },
        }
    }

    pub proof fn lemma_map_frame_refines_map_frame(self, base: nat, pte: PageTableEntry)
        requires
            self.inv(),
            self.accepted_mapping(base, pte),
        ensures
            self.map_frame(base, pte).is_Err() ==> self.map_frame(base, pte).get_Err_0() === self,
            self.map_frame(base, pte).map(|d| d.interp()) === self.interp().map_frame(base, pte),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());

        let res = self.map_frame(base, pte).get_Ok_0();
        if self.map_frame(base, pte).is_Ok() {
            self.lemma_map_frame_preserves_inv(base, pte);
        }

        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                assert(self.map_frame(base, pte).is_Err());

                assert(self.interp_of_entry(entry).map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map.contains_pair(self.entry_base(entry), p));
                assert(self.interp().map_frame(base, pte).is_Err());
            },
            NodeEntry::Directory(d) => {
                d.lemma_inv_implies_interp_inv();
                assert(d.inv());
                if self.entry_size() == pte.frame.size {
                    assert(self.map_frame(base, pte).is_Err());
                    d.lemma_nonempty_implies_exists_interp_dom_contains();
                    let b = choose(|b: nat| d.interp().map.dom().contains(b));
                    assert(self.interp().map.dom().contains(b));
                    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

                    assert(!self.interp().valid_mapping(base, pte));
                    assert(self.interp().map_frame(base, pte).is_Err());
                } else {
                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d);
                    assert(d.accepted_mapping(base, pte));
                    d.lemma_map_frame_refines_map_frame(base, pte);
                    assert(equal(d.map_frame(base, pte).map(|d| d.interp()), d.interp().map_frame(base, pte)));
                    match d.map_frame(base, pte) {
                        Ok(nd)  => {
                            assert(d.map_frame(base, pte).is_Ok());
                            assert(d.interp().map_frame(base, pte).is_Ok());
                            assert(d.interp().accepted_mapping(base, pte));
                            assert(d.interp().valid_mapping(base, pte));
                            assert(self.interp().accepted_mapping(base, pte));
                            assert(self.interp().valid_mapping(base, pte));
                            assert(self.map_frame(base, pte).is_Ok());
                            self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(nd), pte);
                            assert(self.interp().map_frame(base, pte).is_Ok());

                            assert(equal(self.interp().map.insert(base, pte), self.update(entry, NodeEntry::Directory(nd)).interp().map));
                            assert(equal(self.interp().map.insert(base, pte), self.interp().map_frame(base, pte).get_Ok_0().map));

                            assert(equal(self.map_frame(base, pte).get_Ok_0().interp(), self.interp().map_frame(base, pte).get_Ok_0()));
                        },
                        Err(e) => {
                            assert(d.map_frame(base, pte).is_Err());
                            assert(d.interp().map_frame(base, pte).is_Err());
                            assert(d.interp().accepted_mapping(base, pte));
                            assert(!d.interp().valid_mapping(base, pte));
                            let b = choose(|b: nat| #[auto_trigger]
                                           d.interp().map.dom().contains(b) && overlap(
                                               MemRegion { base: base, size: pte.frame.size },
                                               MemRegion { base: b, size: d.interp().map.index(b).frame.size }
                                               ));
                            let bbase = d.interp().map.index(b).frame.base;
                            let bsize = d.interp().map.index(b).frame.size;
                            assert(d.interp().map.contains_pair(b, d.interp().map.index(b)));
                            assert(overlap(
                                    MemRegion { base: base, size: pte.frame.size },
                                    MemRegion { base: b, size: bsize }
                                    ));
                            self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);
                            assert(self.interp().map.contains_pair(b, d.interp().map.index(b)));

                            assert(self.interp().accepted_mapping(base, pte));
                            assert(!self.interp().valid_mapping(base, pte));

                            assert(self.map_frame(base, pte).is_Err());
                            assert(self.interp().map_frame(base, pte).is_Err());
                            assert(self.entries.index(entry) === NodeEntry::Directory(d));
                            assert(self.entries.index(entry) === NodeEntry::Directory(e));
                            let res = self.update(entry, NodeEntry::Directory(e)).entries;
                            assert(res.index(entry) === self.entries.index(entry));
                            assert_seqs_equal!(res, self.entries);
                        },
                    }
                    // d.lemma_map_frame_preserves_inv(base, pte);
                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == pte.frame.size {
                    self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Page(pte), pte);
                    assert(equal(self.map_frame(base, pte).map(|d| d.interp()), self.interp().map_frame(base, pte)));
                } else {
                    assert(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = self.new_empty_dir(entry);
                    self.lemma_new_empty_dir(entry);
                    assert(new_dir.inv());

                    self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir);
                    new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
                    assert(new_dir.accepted_mapping(base, pte));
                    indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());
                    new_dir.lemma_map_frame_empty_is_ok(base, pte);
                    new_dir.lemma_map_frame_preserves_inv(base, pte);

                    let new_dir_mapped = new_dir.map_frame(base, pte).get_Ok_0();
                    assert(new_dir.map_frame(base, pte).is_Ok());
                    assert(new_dir_mapped.inv());
                    new_dir.lemma_map_frame_refines_map_frame(base, pte);
                    assert(new_dir.interp().map_frame(base, pte).is_Ok());
                    assert(equal(new_dir_mapped.interp(), new_dir.interp().map_frame(base, pte).get_Ok_0()));

                    new_dir.lemma_empty_implies_interp_empty();
                    assert_maps_equal!(new_dir.interp().map, map![]);
                    assert_maps_equal!(new_dir.interp().map_frame(base, pte).get_Ok_0().map, map![base => pte]);
                    assert_maps_equal!(self.interp_of_entry(entry).map, map![]);
                    assert(equal(self.interp_of_entry(entry).map, map![]));
                    assert(equal(map![].insert(base, pte), new_dir_mapped.interp().map));
                    assert(equal(self.interp_of_entry(entry).map.insert(base, pte), new_dir_mapped.interp().map));
                    self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(new_dir_mapped), pte);

                    assert(equal(self.map_frame(base, pte).map(|d| d.interp()), self.interp().map_frame(base, pte)));
                }
            },
        }
    }

    pub open spec(checked) fn accepted_unmap(self, base: nat) -> bool
        recommends self.well_formed()
    {
        true
        && self.interp().accepted_unmap(base)
    }

    pub open spec fn unmap(self, base: nat) -> Result<Directory,Directory>
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
                        Err(self)
                    }
                },
                NodeEntry::Directory(d) => {
                    match d.unmap(base) {
                        Ok(new_d) =>
                            Ok(self.update(entry, if new_d.empty() {
                                NodeEntry::Empty()
                            } else {
                                NodeEntry::Directory(new_d)
                            })),
                        Err(new_d) => Err(self.update(entry, NodeEntry::Directory(new_d)))
                    }
                },
                NodeEntry::Empty() => Err(self),
            }
        } else {
            arbitrary()
        }
    }

    #[verifier(decreases_by)]
    proof fn check_unmap(self, base: nat) {
        if self.inv() && self.accepted_unmap(base) {
            ambient_lemmas2();
            indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
        } else {
        }
    }


    pub proof fn lemma_unmap_preserves_inv(self, base: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
            self.unmap(base).is_Ok(),
        ensures
            self.unmap(base).get_Ok_0().inv(),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();

        let res = self.unmap(base).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());

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

    pub proof fn lemma_unmap_structure_assertions(self, base: nat, idx: nat)
        requires
            self.inv(),
            self.accepted_unmap(base),
            idx == self.index_for_vaddr(base),
        ensures
            match self.entries.index(idx) {
                NodeEntry::Page(p)      => {
                    if aligned(base, self.entry_size()) {
                        base == self.base_vaddr + idx * self.entry_size()
                    } else {
                        true
                    }
                },
                NodeEntry::Directory(d) => {
                    &&& d.inv()
                    &&& d.accepted_unmap(base)
                },
                NodeEntry::Empty()      => true,
            }
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_inv_implies_interp_inv();

        indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());

        match self.entries.index(self.index_for_vaddr(base)) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                } else {
                }
            },
            NodeEntry::Directory(d) => {
                assert(d.inv());
                assert(d.accepted_unmap(base));
                d.lemma_unmap_refines_unmap(base);
            },
            NodeEntry::Empty() => { },
        }
   }

    pub proof fn lemma_unmap_refines_unmap(self, base: nat)
        requires
             self.inv(),
             self.accepted_unmap(base),
        ensures
            self.unmap(base).is_Err() ==> self.unmap(base).get_Err_0() === self,
            equal(self.unmap(base).map(|d| d.interp()), self.interp().unmap(base)),
        decreases (self.arch.layers.len() - self.layer)
    {
        ambient_lemmas1();
        ambient_lemmas2();
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
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry);

        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
                if aligned(base, self.entry_size()) {
                    assert_maps_equal!(self.interp_of_entry(entry).map.remove(base), map![]);
                    assert(self.update(entry, NodeEntry::Empty()).inv());
                    self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Empty());
                } else {
                    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
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
                    Err(e) => {
                        assert(self.entries.index(entry) === NodeEntry::Directory(d));
                        assert(self.entries.index(entry) === NodeEntry::Directory(e));
                        let res = self.update(entry, NodeEntry::Directory(e)).entries;
                        assert(res.index(entry) === self.entries.index(entry));
                        assert_seqs_equal!(res, self.entries);
                        assert(res === self.entries);
                    }
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
            forall|j: nat| i <= j && j < self.entries.len() ==> equal(self.entries.index(j), other.entries.index(j)),
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
    pub open spec(checked) fn map_ok<C, F: Fn(A) -> C>(self, f: F) -> Result<C,B> {
        match self {
            Ok(a)  => Ok(f(a)),
            Err(b) => Err(b),
        }
    }
}

impl<A> Result<A,A> {
    pub open spec(checked) fn map<B, F: Fn(A) -> B>(self, f: F) -> Result<B,B> {
        match self {
            Ok(a)  => Ok(f(a)),
            Err(a) => Err(f(a)),
        }
    }
}

}
