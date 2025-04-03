use vstd::assert_by_contradiction;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{new_seq};
#[cfg(verus_keep_ghost)]
use crate::definitions_u::{lemma_new_seq};
//#[cfg(verus_keep_ghost)]
//use crate::extra::{ self, result_map };
use crate::impl_u::indexing;

use crate::spec_t::mmu::defs::{ Arch, PTE };
//use crate::spec_t::mmu::defs::{ MemRegion, Arch, PTE };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ aligned, };
//use crate::spec_t::mmu::defs::{ overlap, between, aligned, };
//#[cfg(verus_keep_ghost)]
//use crate::impl_u::l0;

verus! {

pub broadcast group group_ambient {
    vstd::arithmetic::mul::lemma_mul_is_commutative,
    vstd::map_lib::group_map_union,
}

pub proof fn ambient_lemmas2()
    ensures
        forall|d: Directory, i: nat|
            #![trigger d.inv(), d.entries.index(i as int)]
            d.inv() && i < d.num_entries() && d.entries.index(i as int) is Directory ==> d.entries.index(i as int)->Directory_0.inv(),
        //forall|d: Directory| #[trigger] d.inv() ==> d.interp().upper == d.upper_vaddr(),
        //forall|d: Directory| #[trigger] d.inv() ==> d.interp().lower == d.base_vaddr,
{
    assert forall |d: Directory, i: nat| #![auto] d.inv() && i < d.num_entries() && d.entries.index(i as int) is Directory
        implies d.entries.index(i as int)->Directory_0.inv() by {
        assert(d.directories_obey_invariant());
    };
    //assert forall |d: Directory| #![auto] d.inv() implies d.interp().upper == d.upper_vaddr() && d.interp().lower == d.base_vaddr by {
    //    //d.lemma_inv_implies_interp_inv();
    //};
}

pub enum NodeEntry {
    Directory(Directory),
    Page(PTE),
    Invalid,
}

pub struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat, // index into layer_sizes
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

impl NodeEntry {
    pub open spec fn interp(self, base: nat) -> Map<nat, PTE>
        decreases self, 0nat, 0nat
    {
        match self {
            NodeEntry::Page(p)      => map![base => p],
            NodeEntry::Directory(d) => d.interp_aux(0),
            NodeEntry::Invalid      => map![],
        }
    }
}

impl Directory {
    pub open spec(checked) fn well_formed(&self) -> bool {
        &&& self.arch.inv()
        &&& self.layer < self.arch.layers.len()
        //&&& aligned(self.base_vaddr, self.entry_size() * self.num_entries())
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
        forall|i: nat| i < self.num_entries() ==> self.entries.index(i as int) is Invalid
    }

    pub open spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| (i < self.entries.len() && self.entries[i as int] is Page)
            ==> (#[trigger] self.entries[i as int]->Page_0.frame.size) == self.entry_size()
    }

    pub open spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.entries.len() && self.entries.index(i as int) is Directory ==> {
            let directory = #[trigger] self.entries[i as int]->Directory_0;
            &&& directory.layer == self.layer + 1
            &&& directory.base_vaddr == self.base_vaddr + i * self.entry_size()
        }
    }

    pub open spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases self.arch.layers.len() - self.layer, 0nat
    {
        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall|i: nat| (i < self.entries.len() && #[trigger] self.entries[i as int] is Directory)
                ==> self.entries[i as int]->Directory_0.inv()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn directories_match_arch(&self) -> bool {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i as int) is Directory)
            ==> (#[trigger] self.entries.index(i as int)->Directory_0.arch) == self.arch
    }

    pub open spec fn no_empty_directories(&self) -> bool
        decreases self
    {
        forall|i: nat| i < self.entries.len() ==>
            (#[trigger] self.entries[i as int] matches NodeEntry::Directory(d) ==> {
                &&& !d.empty()
                &&& d.no_empty_directories()
            })
    }

    pub open spec(checked) fn frames_aligned(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.entries.len() && #[trigger] self.entries[i as int] is Page ==>
            aligned(self.entries[i as int]->Page_0.frame.base, self.entry_size())
    }

    pub open spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer
    {
        &&& self.well_formed()
        &&& self.pages_match_entry_size()
        &&& self.directories_are_in_next_layer()
        &&& self.directories_match_arch()
        &&& self.directories_obey_invariant()
        //&&& non_empty ==> self.directories_are_nonempty()
        //&&& self.frames_aligned()
    }

    pub open spec(checked) fn interp(self) -> Map<nat, PTE> {
        //l0::PageTableContents {
        self.interp_aux(0)
        //    arch: self.arch,
        //    lower: 0,
        //    upper: self.upper_vaddr(),
        //}
    }

    pub open spec(checked) fn upper_vaddr(self) -> nat
        recommends self.well_formed()
    {
        self.arch.upper_vaddr(self.layer, self.base_vaddr)
    }

    pub open spec fn index_for_vaddr(self, vaddr: nat) -> nat {
        self.arch.index_for_vaddr(self.layer, self.base_vaddr, vaddr)
    }

    pub open spec fn entry_base(self, idx: nat) -> nat {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn next_entry_base(self, idx: nat) -> nat {
        self.arch.next_entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn entry_bounds(self, entry: nat) -> (nat, nat) {
        (self.entry_base(entry), self.entry_base(entry + 1))
    }

    pub open spec fn interp_of_entry(self, entry: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - entry, 1nat
    {
        if entry < self.entries.len() {
            self.entries[entry as int].interp(self.entry_base(entry))
        } else {
            arbitrary()
        }
    }

    //proof fn lemma_interp_of_entry(self)
    //    requires
    //        self.inv(),
    //    ensures
    //        forall|i: nat| #![trigger self.interp_of_entry(i)]
    //            i < self.num_entries() ==> {
    //                //&&& self.interp_of_entry(i).inv()
    //                //&&& self.interp_of_entry(i).lower == self.entry_base(i)
    //                //&&& self.interp_of_entry(i).upper == self.next_entry_base(i)
    //                &&& (forall|base: nat| self.interp_of_entry(i).contains_key(base) ==> self.entry_base(i) <= base < self.next_entry_base(i))
    //                &&& (forall|base: nat, pte: PTE| self.interp_of_entry(i).contains_pair(base, pte) ==> self.entry_base(i) <= base < self.next_entry_base(i))
    //            }
    //{
    //    //assert forall |i: nat| #![auto] i < self.num_entries() implies
    //    //             self.interp_of_entry(i).inv() &&
    //    //             self.interp_of_entry(i).lower == self.entry_base(i) &&
    //    //             self.interp_of_entry(i).upper == self.next_entry_base(i) by {
    //    //    self.lemma_inv_implies_interp_of_entry_inv(i);
    //    //};
    //}

    //proof fn lemma_inv_implies_interp_of_entry_inv(self, i: nat)
    //    requires
    //        self.inv(),
    //        i < self.num_entries(),
    //    ensures
    //        self.interp_of_entry(i).inv(),
    //        self.interp_of_entry(i).lower == self.entry_base(i),
    //        self.interp_of_entry(i).upper == self.entry_base(i+1),
    //{
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
    //    indexing::lemma_entry_base_from_index_support(self.base_vaddr, i, self.entry_size());
    //    if let NodeEntry::Directory(d) = self.entries[i as int] {
    //        d.lemma_inv_implies_interp_inv();
    //    }
    //}
    //
    //proof fn lemma_interp_of_entries_disjoint(self)
    //    requires
    //        self.inv(),
    //    ensures
    //        forall|i: nat, j: nat|
    //            i < self.num_entries() && j < self.num_entries() && i != j
    //            ==> self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j)),
    //{
    //    assert forall|i: nat, j: nat|
    //        i < self.num_entries() && j < self.num_entries() && i != j
    //        implies self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j))
    //    by {
    //        if i < j {
    //            assert(self.base_vaddr + i * self.entry_size() <= self.base_vaddr + j * self.entry_size()) by (nonlinear_arith)
    //                requires self.inv() && i < j && self.entry_size() > 0 {};
    //            assert(self.base_vaddr + (i+1) * self.entry_size() <= self.base_vaddr + j * self.entry_size()) by (nonlinear_arith)
    //                requires self.inv() && i < j && self.entry_size() > 0 {};
    //        } else {
    //            assert(self.base_vaddr + j * self.entry_size() < self.base_vaddr + i * self.entry_size()) by (nonlinear_arith)
    //                requires self.inv() && j < i && self.entry_size() > 0 {};
    //            assert(self.base_vaddr + (j+1) * self.entry_size() <= self.base_vaddr + i * self.entry_size()) by (nonlinear_arith)
    //                requires self.inv() && j < i && self.entry_size() > 0 {};
    //        }
    //    }
    //}

    pub open spec fn interp_aux(self, i: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - i, 2nat
    {
        if i < self.entries.len() {
            self.interp_aux(i + 1).union_prefer_right(self.interp_of_entry(i))
        } else { // i < self.entries.len()
            map![]
        }
    }

    pub proof fn lemma_interp_of_entry_disjoint_mappings(self, i: nat, j: nat)
        requires
            i < j < self.entries.len(),
            self.inv(),
        ensures
            forall|va, pte| self.interp_of_entry(i).contains_pair(va, pte) ==> !self.interp_of_entry(j).contains_pair(va, pte),
            forall|va| self.interp_of_entry(i).contains_key(va) ==> !self.interp_of_entry(j).contains_key(va),
            forall|va, pte| self.interp_of_entry(j).contains_pair(va, pte) ==> !self.interp_of_entry(i).contains_pair(va, pte),
            forall|va| self.interp_of_entry(j).contains_key(va) ==> !self.interp_of_entry(i).contains_key(va),
    {
        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index(self.base_vaddr, j, self.entry_size());
        assert forall|va, pte| self.interp_of_entry(i).contains_pair(va, pte) implies !self.interp_of_entry(j).contains_pair(va, pte) by {
            broadcast use Directory::lemma_interp_of_entry_between;
        };
        assert forall|va| self.interp_of_entry(i).contains_key(va) implies !self.interp_of_entry(j).contains_key(va) by {
            broadcast use Directory::lemma_interp_of_entry_between;
            assert(self.interp_of_entry(i).contains_pair(va, self.interp_of_entry(i)[va]));
            assert_by_contradiction!(!self.interp_of_entry(j).contains_key(va), {
                assert(self.interp_of_entry(j).contains_pair(va, self.interp_of_entry(j)[va]));
            });
        };
    }

    pub broadcast proof fn lemma_interp_of_entry_between(self, i: nat, va: nat, pte: PTE)
        requires
            i < self.entries.len(),
            #[trigger] self.interp_of_entry(i).contains_pair(va, pte),
            #[trigger] self.inv(),
        ensures
            self.entry_base(i) <= va < self.next_entry_base(i),
            self.entry_base(i) < va + pte.frame.size <= self.next_entry_base(i),
            //i <= self.entries.len() ==> self.interp_aux(i).lower == self.entry_base(i),
            //self.interp_aux(i).upper == self.upper_vaddr(),
            //i == 0 ==> self.interp_aux(0).lower == self.base_vaddr,
        decreases self, self.entries.len() - i, 0nat
    {
        assert(self.interp_of_entry(i).contains_key(va));
        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        match self.entries[i as int] {
            NodeEntry::Page(p)      => {},
            NodeEntry::Directory(d) => {
                assert(self.next_entry_base(i) == d.upper_vaddr()) by {
                    assert(self.directories_obey_invariant());
                    assert(self.arch.num_entries(self.layer + 1) * self.arch.entry_size(self.layer + 1) == self.arch.entry_size(self.layer)) by (nonlinear_arith)
                        requires
                            self.arch.inv(),
                            self.layer + 1 < self.arch.layers.len();
                };
                d.lemma_interp_aux_between(0, va, pte);
            },
            NodeEntry::Invalid      => {},
        }
    }

    pub broadcast proof fn lemma_interp_aux_between(self, i: nat, va: nat, pte: PTE)
        requires
            #[trigger] self.inv(),
            #[trigger] self.interp_aux(i).contains_pair(va, pte),
        ensures
            self.entry_base(i) <= va < self.upper_vaddr(),
            self.entry_base(i) < va + self.interp_aux(i)[va].frame.size <= self.upper_vaddr(),
        decreases self, self.entries.len() - i, 1nat
    {
        if i < self.entries.len() {
            indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
            if self.interp_of_entry(i).contains_pair(va, pte) {
                self.lemma_interp_of_entry_between(i, va, pte);
                assert(self.entry_base(i) <= va < self.upper_vaddr());
            } else {
                self.lemma_interp_aux_between(i + 1, va, pte);
            }
        }
    }

    pub broadcast proof fn lemma_interp_of_entry_key_between(self, i: nat, va: nat)
        requires
            i < self.entries.len(),
            #[trigger] self.interp_of_entry(i).contains_key(va),
            #[trigger] self.inv(),
        ensures
            self.entry_base(i) <= va < self.next_entry_base(i),
        decreases self, self.entries.len() - i, 0nat
    {
        self.lemma_interp_of_entry_between(i, va, self.interp_of_entry(i)[va]);
    }

    //pub proof fn lemma_inv_implies_interp_inv(self)
    //    requires
    //        self.inv(),
    //    ensures
    //        self.interp().inv(),
    //        self.interp().upper == self.upper_vaddr(),
    //        self.interp().lower == self.base_vaddr,
    //{
    //    self.lemma_inv_implies_interp_aux_inv(0);
    //}
    //
    //pub proof fn lemma_inv_implies_interp_aux_inv(self, i: nat)
    //    requires
    //        self.inv(),
    //    ensures
    //        self.interp_aux(i).inv(),
    //        i <= self.entries.len() ==> self.interp_aux(i).lower == self.entry_base(i),
    //        self.interp_aux(i).upper == self.upper_vaddr(),
    //        i == 0 ==> self.interp_aux(0).lower == self.base_vaddr,
    //    decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    //{
    //    broadcast use group_ambient;
    //
    //    let interp = self.interp_aux(i);
    //
    //    if i >= self.entries.len() {
    //    } else {
    //        assert(i < self.entries.len());
    //
    //        self.lemma_inv_implies_interp_aux_inv(i + 1);
    //
    //        assert(self.directories_obey_invariant());
    //
    //        let entry = self.entries.index(i as int);
    //        let entry_i = self.interp_of_entry(i);
    //        let rem = self.interp_aux(i+1);
    //
    //        match entry {
    //            NodeEntry::Page(p) => {}
    //            NodeEntry::Directory(d) => {
    //                d.lemma_inv_implies_interp_aux_inv(0);
    //            }
    //            NodeEntry::Invalid => { }
    //        }
    //
    //        assert(interp.mappings_are_of_valid_size());
    //
    //        if let NodeEntry::Page(pte) = entry {
    //            indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
    //            indexing::lemma_entry_base_from_index_support(self.base_vaddr, i, self.entry_size());
    //        }
    //
    //        assert(interp.mappings_are_aligned());
    //
    //        match entry {
    //            NodeEntry::Page(pte) => {
    //                assert_nonlinear_by({
    //                    requires([
    //                        self.inv(),
    //                        equal(entry_i, self.interp_of_entry(i)),
    //                        self.entry_size() == pte.frame.size,
    //                        i < self.entries.len(),
    //                    ]);
    //                    ensures(entry_i.candidate_mapping_in_bounds(self.entry_base(i), pte));
    //                });
    //            }
    //            NodeEntry::Directory(d) => {
    //                assert_nonlinear_by({
    //                    requires([
    //                        self.inv(),
    //                        equal(entry_i, self.interp_of_entry(i)),
    //                        d.interp_aux(0).inv(),
    //                        d.interp_aux(0).lower == self.entry_base(i),
    //                        d.base_vaddr == self.entry_base(i),
    //                        d.entry_size() * d.num_entries() == self.entry_size(),
    //                        d.interp_aux(0).upper == d.upper_vaddr(),
    //                        equal(self.interp_of_entry(i).map, d.interp_aux(0).map),
    //                        i < self.entries.len(),
    //                    ]);
    //                    ensures(entry_i.mappings_in_bounds());
    //                    assert(self.well_formed());
    //                    assert(entry_i.lower <= d.interp_aux(0).lower); // proof stability
    //                    assert(entry_i.upper >= d.interp_aux(0).upper); // proof stability
    //                });
    //            }
    //            NodeEntry::Invalid => {}
    //        }
    //        assert(entry_i.mappings_in_bounds());
    //
    //        assert(entry_i.inv());
    //
    //
    //        assert(self.interp_aux(i + 1).lower == self.entry_base(i + 1));
    //
    //        assert_nonlinear_by({
    //            requires([
    //                self.inv()),
    //                equal(rem, self.interp_aux(i + 1)),
    //                equal(entry_i, self.interp_of_entry(i)),
    //                self.interp_aux(i + 1).lower == self.entry_base(i + 1)
    //            ]);
    //            ensures(rem.ranges_disjoint(entry_i));
    //        });
    //        rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);
    //
    //        assert(interp.mappings_dont_overlap());
    //
    //        assert_nonlinear_by({
    //            requires([
    //                self.inv()),
    //                equal(interp, self.interp_aux(i)),
    //                equal(entry_i, self.interp_of_entry(i)),
    //                equal(rem, self.interp_aux(i + 1)),
    //                self.interp_aux(i + 1).lower == self.entry_base(i + 1),
    //                entry_i.upper == self.entry_base(i + 1),
    //                interp.upper == self.upper_vaddr(),
    //            ]);
    //            ensures([
    //                interp.lower <= entry_i.lower,
    //                interp.upper >= entry_i.upper,
    //                interp.lower <= self.interp_aux(i + 1).lower,
    //                interp.upper >= self.interp_aux(i + 1).upper,
    //            ]);
    //        });
    //
    //        assert(interp.mappings_in_bounds());
    //
    //        assert(interp.map.dom().finite());
    //
    //        if i == 0 {
    //            assert_nonlinear_by({
    //                requires([
    //                    self.inv()),
    //                    equal(entry_i, self.interp_of_entry(i)),
    //                    entry_i.lower == self.base_vaddr + i * self.entry_size(),
    //                    i == 0,
    //                ]);
    //                ensures(self.interp_aux(0).lower == self.base_vaddr);
    //            });
    //        }
    //    }
    //}

    pub proof fn lemma_empty_implies_interp_aux_empty(self, i: nat)
        requires
             self.inv(),
             self.empty(),
        ensures
            self.interp_aux(i) === Map::empty(),
            self.interp_aux(i).dom() === Set::empty(),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        if i >= self.entries.len() {
        } else {
            let rem = self.interp_aux(i + 1);
            let entry_i = self.interp_of_entry(i);
            self.lemma_empty_implies_interp_aux_empty(i + 1);
            assert(rem.union_prefer_right(entry_i) =~= Map::empty());
        }
    }

    pub proof fn lemma_empty_implies_interp_empty(self)
        requires
             self.inv(),
             self.empty()
        ensures
            self.interp() === Map::empty(),
            self.interp().dom() === Set::empty()
    {
        self.lemma_empty_implies_interp_aux_empty(0);
    }

    //proof fn lemma_ranges_disjoint_interp_aux_interp_of_entry(self)
    //    requires
    //        self.inv(),
    //    ensures
    //        forall|i: nat, j: nat|
    //            j < i && i < self.num_entries()
    //            ==> self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j)),
    //{
    //    assert_forall_by(|i: nat, j: nat| {
    //        requires(j < i && i < self.num_entries());
    //        ensures(self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j)));
    //        let interp  = self.interp_aux(i);
    //        let entry_j = self.interp_of_entry(j);
    //        self.lemma_inv_implies_interp_aux_inv(i);
    //        assert_nonlinear_by({
    //            requires(self.entry_size() > 0 && j < i);
    //            ensures(
    //                self.entry_base(j+1) <= self.entry_base(i) &&
    //                self.entry_base(i) > self.entry_base(j));
    //        });
    //    });
    //}

    #[verifier(spinoff_prover)]
    proof fn lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(self, i: nat, j: nat)
        requires
             self.inv(),
             i <= j,
             j < self.entries.len(),
        ensures
            forall|va: nat, pte: PTE| #![auto] self.interp_of_entry(j).contains_pair(va, pte) ==> self.interp_aux(i).contains_pair(va, pte),
            forall|va: nat| #![auto] self.interp_of_entry(j).contains_key(va) ==> self.interp_aux(i).contains_key(va),
            //forall|va: nat|
            //    between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).contains_key(va)
            //    ==> !self.interp_aux(i).contains_key(va),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
        indexing::lemma_entry_base_from_index(self.base_vaddr, j, self.entry_size());
        //self.lemma_inv_implies_interp_aux_inv(i+1);
        //self.lemma_inv_implies_interp_of_entry_inv(i);
        //self.lemma_inv_implies_interp_of_entry_inv(j);

        let rem = self.interp_aux(i + 1);
        let entry_i = self.interp_of_entry(i);

        if i != j {
            assert(i < j);
            self.lemma_interp_of_entry_disjoint_mappings(i, j);
            self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i+1, j);

            if let NodeEntry::Directory(d) = self.entries.index(i as int) {
                assert(self.directories_obey_invariant());
                assert(d.inv());
                //d.lemma_inv_implies_interp_inv();
                //self.lemma_ranges_disjoint_interp_aux_interp_of_entry();
                //rem.lemma_ranges_disjoint_implies_mappings_disjoint(entry_i);
            }

            assert forall|va: nat, pte: PTE| #![auto]
                self.interp_of_entry(j).contains_pair(va, pte) implies self.interp_aux(i).contains_pair(va, pte)
            by {
                assert(self.interp_aux(i + 1).contains_pair(va, pte));
                assert_by_contradiction!(!self.interp_of_entry(i).contains_key(va), {
                    let ppte = self.interp_aux(i)[va];
                    self.lemma_interp_of_entry_between(i, va, ppte);
                    self.lemma_interp_of_entry_between(j, va, pte);
                });
            };
        }
    }

    pub proof fn lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(self, j: nat)
        requires
             self.inv(),
             j < self.entries.len(),
        ensures
            forall|va: nat| #![auto] self.interp_of_entry(j).contains_key(va) ==> self.interp().contains_key(va),
            forall|va: nat, pte: PTE| #![auto] self.interp_of_entry(j).contains_pair(va, pte) ==> self.interp().contains_pair(va, pte),
            //forall|va: nat| #![auto]
            //    self.entry_base(j) <= va < self.entry_base(j+1) && !self.interp_of_entry(j).contains_key(va)
            //    ==> !self.interp().contains_key(va),
    {
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(0, j);
    }

    ////// TODO restore spec(checked) when recommends_by is fixed
    ////pub open spec fn resolve(self, vaddr: nat) -> Result<(nat, PTE),()>
    ////    recommends
    ////        self.inv(),
    ////        self.interp().accepted_resolve(vaddr),
    ////    decreases self.arch.layers.len() - self.layer
    ////{
    ////    decreases_when(self.inv() && self.interp().accepted_resolve(vaddr));
    ////    decreases_by(Self::check_resolve);
    ////
    ////    let entry = self.index_for_vaddr(vaddr);
    ////    match self.entries.index(entry as int) {
    ////        NodeEntry::Page(pte) => {
    ////            let offset = vaddr - self.entry_base(entry);
    ////            Ok((self.entry_base(entry), pte))
    ////        },
    ////        NodeEntry::Directory(d) => {
    ////            d.resolve(vaddr)
    ////        },
    ////        NodeEntry::Invalid => {
    ////            Err(())
    ////        },
    ////    }
    ////}
    ////
    ////#[verifier(decreases_by)]
    ////proof fn check_resolve(self, vaddr: nat) {
    ////    assert(self.inv() && self.interp().accepted_resolve(vaddr));
    ////
    ////    broadcast use group_ambient;
    ////    ambient_lemmas2();
    ////    self.lemma_inv_implies_interp_inv();
    ////
    ////    assert(between(vaddr, self.base_vaddr, self.upper_vaddr()));
    ////    let entry = self.index_for_vaddr(vaddr);
    ////    indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());
    ////    // TODO: This makes the recommends failure on the line below go away but not the one in the
    ////    // corresponding spec function. wtf
    ////    assert(0 <= entry < self.entries.len());
    ////    match self.entries.index(entry as int) {
    ////        NodeEntry::Page(p) => {
    ////        },
    ////        NodeEntry::Directory(d) => {
    ////            d.lemma_inv_implies_interp_inv();
    ////            assert(d.inv());
    ////        },
    ////        NodeEntry::Invalid => {
    ////        },
    ////    }
    ////}

    proof fn lemma_interp_aux_contains_implies_interp_of_entry_contains(self, j: nat)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PTE|
                self.interp_aux(j).contains_pair(base, pte) ==>
                exists|i: nat| #![auto] j <= i < self.num_entries() && self.interp_of_entry(i).contains_pair(base, pte),
            forall|base: nat|
                self.interp_aux(j).contains_key(base) ==>
                exists|i: nat| #![auto] j <= i < self.num_entries() && self.interp_of_entry(i).contains_key(base)
        decreases self.arch.layers.len() - self.layer, self.num_entries() - j
    {
        if j >= self.entries.len() {
        } else {
            let _ = self.interp_of_entry(j);
            self.lemma_interp_aux_contains_implies_interp_of_entry_contains(j+1);
            assert forall|base: nat, pte: PTE| #![auto]
                self.interp_aux(j).contains_pair(base, pte) implies
                exists|i: nat| #![auto] j <= i < self.num_entries() && self.interp_of_entry(i).contains_pair(base, pte) by {
                if self.interp_aux(j+1).contains_pair(base, pte) { } else { }
            };
            assert forall|base: nat| #![auto]
                self.interp_aux(j).contains_key(base) implies
                exists|i: nat| #![auto] j <= i < self.num_entries() && self.interp_of_entry(i).contains_key(base) by {
                if self.interp_aux(j+1).contains_key(base) { } else { }
            };
        }
    }

    pub proof fn lemma_interp_contains_implies_interp_of_entry_contains(self)
        requires
            self.inv(),
        ensures
            forall|base: nat, pte: PTE|
                self.interp().contains_pair(base, pte) ==>
                exists|i: nat| #![auto] i < self.num_entries() && self.interp_of_entry(i).contains_pair(base, pte),
            forall|base: nat|
                self.interp().contains_key(base) ==>
                exists|i: nat| #![auto] i < self.num_entries() && self.interp_of_entry(i).contains_key(base),
    {
        self.lemma_interp_aux_contains_implies_interp_of_entry_contains(0);
    }

    //#[verifier(spinoff_prover)]
    //proof fn lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(self, vaddr: nat, i: nat)
    //    requires
    //        self.inv(),
    //        i < self.num_entries(),
    //        self.entry_base(i) <= vaddr < self.next_entry_base(i),
    //        !exists|base: nat, pte: PTE|
    //            self.interp_of_entry(i).contains_pair(base, pte) &&
    //            base <= vaddr < base + pte.frame.size,
    //    ensures
    //        !exists|base: nat, pte: PTE|
    //            self.interp().contains_pair(base, pte) &&
    //            base <= vaddr < base + pte.frame.size,
    //{
    //    assert(0 < self.arch.entry_size(self.layer));
    //    assert forall|idx: nat, idx2: nat, base: nat, layer: nat|
    //        layer < self.arch.layers.len() && idx < idx2
    //        implies self.arch.entry_base(layer, base, idx) <  self.arch.entry_base(layer, base, idx2)
    //    by { indexing::lemma_entry_base_from_index(base, idx, self.arch.entry_size(layer)); };
    //    self.lemma_interp_of_entry();
    //    self.lemma_interp_contains_implies_interp_of_entry_contains();
    //
    //    assert(self.directories_obey_invariant());
    //    assert_by_contradiction!(
    //        !exists|base: nat, pte: PTE|
    //            self.interp().contains_pair(base, pte) &&
    //            base <= vaddr < base + pte.frame.size,
    //    {
    //        let (base, pte) = choose|base: nat, pte: PTE|
    //                self.interp().contains_pair(base, pte) &&
    //                base <= vaddr < base + pte.frame.size;
    //        //let p = self.interp()[base];
    //        //assert(self.interp().contains_pair(base, p));
    //        //assert(self.interp().contains_key(base));
    //        //assert(self.interp()[base] == p);
    //        broadcast use Directory::lemma_interp_of_entry_between;
    //        assert(
    //        assert(self.interp_of_entry(i).contains_pair(base, pte));
    //    });
    //    //if exists|base:nat|
    //    //    self.interp().contains_key(base) &&
    //    //    base <= vaddr < base + (#[trigger] self.interp()[base]).frame.size {
    //    //    let base = choose|base:nat|
    //    //                      self.interp().contains_key(base) &&
    //    //                      base <= vaddr < base + (#[trigger] self.interp()[base]).frame.size;
    //    //    let p = self.interp()[base];
    //    //    assert(self.interp().contains_pair(base, p));
    //    //    assert(self.interp().contains_key(base));
    //    //    assert(self.interp()[base] == p);
    //    //}
    //}

    //#[verifier(spinoff_prover)]
    //pub proof fn lemma_resolve_structure_assertions(self, vaddr: nat, idx: nat)
    //    requires
    //        self.inv(),
    //        self.interp().accepted_resolve(vaddr),
    //        idx == self.index_for_vaddr(vaddr),
    //    ensures
    //        self.entries.index(idx as int) is Directory ==> {
    //            let d = self.entries.index(idx as int)->Directory_0;
    //            &&& d.interp().accepted_resolve(vaddr)
    //            &&& d.inv()
    //        },
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());
    //
    //    match self.entries.index(idx as int) {
    //        NodeEntry::Page(p) => { },
    //        NodeEntry::Directory(d) => {
    //            d.lemma_inv_implies_interp_inv();
    //            assert(d.interp().accepted_resolve(vaddr));
    //        },
    //        NodeEntry::Invalid => { },
    //    }
    //}
    //
    //#[verifier(spinoff_prover)]
    //pub proof fn lemma_resolve_refines(self, vaddr: nat)
    //    requires
    //        self.inv(),
    //        self.interp().accepted_resolve(vaddr),
    //    ensures
    //        equal(self.interp().resolve(vaddr), self.resolve(vaddr)),
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //    self.lemma_inv_implies_interp_inv();
    //
    //    let entry = self.index_for_vaddr(vaddr);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, vaddr, self.entry_size(), self.num_entries());
    //    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => {
    //            assert(self.resolve(vaddr).is_Ok());
    //            let p_vaddr = self.entry_base(entry);
    //            assert(self.interp().map.contains_pair(p_vaddr, p));
    //            assert(vaddr < p_vaddr + self.interp().map.index(p_vaddr).frame.size);
    //        },
    //        NodeEntry::Directory(d) => {
    //            d.lemma_inv_implies_interp_inv();
    //            assert(d.interp().accepted_resolve(vaddr));
    //            d.lemma_resolve_refines(vaddr);
    //
    //            assert(equal(self.interp_of_entry(entry), d.interp()));
    //
    //            assert(equal(d.interp().resolve(vaddr), d.resolve(vaddr)));
    //
    //            if d.resolve(vaddr).is_Ok() {
    //                assert(self.resolve(vaddr).is_Ok());
    //                assert(exists|base: nat|
    //                       d.interp().map.contains_key(base) &&
    //                       between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size));
    //
    //                let base = choose|base:nat|
    //                                d.interp().map.contains_key(base) &&
    //                                between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size);
    //
    //                assert(self.interp().map.contains_pair(base, self.interp_of_entry(entry).map.index(base)));
    //
    //                assert(d.resolve(vaddr).is_Ok());
    //                assert(d.interp().resolve(vaddr).is_Ok());
    //                assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
    //            } else {
    //                assert(d.resolve(vaddr).is_Err());
    //                assert(self.resolve(vaddr).is_Err());
    //
    //                assert(d.interp().resolve(vaddr).is_Err());
    //                assert(!exists|base:nat|
    //                       d.interp().map.contains_key(base) &&
    //                       between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size)) by
    //                {
    //                    assert(!exists|base:nat, pte:PTE|
    //                                d.interp().map.contains_pair(base, pte) &&
    //                                between(vaddr, base, base + pte.frame.size));
    //                    if exists|base:nat|
    //                       d.interp().map.contains_key(base) &&
    //                       between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size) {
    //                       let base = choose|base:nat|
    //                           d.interp().map.contains_key(base) &&
    //                           between(vaddr, base, base + (#[trigger] d.interp().map.index(base)).frame.size);
    //                       let pte = d.interp().map.index(base);
    //                       assert(d.interp().map.contains_pair(base, pte));
    //                   }
    //                };
    //                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(vaddr, entry, true);
    //            }
    //            assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
    //        },
    //        NodeEntry::Invalid => {
    //            assert(self.resolve(vaddr).is_Err());
    //            self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(vaddr, entry, true);
    //            assert(self.interp().resolve(vaddr).is_Err());
    //        },
    //    }
    //}

    pub open spec(checked) fn update(self, n: nat, e: NodeEntry) -> Self
        recommends n < self.entries.len()
    {
        Directory {
            entries: self.entries.update(n as int, e),
            ..self
        }
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(self, base: nat, pte: PTE) -> bool
        recommends self.well_formed()
    {
        self.base_vaddr <= base && base + pte.frame.size <= self.upper_vaddr()
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, pte: PTE) -> bool
        recommends self.well_formed()
    {
        &&& aligned(base, pte.frame.size)
        &&& aligned(pte.frame.base, pte.frame.size)
        &&& self.candidate_mapping_in_bounds(base, pte)
        &&& self.arch.contains_entry_size_at_index_atleast(pte.frame.size, self.layer)
    }

    //pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_manual(self, base: nat, pte: PTE)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte)
    //    ensures
    //        self.interp().accepted_mapping(base, pte),
    //{
    //    self.lemma_inv_implies_interp_inv();
    //}
    //
    //pub proof fn lemma_accepted_mapping_implies_interp_accepted_mapping_auto(self)
    //    ensures
    //        forall|base: nat, pte: PTE|
    //            #[trigger] self.inv() && #[trigger] self.accepted_mapping(base, pte) ==>
    //            self.interp().accepted_mapping(base, pte),
    //{
    //    assert_forall_by(|base: nat, pte: PTE| {
    //        requires(#[trigger] self.inv() && #[trigger] self.accepted_mapping(base, pte));
    //        ensures(self.interp().accepted_mapping(base, pte));
    //
    //        self.lemma_accepted_mapping_implies_interp_accepted_mapping_manual(base, pte);
    //    });
    //}

    // Creates new empty directory to map to entry 'entry'
    pub open spec fn new_empty_dir(self, entry: nat) -> Self
        recommends
            //self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
    {
        Directory {
            entries:    new_seq(self.arch.num_entries((self.layer + 1) as nat), NodeEntry::Invalid),
            layer:      self.layer + 1,
            base_vaddr: self.entry_base(entry),
            arch:       self.arch,
        }
    }

    pub proof fn lemma_new_empty_dir(self, entry: nat)
        requires
            self.inv(),
            entry < self.num_entries(),
            self.layer + 1 < self.arch.layers.len(),
        ensures
            self.new_empty_dir(entry).inv(),
            self.new_empty_dir(entry).entries.len() == self.arch.num_entries((self.layer + 1) as nat),
            forall|j: nat| j < self.new_empty_dir(entry).num_entries() ==> equal(self.new_empty_dir(entry).entries.index(j as int), NodeEntry::Invalid),
    {
        let new_dir = self.new_empty_dir(entry);
        let num_entries = self.arch.num_entries((self.layer + 1) as nat);
        indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
        indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
        lemma_new_seq::<NodeEntry>(num_entries, NodeEntry::Invalid);

        assert(new_dir.directories_obey_invariant());
        assert(new_dir.well_formed());
        assert(new_dir.inv());
    }

    pub open spec fn map_frame(self, base: nat, pte: PTE) -> Result<Directory,Directory>
        decreases self.arch.layers.len() - self.layer via Self::check_map_frame
    {

        if self.inv() && self.accepted_mapping(base, pte) {
            let entry = self.index_for_vaddr(base);
            match self.entries.index(entry as int) {
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
                NodeEntry::Invalid => {
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
    proof fn check_map_frame(self, base: nat, pte: PTE) {
        broadcast use group_ambient;
        ambient_lemmas2(); // TODO: unnecessary?
        //self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
        if self.inv() && self.accepted_mapping(base, pte) {
            indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
        }
    }

    //pub proof fn lemma_accepted_mapping_implies_directory_accepted_mapping(self, base: nat, pte: PTE, d: Directory)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte),
    //        equal(d.arch, self.arch),
    //        d.base_vaddr == self.entry_base(self.index_for_vaddr(base)),
    //        d.upper_vaddr() == self.entry_base(self.index_for_vaddr(base)+1),
    //        d.inv(),
    //        d.layer == self.layer + 1,
    //        self.entry_size() != pte.frame.size,
    //    ensures
    //        d.accepted_mapping(base, pte),
    //{
    //    broadcast use group_ambient;
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //    self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
    //    assert(self.directories_obey_invariant());
    //    assert(d.inv());
    //
    //    assert(aligned(base, pte.frame.size));
    //    assert(aligned(pte.frame.base, pte.frame.size));
    //    assert(d.arch.contains_entry_size_at_index_atleast(pte.frame.size, d.layer));
    //
    //    assert(self.entry_base(entry) <= base);
    //    assert(aligned(base, pte.frame.size));
    //    self.arch.lemma_entry_sizes_aligned_auto();
    //    assert(aligned(self.entry_size(), pte.frame.size));
    //
    //    extra::aligned_transitive_auto();
    //    assert(aligned(self.next_entry_base(entry), pte.frame.size));
    //    extra::leq_add_aligned_less(base, pte.frame.size, self.entry_base(entry+1));
    //    assert(base + pte.frame.size <= self.entry_base(entry+1));
    //    assert(base + pte.frame.size <= self.entry_base(entry) + self.entry_size());
    //    assert(base + pte.frame.size <= d.base_vaddr + self.entry_size());
    //    assert(base + pte.frame.size <= d.base_vaddr + d.num_entries() * d.entry_size());
    //    assert(base + pte.frame.size <= d.upper_vaddr());
    //    assert(d.candidate_mapping_in_bounds(base, pte));
    //    assert(aligned(base, pte.frame.size));
    //    assert(aligned(pte.frame.base, pte.frame.size));
    //}
    //
    //proof fn lemma_map_frame_empty_is_ok(self, base: nat, pte: PTE)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte),
    //        self.entries.index(self.index_for_vaddr(base) as int) is Invalid,
    //    ensures
    //        self.map_frame(base, pte).is_Ok(),
    //        // self.new_empty_dir(self.index_for_vaddr(base)).map_frame(base, pte).is_Ok()
    //    decreases self.arch.layers.len() - self.layer;
    //
    //pub proof fn lemma_map_frame_preserves_inv(self, base: nat, pte: PTE)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte),
    //        self.map_frame(base, pte).is_Ok(),
    //    ensures
    //        self.map_frame(base, pte).get_Ok_0().layer === self.layer,
    //        self.map_frame(base, pte).get_Ok_0().arch === self.arch,
    //        self.map_frame(base, pte).get_Ok_0().base_vaddr === self.base_vaddr,
    //        !self.map_frame(base, pte).get_Ok_0().empty(),
    //        self.map_frame(base, pte).get_Ok_0().inv(),
    //        !exists|b:nat| true
    //            && self.interp().map.contains_key(b)
    //            && between(base, b, b + (#[trigger] self.interp().map.index(b)).frame.size),
    //
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //    self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //
    //    let res = self.map_frame(base, pte).get_Ok_0();
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => (),
    //        NodeEntry::Directory(d) => {
    //            if self.entry_size() == pte.frame.size {
    //            } else {
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d, true);
    //                d.lemma_inv_implies_interp_inv();
    //                assert(d.inv());
    //                d.lemma_map_frame_preserves_inv(base, pte);
    //                assert(res.well_formed());
    //                assert(res.pages_match_entry_size());
    //                assert(res.directories_match_arch());
    //                // assert_forall_by(|i: nat| {
    //                //     requires(i < res.entries.len() && res.entries.index(i as int) is
    //                //     Directory);
    //                //     ensures(true
    //                //             && (#[trigger] res.entries.index(i as int))->Directory_0.layer == res.layer + 1
    //                //             && res.entries.index(i as int)->Directory_0.base_vaddr == res.base_vaddr + i * res.entry_size());
    //                //     if i < res.entries.len() && res.entries.index(i as int) is Directory {
    //                //         if i == entry {
    //                //         }
    //                //     }
    //                // });
    //                assert(res.directories_are_in_next_layer());
    //                assert(res.directories_obey_invariant(true));
    //                assert(res.directories_are_nonempty());
    //                assert(res.inv());
    //                assert(equal(self.map_frame(base, pte).get_Ok_0().layer, self.layer));
    //
    //                assert(res.entries.index(entry as int) is Directory);
    //                assert(!res.empty());
    //                self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry, true);
    //            }
    //        },
    //        NodeEntry::Invalid => {
    //            self.lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(base, entry, true);
    //            if self.entry_size() == pte.frame.size {
    //                assert(equal(res.layer, self.layer));
    //                assert(res.entries.index(entry as int) is Page);
    //                assert(!res.empty());
    //                assert(res.directories_are_in_next_layer());
    //                assert(res.directories_obey_invariant(true));
    //                assert(res.inv());
    //            } else {
    //                assert(((self.layer + 1) as nat) < self.arch.layers.len());
    //                let new_dir = self.new_empty_dir(entry);
    //                self.lemma_new_empty_dir(entry, true);
    //
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir, true);
    //                new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //                assert(new_dir.accepted_mapping(base, pte));
    //                indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());
    //                new_dir.lemma_map_frame_empty_is_ok(base, pte);
    //                new_dir.lemma_map_frame_preserves_inv(base, pte);
    //
    //                assert(res.directories_are_in_next_layer());
    //                assert(res.directories_obey_invariant(true));
    //                assert(res.directories_are_nonempty());
    //                assert(res.frames_aligned());
    //                assert(res.inv());
    //                assert(equal(res.layer, self.layer));
    //                assert(res.entries.index(entry as int) is Directory);
    //                assert(!res.empty());
    //                assert(new_dir.map_frame(base, pte).is_Ok());
    //            }
    //        },
    //    }
    //}

    //proof fn lemma_insert_interp_of_entry_implies_insert_interp_aux(self, i: nat, j: nat, base: nat, n: NodeEntry, pte: PTE)
    //    requires
    //        self.inv(),
    //        i <= j,
    //        j < self.num_entries(),
    //        !self.interp_aux(i).contains_key(base),
    //        self.update(j, n).inv(),
    //        equal(
    //            self.interp_of_entry(j).insert(base, pte),
    //            match n {
    //                NodeEntry::Page(p)      => map![self.entry_base(j) => p],
    //                NodeEntry::Directory(d) => d.interp_aux(0),
    //                NodeEntry::Invalid      => map![],
    //            }),
    //    ensures
    //        self.interp_aux(i).insert(base, pte) == self.update(j, n).interp_aux(i),
    //    decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //
    //    //self.lemma_inv_implies_interp_aux_inv(i);
    //    //self.lemma_inv_implies_interp_aux_inv(i + 1);
    //    //self.lemma_inv_implies_interp_of_entry_inv(i);
    //    //self.lemma_inv_implies_interp_of_entry_inv(j);
    //
    //    //self.lemma_interp_of_entry();
    //    //self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);
    //
    //    let nself = self.update(j, n);
    //
    //    if i >= self.entries.len() {
    //    } else {
    //        //if i == j {
    //        //    assert(!self.interp_aux(i + 1).map.contains_key(base));
    //        //    assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));
    //        //
    //        //    assert(equal(self.interp_of_entry(i).map.insert(base, pte), nself.interp_of_entry(i).map));
    //        //    self.lemma_entries_equal_implies_interp_aux_equal(nself, i+1);
    //        //    assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));
    //        //
    //        //
    //        //    assert(!self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).contains_key(base));
    //        //
    //        //    assert(equal(self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).insert(base, pte),
    //        //                 self.update(j, n).interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));
    //        //
    //        //    assert(equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map));
    //        //} else {
    //        //    assert(i < j);
    //        //    assert(self.directories_obey_invariant());
    //        //
    //        //    self.lemma_insert_interp_of_entry_implies_insert_interp_aux(i + 1, j, base, n, pte);
    //        //    self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i + 1, j);
    //        //    assert(!self.interp_of_entry(j).map.contains_key(base));
    //        //
    //        //    assert(!self.interp_aux(i).map.contains_key(base));
    //        //
    //        //    assert(equal(self.interp_aux(i + 1).map.insert(base, pte), self.update(j, n).interp_aux(i + 1).map));
    //        //
    //        //    assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));
    //        //
    //        //    assert(nself.inv());
    //        //    assert(equal(nself.interp_aux(i).map, nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));
    //        //
    //        //    assert(equal(self.interp_aux(i).map.insert(base, pte), self.update(j, n).interp_aux(i).map));
    //        //}
    //    }
    //}

    proof fn lemma_interp_of_entry_insert_implies_interp_aux_insert(self, i: nat, j: nat, base: nat, n: NodeEntry, pte: PTE)
        requires
            self.inv(),
            i <= j,
            j < self.num_entries(),
            // !self.interp_aux(i).contains_key(base),
            self.update(j, n).inv(),
            self.interp_of_entry(j).insert(base, pte) == self.update(j, n).interp_of_entry(j),
        ensures
            self.interp_aux(i).insert(base, pte) == self.update(j, n).interp_aux(i),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        broadcast use group_ambient;

        let nself = self.update(j, n);

        if i >= self.entries.len() {
        } else {
            if i == j {
                //assert(!self.interp_aux(i + 1).contains_key(base));
                assert(self.interp_aux(i) == self.interp_aux(i + 1).union_prefer_right(self.interp_of_entry(i)));

                assert(self.interp_of_entry(i).insert(base, pte) == nself.interp_of_entry(i));
                self.lemma_entries_interp_equal_implies_interp_aux_equal(nself, i+1);
            } else {
                assert(i < j);
                assert(self.directories_obey_invariant());

                self.lemma_interp_of_entry_insert_implies_interp_aux_insert(i + 1, j, base, n, pte);
                assert_by_contradiction!(!self.interp_of_entry(i).contains_key(base), {
                    let ppte = self.interp_of_entry(i)[base];
                    self.update(j, n).lemma_interp_aux_between(i + 1, base, pte);
                    assert(self.entry_base(i + 1) <= base);
                    self.lemma_interp_of_entry_between(i, base, ppte);
                });
                assert(self.interp_aux(i + 1).insert(base, pte) == self.update(j, n).interp_aux(i + 1));
                assert(nself.interp_aux(i) == nself.interp_aux(i + 1).union_prefer_right(nself.interp_of_entry(i)));
                assert(self.interp_aux(i).insert(base, pte) == self.update(j, n).interp_aux(i));
            }
        }
    }

    pub proof fn lemma_interp_entries_insert_implies_interp_insert(self, j: nat, base: nat, n: NodeEntry, pte: PTE)
        requires
            self.inv(),
            j < self.num_entries(),
            // !self.interp_aux(i).contains_key(base),
            self.update(j, n).inv(),
            self.entries[j as int].interp(self.entry_base(j)).insert(base, pte) == n.interp(self.entry_base(j))
        ensures
            self.interp().insert(base, pte) == self.update(j, n).interp(),
    {
        self.lemma_interp_of_entry_insert_implies_interp_aux_insert(0, j, base, n, pte);
    }

    pub proof fn lemma_interp_of_entry_insert_implies_interp_insert(self, j: nat, base: nat, n: NodeEntry, pte: PTE)
        requires
            self.inv(),
            j < self.num_entries(),
            // !self.interp_aux(i).contains_key(base),
            self.update(j, n).inv(),
            self.interp_of_entry(j).insert(base, pte) == self.update(j, n).interp_of_entry(j),
        ensures
            self.interp().insert(base, pte) == self.update(j, n).interp(),
    {
        self.lemma_interp_of_entry_insert_implies_interp_aux_insert(0, j, base, n, pte);
    }

    pub proof fn lemma_interp_of_entry_insert_page_implies_interp_insert_page(self, j: nat, base: nat, pte: PTE)
        requires
            self.inv(),
            j < self.num_entries(),
            // !self.interp().contains_key(base),
            //self.entries[j as int] is Invalid,
            self.update(j, NodeEntry::Page(pte)).inv(),
            self.interp_of_entry(j).insert(base, pte) == self.update(j, NodeEntry::Page(pte)).interp_of_entry(j),
        ensures
            self.interp().insert(base, pte) == self.update(j, NodeEntry::Page(pte)).interp(),
    {
        self.lemma_interp_of_entry_insert_implies_interp_aux_insert(0, j, base, NodeEntry::Page(pte), pte);
    }

    pub proof fn lemma_interp_entries_remove_implies_interp_remove(self, other: Directory, idx: nat, vaddr: nat)
        requires
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            self.entry_base(idx) <= vaddr < self.next_entry_base(idx),
            idx < self.num_entries(),
            other.entries[idx as int].interp(self.entry_base(idx)) == self.entries[idx as int].interp(self.entry_base(idx)).remove(vaddr),
            forall|i| 0 <= i < self.num_entries() && i != idx ==> other.entries[i] == self.entries[i],
        ensures
            other.interp() == self.interp().remove(vaddr),
    {
        if self.entries[idx as int].interp(self.entry_base(idx)).contains_key(vaddr) {
            self.lemma_entries_interp_remove_implies_interp_aux_remove(other, idx, vaddr, 0);
        } else {
            assert(self.entries[idx as int].interp(self.entry_base(idx)) =~= other.entries[idx as int].interp(self.entry_base(idx)));
            self.lemma_entries_interp_equal_implies_interp_equal(other);
            assert_by_contradiction!(!self.interp().contains_key(vaddr), {
                self.lemma_interp_contains_implies_interp_of_entry_contains();
                assert(exists|j: nat| #![auto] j < self.num_entries() && self.interp_of_entry(j).contains_key(vaddr));
                let j = choose|j: nat| #![auto] j < self.num_entries() && self.interp_of_entry(j).contains_key(vaddr);
                self.lemma_interp_of_entry_key_between(j, vaddr);
                assert(j == idx) by (nonlinear_arith)
                    requires
                        self.entry_base(j) <= vaddr < self.next_entry_base(j),
                        self.entry_base(idx) <= vaddr < self.next_entry_base(idx),
                {};
            });
            assert(other.interp() =~= self.interp().remove(vaddr));
        }
    }

    proof fn lemma_entries_interp_remove_implies_interp_aux_remove(self, other: Directory, idx: nat, vaddr: nat, i: nat)
        requires
            idx < self.entries.len(),
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            // This precondition isn't really necessary
            self.entries[idx as int].interp(self.entry_base(idx)).contains_key(vaddr),
            other.entries[idx as int].interp(self.entry_base(idx)) == self.entries[idx as int].interp(self.entry_base(idx)).remove(vaddr),
            forall|j: nat| i <= j < self.entries.len() && j != idx
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j))
                            == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            if idx < i {
                other.interp_aux(i) === self.interp_aux(i)
            } else {
                other.interp_aux(i) === self.interp_aux(i).remove(vaddr)
            }
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        self.lemma_interp_of_entry_key_between(idx, vaddr);
        assert(self.entry_base(idx) <= vaddr < self.next_entry_base(idx));
        indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
        if i >= self.entries.len() {
        } else {
            let rem1 = self.interp_aux(i + 1);
            let rem2 = other.interp_aux(i + 1);
            let entry_i1 = self.interp_of_entry(i);
            let entry_i2 = other.interp_of_entry(i);
            if idx < i {
                self.lemma_entries_interp_remove_implies_interp_aux_remove(other, idx, vaddr, i + 1);
                assert(rem1.union_prefer_right(entry_i1) =~= rem2.union_prefer_right(entry_i2));
            } else if idx == i {
                self.lemma_entries_interp_remove_implies_interp_aux_remove(other, idx, vaddr, i + 1);
                assert_by_contradiction!(!rem2.contains_key(vaddr), {
                    self.lemma_interp_aux_contains_implies_interp_of_entry_contains(i + 1);
                    assert(exists|j: nat| #![auto] i + 1 <= j < self.num_entries() && self.interp_of_entry(j).contains_key(vaddr));
                    let j = choose|j: nat| #![auto] i + 1 <= j < self.num_entries() && self.interp_of_entry(j).contains_key(vaddr);
                    self.lemma_interp_of_entry_key_between(j, vaddr);
                    assert(self.entry_base(j) <= vaddr < self.next_entry_base(j));
                });
                assert(rem2.union_prefer_right(entry_i2) =~= rem1.union_prefer_right(entry_i1).remove(vaddr));
            } else {
                self.lemma_entries_interp_remove_implies_interp_aux_remove(other, idx, vaddr, i + 1);
                assert_by_contradiction!(!entry_i1.contains_key(vaddr), {
                    self.lemma_interp_of_entry_key_between(i, vaddr);
                    assert(self.entry_base(i) <= vaddr < self.next_entry_base(i));
                    indexing::lemma_entry_base_from_index(self.base_vaddr, i, self.entry_size());
                });
                assert(rem2.union_prefer_right(entry_i2) =~= rem1.union_prefer_right(entry_i1).remove(vaddr));
            }
        }
    }

    //proof fn lemma_insert_interp_of_entry_implies_insert_interp(self, j: nat, base: nat, n: NodeEntry, pte: PTE)
    //    requires
    //        self.inv(),
    //        j < self.num_entries(),
    //        !self.interp().map.contains_key(base),
    //        self.update(j, n).inv(),
    //        equal(
    //            self.interp_of_entry(j).map.insert(base, pte),
    //            match n {
    //                NodeEntry::Page(p)      => map![self.entry_base(j) => p],
    //                NodeEntry::Directory(d) => d.interp_aux(0).map,
    //                NodeEntry::Invalid      => map![],
    //            }),
    //    ensures
    //        self.interp().map.insert(base, pte) == self.update(j, n).interp().map,
    //    decreases
    //        self.arch.layers.len() - self.layer,
    //{
    //    self.lemma_insert_interp_of_entry_implies_insert_interp_aux(0, j, base, n, pte);
    //}

    pub proof fn lemma_nonempty_implies_interp_contains(self)
        requires
            self.inv(),
            self.no_empty_directories(),
            !self.empty(),
        ensures
            exists|b: nat, pte: PTE|
                self.interp().contains_pair(b, pte)
                && self.arch.contains_entry_size_at_index_atleast(pte.frame.size, self.layer)
        decreases self.arch.layers.len() - self.layer
    {
        let i = choose|i: nat| i < self.num_entries() && self.entries[i as int] !is Invalid;
        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(i);
        match self.entries[i as int] {
            NodeEntry::Page(pte) => {
                assert(self.interp().contains_pair(self.entry_base(i), pte));
            },
            NodeEntry::Directory(d) => {
                d.lemma_nonempty_implies_interp_contains();
                let (b, pte) = choose|b: nat, pte: PTE|
                    d.interp().contains_pair(b, pte)
                    && d.arch.contains_entry_size_at_index_atleast(pte.frame.size, d.layer);
                assert(self.interp().contains_pair(b, pte));
            },
            NodeEntry::Invalid => {},
        }
    }

    //pub proof fn lemma_map_frame_structure_assertions(self, base: nat, pte: PTE, idx: nat)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte),
    //        idx == self.index_for_vaddr(base),
    //    ensures
    //        match self.entries.index(idx as int) {
    //            NodeEntry::Page(p)      => true,
    //            NodeEntry::Directory(d) => {
    //                &&& d.inv()
    //                &&& if self.entry_size() == pte.frame.size {
    //                    true
    //                } else {
    //                    d.accepted_mapping(base, pte)
    //                }
    //            },
    //            NodeEntry::Invalid      => {
    //                if self.entry_size() == pte.frame.size {
    //                    true
    //                } else {
    //                    &&& ((self.layer + 1) as nat) < self.arch.layers.len()
    //                    &&& self.new_empty_dir(idx).inv()
    //                    &&& self.new_empty_dir(idx).accepted_mapping(base, pte)
    //                    &&& self.new_empty_dir(idx).map_frame(base, pte).is_Ok()
    //                }
    //            },
    //        }
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //    self.lemma_inv_implies_interp_inv();
    //    self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //
    //    let res = self.map_frame(base, pte).get_Ok_0();
    //    if self.map_frame(base, pte).is_Ok() {
    //        self.lemma_map_frame_preserves_inv(base, pte);
    //    }
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => { },
    //        NodeEntry::Directory(d) => {
    //            assert(d.inv());
    //            if self.entry_size() == pte.frame.size {
    //            } else {
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d, true);
    //                assert(d.accepted_mapping(base, pte));
    //            }
    //        },
    //        NodeEntry::Invalid => {
    //            if self.entry_size() == pte.frame.size {
    //            } else {
    //                assert(((self.layer + 1) as nat) < self.arch.layers.len());
    //                let new_dir = self.new_empty_dir(entry);
    //                self.lemma_new_empty_dir(entry, true);
    //                assert(new_dir.inv());
    //
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir, true);
    //                new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //                assert(new_dir.accepted_mapping(base, pte));
    //                indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());
    //
    //                new_dir.lemma_map_frame_refines_map_frame(base, pte);
    //                assert(new_dir.interp().map_frame(base, pte).is_Ok());
    //            }
    //        },
    //    }
    //}

    //pub proof fn lemma_map_frame_refines_map_frame(self, base: nat, pte: PTE)
    //    requires
    //        self.inv(),
    //        self.accepted_mapping(base, pte),
    //    ensures
    //        self.map_frame(base, pte).is_Err() ==> self.map_frame(base, pte).get_Err_0() === self,
    //        result_map(self.map_frame(base, pte), |d: Directory| d.interp()) === self.interp().map_frame(base, pte),
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //    self.lemma_inv_implies_interp_inv();
    //    self.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //    assert(aligned(self.base_vaddr, self.entry_size())) by {
    //        extra::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
    //    };
    //
    //    let res = self.map_frame(base, pte).get_Ok_0();
    //    if self.map_frame(base, pte).is_Ok() {
    //        self.lemma_map_frame_preserves_inv(base, pte);
    //    }
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => {
    //            assert(self.map_frame(base, pte).is_Err());
    //
    //            assert(self.interp_of_entry(entry).map.contains_pair(self.entry_base(entry), p));
    //            assert(self.interp().map.contains_pair(self.entry_base(entry), p));
    //            assert(self.interp().map_frame(base, pte).is_Err());
    //        },
    //        NodeEntry::Directory(d) => {
    //            d.lemma_inv_implies_interp_inv();
    //            assert(d.inv());
    //            if self.entry_size() == pte.frame.size {
    //                assert(self.map_frame(base, pte).is_Err());
    //                d.lemma_nonempty_implies_interp_contains();
    //                let b = choose|b: nat| d.interp().map.contains_key(b);
    //                assert(self.interp().map.contains_key(b));
    //                self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //
    //                assert(!self.interp().valid_mapping(base, pte));
    //                assert(self.interp().map_frame(base, pte).is_Err());
    //            } else {
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, d, true);
    //                assert(d.accepted_mapping(base, pte));
    //                d.lemma_map_frame_refines_map_frame(base, pte);
    //                assert(equal(result_map(d.map_frame(base, pte), |d: Directory| d.interp()), d.interp().map_frame(base, pte)));
    //                match d.map_frame(base, pte) {
    //                    Ok(nd)  => {
    //                        assert(d.map_frame(base, pte).is_Ok());
    //                        assert(d.interp().map_frame(base, pte).is_Ok());
    //                        assert(d.interp().accepted_mapping(base, pte));
    //                        assert(d.interp().valid_mapping(base, pte));
    //                        assert(self.interp().accepted_mapping(base, pte));
    //                        assert(self.interp().valid_mapping(base, pte));
    //                        assert(self.map_frame(base, pte).is_Ok());
    //                        self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(nd), pte, true);
    //                        assert(self.interp().map_frame(base, pte).is_Ok());
    //
    //                        assert(equal(self.interp().map.insert(base, pte), self.update(entry, NodeEntry::Directory(nd)).interp().map));
    //                        assert(equal(self.interp().map.insert(base, pte), self.interp().map_frame(base, pte).get_Ok_0().map));
    //
    //                        assert(equal(self.map_frame(base, pte).get_Ok_0().interp(), self.interp().map_frame(base, pte).get_Ok_0()));
    //                    },
    //                    Err(e) => {
    //                        assert(d.map_frame(base, pte).is_Err());
    //                        assert(d.interp().map_frame(base, pte).is_Err());
    //                        assert(d.interp().accepted_mapping(base, pte));
    //                        assert(!d.interp().valid_mapping(base, pte));
    //                        let b = choose|b: nat| #![auto]
    //                                       d.interp().map.contains_key(b) && overlap(
    //                                           MemRegion { base: base, size: pte.frame.size },
    //                                           MemRegion { base: b, size: d.interp().map.index(b).frame.size }
    //                                           );
    //                        let bbase = d.interp().map.index(b).frame.base;
    //                        let bsize = d.interp().map.index(b).frame.size;
    //                        assert(d.interp().map.contains_pair(b, d.interp().map.index(b)));
    //                        assert(overlap(
    //                                MemRegion { base: base, size: pte.frame.size },
    //                                MemRegion { base: b, size: bsize }
    //                                ));
    //                        self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //                        assert(self.interp().map.contains_pair(b, d.interp().map.index(b)));
    //
    //                        assert(self.interp().accepted_mapping(base, pte));
    //                        assert(!self.interp().valid_mapping(base, pte));
    //
    //                        assert(self.map_frame(base, pte).is_Err());
    //                        assert(self.interp().map_frame(base, pte).is_Err());
    //                        assert(self.entries.index(entry as int) === NodeEntry::Directory(d));
    //                        assert(self.entries.index(entry as int) === NodeEntry::Directory(e));
    //                        let res = self.update(entry, NodeEntry::Directory(e)).entries;
    //                        assert(res.index(entry as int) === self.entries.index(entry as int));
    //                        assert(res =~= self.entries);
    //                    },
    //                }
    //                // d.lemma_map_frame_preserves_inv(base, pte);
    //            }
    //        },
    //        NodeEntry::Invalid => {
    //            if self.entry_size() == pte.frame.size {
    //                self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Page(pte), pte, true);
    //                assert(equal(result_map(self.map_frame(base, pte), |d: Directory| d.interp()), self.interp().map_frame(base, pte)));
    //            } else {
    //                assert(((self.layer + 1) as nat) < self.arch.layers.len());
    //                let new_dir = self.new_empty_dir(entry);
    //                self.lemma_new_empty_dir(entry, true);
    //                assert(new_dir.inv());
    //
    //                self.lemma_accepted_mapping_implies_directory_accepted_mapping(base, pte, new_dir, true);
    //                new_dir.lemma_accepted_mapping_implies_interp_accepted_mapping_auto();
    //                assert(new_dir.accepted_mapping(base, pte));
    //                indexing::lemma_index_from_base_and_addr(new_dir.base_vaddr, base, new_dir.entry_size(), new_dir.num_entries());
    //                new_dir.lemma_map_frame_empty_is_ok(base, pte);
    //                new_dir.lemma_map_frame_preserves_inv(base, pte);
    //
    //                let new_dir_mapped = new_dir.map_frame(base, pte).get_Ok_0();
    //                assert(new_dir.map_frame(base, pte).is_Ok());
    //                assert(new_dir_mapped.inv());
    //                new_dir.lemma_map_frame_refines_map_frame(base, pte);
    //                assert(new_dir.interp().map_frame(base, pte).is_Ok());
    //                assert(equal(new_dir_mapped.interp(), new_dir.interp().map_frame(base, pte).get_Ok_0()));
    //
    //                new_dir.lemma_empty_implies_interp_empty(true);
    //                assert(new_dir.interp().map =~= map![]);
    //                assert(new_dir.interp().map_frame(base, pte).get_Ok_0().map =~= map![base => pte]);
    //                assert(self.interp_of_entry(entry).map =~= map![]);
    //                assert(equal(self.interp_of_entry(entry).map, map![]));
    //                assert(equal(map![].insert(base, pte), new_dir_mapped.interp().map));
    //                assert(equal(self.interp_of_entry(entry).map.insert(base, pte), new_dir_mapped.interp().map));
    //                self.lemma_insert_interp_of_entry_implies_insert_interp(entry, base, NodeEntry::Directory(new_dir_mapped), pte, true);
    //
    //                assert(equal(result_map(self.map_frame(base, pte), |d: Directory| d.interp()), self.interp().map_frame(base, pte)));
    //            }
    //        },
    //    }
    //}

    //pub open spec(checked) fn accepted_unmap(self, base: nat) -> bool
    //    recommends self.well_formed()
    //{
    //    self.interp().accepted_unmap(base)
    //}

    //pub open spec fn unmap(self, base: nat) -> Result<Directory,Directory>
    //    recommends
    //        self.inv(),
    //        self.accepted_unmap(base),
    //    decreases self.arch.layers.len() - self.layer via Self::check_unmap
    //{
    //    if self.inv() && self.accepted_unmap(base) {
    //        let entry = self.index_for_vaddr(base);
    //        match self.entries.index(entry as int) {
    //            NodeEntry::Page(p) => {
    //                if aligned(base, self.entry_size()) {
    //                    // This implies:
    //                    // base == self.base_vaddr + entry * self.entry_size()
    //                    // (i.e. no remainder on division)
    //                    // (proved in lemma_index_for_vaddr_bounds)
    //                    Ok(self.update(entry, NodeEntry::Invalid))
    //                } else {
    //                    Err(self)
    //                }
    //            },
    //            NodeEntry::Directory(d) => {
    //                match d.unmap(base) {
    //                    Ok(new_d) =>
    //                        Ok(self.update(entry, if new_d.empty() {
    //                            NodeEntry::Invalid
    //                        } else {
    //                            NodeEntry::Directory(new_d)
    //                        })),
    //                    Err(new_d) => Err(self.update(entry, NodeEntry::Directory(new_d)))
    //                }
    //            },
    //            NodeEntry::Invalid => Err(self),
    //        }
    //    } else {
    //        arbitrary()
    //    }
    //}
    //
    //#[verifier(decreases_by)]
    //proof fn check_unmap(self, base: nat) {
    //    if self.inv() && self.accepted_unmap(base) {
    //        ambient_lemmas2();
    //        indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //    } else {
    //    }
    //}


    //pub proof fn lemma_unmap_preserves_inv(self, base: nat)
    //    requires
    //        self.inv(),
    //        self.accepted_unmap(base),
    //        self.unmap(base).is_Ok(),
    //    ensures
    //        self.unmap(base).get_Ok_0().inv(),
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //
    //    let res = self.unmap(base).get_Ok_0();
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //
    //    assert(entry < self.num_entries());
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => {
    //            if aligned(base, self.entry_size()) {
    //                assert(res.directories_obey_invariant(true));
    //            } else {
    //            }
    //        },
    //        NodeEntry::Directory(d) => {
    //            d.lemma_inv_implies_interp_inv();
    //            assert(d.accepted_unmap(base));
    //            match d.unmap(base) {
    //                Ok(new_d) => {
    //                    d.lemma_unmap_preserves_inv(base);
    //                    assert(res.directories_obey_invariant(true));
    //                }
    //                Err(_) => { }
    //            }
    //        },
    //        NodeEntry::Invalid => { },
    //    }
    //}

   // pub proof fn lemma_unmap_structure_assertions(self, base: nat, idx: nat)
   //     requires
   //         self.inv(),
   //         self.accepted_unmap(base),
   //         idx == self.index_for_vaddr(base),
   //     ensures
   //         match self.entries.index(idx as int) {
   //             NodeEntry::Page(p)      => {
   //                 if aligned(base, self.entry_size()) {
   //                     base == self.base_vaddr + idx * self.entry_size()
   //                 } else {
   //                     true
   //                 }
   //             },
   //             NodeEntry::Directory(d) => {
   //                 &&& d.inv()
   //                 &&& d.accepted_unmap(base)
   //             },
   //             NodeEntry::Invalid      => true,
   //         }
   //     decreases self.arch.layers.len() - self.layer
   // {
   //     broadcast use group_ambient;
   //     ambient_lemmas2();
   //     self.lemma_inv_implies_interp_inv();
   //
   //     indexing::lemma_entry_base_from_index(self.base_vaddr, idx, self.entry_size());
   //     indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
   //     assert(aligned(self.base_vaddr, self.entry_size())) by {
   //         extra::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
   //     };
   //
   //     match self.entries.index(self.index_for_vaddr(base) as int) {
   //         NodeEntry::Page(p) => {
   //             if aligned(base, self.entry_size()) {
   //             } else {
   //             }
   //         },
   //         NodeEntry::Directory(d) => {
   //             assert(d.inv());
   //             assert(d.accepted_unmap(base));
   //             d.lemma_unmap_refines_unmap(base);
   //         },
   //         NodeEntry::Invalid => { },
   //     }
   //}

    //pub proof fn lemma_unmap_refines_unmap(self, base: nat)
    //    requires
    //         self.inv(),
    //         self.accepted_unmap(base),
    //    ensures
    //        self.unmap(base).is_Err() ==> self.unmap(base).get_Err_0() === self,
    //        equal(result_map(self.unmap(base), |d: Directory| d.interp()), self.interp().unmap(base)),
    //    decreases self.arch.layers.len() - self.layer
    //{
    //    broadcast use group_ambient;
    //    ambient_lemmas2();
    //    self.lemma_inv_implies_interp_inv();
    //
    //    if let Ok(nself) = self.unmap(base) {
    //        self.lemma_unmap_preserves_inv(base);
    //        assert(nself.inv());
    //        nself.lemma_inv_implies_interp_inv();
    //        assert(nself.interp().inv());
    //    }
    //
    //    let nself_res = self.unmap(base);
    //    let nself     = self.unmap(base).get_Ok_0();
    //
    //    let i_nself_res = self.interp().unmap(base);
    //    let i_nself     = self.interp().unmap(base).get_Ok_0();
    //
    //    let entry = self.index_for_vaddr(base);
    //    indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //    indexing::lemma_entry_base_from_index_support(self.base_vaddr, entry, self.entry_size());
    //    indexing::lemma_index_from_base_and_addr(self.base_vaddr, base, self.entry_size(), self.num_entries());
    //    self.lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(entry, true);
    //
    //    match self.entries.index(entry as int) {
    //        NodeEntry::Page(p) => {
    //            if aligned(base, self.entry_size()) {
    //                assert(self.interp_of_entry(entry).map.remove(base) =~= map![]);
    //                assert(self.update(entry, NodeEntry::Invalid).inv());
    //                self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Invalid, true);
    //            } else {
    //                indexing::lemma_entry_base_from_index(self.base_vaddr, entry, self.entry_size());
    //                assert(!self.interp().map.contains_key(base));
    //                assert(i_nself_res.is_Err());
    //            }
    //        },
    //        NodeEntry::Directory(d) => {
    //            assert(d.inv());
    //            d.lemma_inv_implies_interp_inv();
    //            assert(d.accepted_unmap(base));
    //            d.lemma_unmap_refines_unmap(base);
    //            match d.unmap(base) {
    //                Ok(new_d) => {
    //                    d.lemma_unmap_preserves_inv(base);
    //                    assert(new_d.inv());
    //                    assert(d.unmap(base).is_Ok());
    //                    assert(d.interp().unmap(base).is_Ok());
    //                    assert(equal(new_d.interp(), d.interp().unmap(base).get_Ok_0()));
    //                    if new_d.empty() {
    //                        new_d.lemma_empty_implies_interp_empty(true);
    //                        d.interp().lemma_unmap_decrements_len(base);
    //                        assert(new_d.interp().map.dom().len() == 0);
    //                        assert(d.interp().map.dom().len() == 1);
    //                        assert(d.interp().map.contains_key(base));
    //                        assert(d.interp().map.dom() =~= set![base]);
    //                        assert(nself_res.is_Ok());
    //                        assert(equal(self.interp_of_entry(entry).map, d.interp().map));
    //                        assert(equal(d.interp().unmap(base).get_Ok_0().map, d.interp().map.remove(base)));
    //                        assert(self.interp_of_entry(entry).map.remove(base) =~= map![]);
    //                        assert(self.update(entry, NodeEntry::Invalid).inv());
    //                        self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Invalid, true);
    //                        assert(equal(nself.interp(), i_nself));
    //                    } else {
    //                        assert(self.update(entry, NodeEntry::Directory(new_d)).inv());
    //                        self.lemma_remove_from_interp_of_entry_implies_remove_from_interp(entry, base, NodeEntry::Directory(new_d), true);
    //                    }
    //                }
    //                Err(e) => {
    //                    assert(self.entries.index(entry as int) === NodeEntry::Directory(d));
    //                    assert(self.entries.index(entry as int) === NodeEntry::Directory(e));
    //                    let res = self.update(entry, NodeEntry::Directory(e)).entries;
    //                    assert(res.index(entry as int) === self.entries.index(entry as int));
    //                    assert(res =~= self.entries);
    //                }
    //            }
    //        },
    //        NodeEntry::Invalid => { },
    //    }
    //}

    proof fn lemma_entries_interp_equal_implies_interp_aux_equal(self, other: Directory, i: nat)
        requires
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            forall|j: nat| i <= j && j < self.entries.len()
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j)) == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            self.interp_aux(i) === other.interp_aux(i),
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        if i >= self.entries.len() {
        } else {
            let rem1 = self.interp_aux(i + 1);
            let rem2 = other.interp_aux(i + 1);
            let entry_i1 = self.interp_of_entry(i);
            let entry_i2 = other.interp_of_entry(i);
            self.lemma_entries_interp_equal_implies_interp_aux_equal(other, i + 1);
            assert(rem1.union_prefer_right(entry_i1) =~= rem2.union_prefer_right(entry_i2));
        }
    }

    pub proof fn lemma_entries_interp_equal_implies_interp_equal(self, other: Directory)
        requires
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            forall|j: nat| j < self.entries.len()
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j))
                            == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            self.interp() === other.interp(),
    {
        self.lemma_entries_interp_equal_implies_interp_aux_equal(other, 0);
    }

    pub proof fn lemma_entries_interp_insert_implies_interp_insert(self, other: Directory, idx: nat, vaddr: nat, pte: PTE)
        requires
            idx < self.entries.len(),
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            other.entries[idx as int].interp(self.entry_base(idx))
                == self.entries[idx as int].interp(self.entry_base(idx)).insert(vaddr, pte),
            forall|j: nat| j < self.entries.len() && j != idx
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j))
                            == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            other.interp() === self.interp().insert(vaddr, pte),
    {
        self.lemma_entries_interp_insert_implies_interp_aux_insert(other, idx, vaddr, pte, 0);
    }

    proof fn lemma_entries_interp_insert_implies_interp_aux_insert(self, other: Directory, idx: nat, vaddr: nat, pte: PTE, i: nat)
        requires
            idx < self.entries.len(),
            self.inv(),
            other.inv(),
            self.arch == other.arch,
            self.layer == other.layer,
            self.base_vaddr == other.base_vaddr,
            other.entries[idx as int].interp(self.entry_base(idx))
                == self.entries[idx as int].interp(self.entry_base(idx)).insert(vaddr, pte),
            forall|j: nat| i <= j < self.entries.len() && j != idx
                ==> (#[trigger] self.entries[j as int]).interp(self.entry_base(j))
                            == other.entries[j as int].interp(self.entry_base(j)),
        ensures
            if idx < i {
                other.interp_aux(i) === self.interp_aux(i)
            } else {
                other.interp_aux(i) === self.interp_aux(i).insert(vaddr, pte)
            }
        decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    {
        if i >= self.entries.len() {
        } else {
            let rem1 = self.interp_aux(i + 1);
            let rem2 = other.interp_aux(i + 1);
            let entry_i1 = self.interp_of_entry(i);
            let entry_i2 = other.interp_of_entry(i);
            if idx < i {
                self.lemma_entries_interp_insert_implies_interp_aux_insert(other, idx, vaddr, pte, i + 1);
                assert(rem1.union_prefer_right(entry_i1) =~= rem2.union_prefer_right(entry_i2));
            } else if idx == i {
                self.lemma_entries_interp_insert_implies_interp_aux_insert(other, idx, vaddr, pte, i + 1);
                assert(rem2.union_prefer_right(entry_i2) =~= rem1.union_prefer_right(entry_i1).insert(vaddr, pte));
            } else {
                self.lemma_entries_interp_insert_implies_interp_aux_insert(other, idx, vaddr, pte, i + 1);
                other.lemma_interp_of_entry_disjoint_mappings(i, idx);
                assert(rem2.union_prefer_right(entry_i2) =~= rem1.union_prefer_right(entry_i1).insert(vaddr, pte));
            }
        }
    }

    //proof fn lemma_entries_equal_implies_interp_aux_equal(self, other: Directory, i: nat)
    //    requires
    //        self.inv(),
    //        other.inv(),
    //        equal(self.arch, other.arch),
    //        equal(self.layer, other.layer),
    //        equal(self.base_vaddr, other.base_vaddr),
    //        equal(self.num_entries(), other.num_entries()),
    //        forall|j: int| i <= j && j < self.entries.len() ==> equal(self.entries.index(j), other.entries.index(j)),
    //    ensures
    //        self.interp_aux(i) === other.interp_aux(i),
    //    decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    //{
    //    if i >= self.entries.len() {
    //    } else {
    //        let rem1 = self.interp_aux(i + 1);
    //        let rem2 = other.interp_aux(i + 1);
    //        let entry_i1 = self.interp_of_entry(i);
    //        let entry_i2 = other.interp_of_entry(i);
    //        self.lemma_entries_equal_implies_interp_aux_equal(other, i + 1);
    //        assert(rem1.union_prefer_right(entry_i1) =~= rem2.union_prefer_right(entry_i2));
    //    }
    //}

    //proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(self, j: nat, i: nat, vaddr: nat, n: NodeEntry)
    //    requires
    //        self.inv(),
    //        i <= j,
    //        j < self.num_entries(),
    //        self.interp_of_entry(j).map.contains_key(vaddr),
    //        self.update(j, n).inv(),
    //        equal(
    //            self.interp_of_entry(j).map.remove(vaddr),
    //            match n {
    //                NodeEntry::Page(p)      => map![self.entry_base(j) => p],
    //                NodeEntry::Directory(d) => d.interp_aux(0).map,
    //                NodeEntry::Invalid      => map![],
    //            }),
    //    ensures
    //        equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map),
    //    decreases self.arch.layers.len() - self.layer, self.num_entries() - i
    //{
    //
    //    assert(j < self.entries.len());
    //    broadcast use group_ambient;
    //    self.lemma_inv_implies_interp_aux_inv(i);
    //    self.lemma_inv_implies_interp_aux_inv(i + 1);
    //    self.lemma_inv_implies_interp_of_entry_inv(i);
    //    self.lemma_inv_implies_interp_of_entry_inv(j);
    //
    //    self.lemma_interp_of_entry();
    //    self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i, j);
    //
    //    let nself = self.update(j, n);
    //
    //    if i >= self.entries.len() {
    //    } else {
    //        if i == j {
    //            assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));
    //
    //            assert(equal(self.interp_of_entry(i).map.remove(vaddr), nself.interp_of_entry(i).map));
    //            self.lemma_entries_equal_implies_interp_aux_equal(nself, i+1);
    //            assert(equal(self.interp_aux(i + 1).map, nself.interp_aux(i + 1).map));
    //
    //            assert(equal(self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map).remove(vaddr),
    //                         nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));
    //
    //            assert(equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map));
    //        } else {
    //            assert(i < j);
    //            assert(self.directories_obey_invariant());
    //
    //            self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, i + 1, vaddr, n);
    //            self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(i + 1, j);
    //
    //            assert(self.interp_aux(j).map.contains_key(vaddr));
    //            assert(self.interp_aux(i + 1).map.contains_key(vaddr));
    //
    //            assert(equal(self.interp_aux(i + 1).map.remove(vaddr), self.update(j, n).interp_aux(i + 1).map));
    //
    //            assert(equal(self.interp_aux(i).map, self.interp_aux(i + 1).map.union_prefer_right(self.interp_of_entry(i).map)));
    //
    //
    //
    //            assert(nself.inv());
    //            assert(equal(nself.interp_aux(i).map, nself.interp_aux(i + 1).map.union_prefer_right(nself.interp_of_entry(i).map)));
    //
    //            assert(equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map));
    //        }
    //    }
    //}

    //proof fn lemma_remove_from_interp_of_entry_implies_remove_from_interp(self, j: nat, vaddr: nat, n: NodeEntry)
    //    requires
    //        self.inv(),
    //        j < self.num_entries(),
    //        self.interp_of_entry(j).map.contains_key(vaddr),
    //        self.update(j, n).inv(),
    //        equal(
    //            self.interp_of_entry(j).map.remove(vaddr),
    //            match n {
    //                NodeEntry::Page(p)      => map![self.entry_base(j) => p],
    //                NodeEntry::Directory(d) => d.interp_aux(0).map,
    //                NodeEntry::Invalid      => map![],
    //            })
    //    ensures
    //        equal(self.interp().map.remove(vaddr), self.update(j, n).interp().map),
    //{
    //    self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, 0, vaddr, n);
    //}
}

}
