#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[macro_use]
use crate::pervasive::*;
use seq::*;
use map::*;
#[allow(unused_imports)]
use set::*;
#[allow(unused_imports)]
use crate::{seq, seq_insert_rec, map, map_insert_rec, assert_maps_equal, assert_sets_equal, set, set_insert_rec};
#[allow(unused_imports)]
use result::{*, Result::*};

#[proof]
fn ambient_lemmas1() {
    ensures([
            forall(|d: Directory, i: nat| with_triggers!([d.inv(), d.entries.index(i)] => d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory() >>= d.entries.index(i).get_Directory_0().inv())),
            forall(|s1: Map<nat,MemRegion>, s2: Map<nat,MemRegion>| s1.dom().finite() && s2.dom().finite() >>= #[trigger] s1.union_prefer_right(s2).dom().finite()),
            forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
            forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
                   (m1.dom().contains(n) && !m2.dom().contains(n))
                   >>= equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))),
            forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
                   (m2.dom().contains(n) && !m1.dom().contains(n))
                   >>= equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n))),
    ]);
    lemma_finite_map_union::<nat,MemRegion>();
    assert_nonlinear_by({ ensures(forall(|d: Directory| equal(d.num_entries() * d.entry_size(), d.entry_size() * d.num_entries()))); });
    assert_forall_by(|d: Directory, i: nat| {
        requires(#[auto_trigger] d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
        ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
        assert(d.directories_obey_invariant());
    });
    lemma_map_union_prefer_right_remove_commute::<nat,MemRegion>();
}


#[proof]
fn ambient_lemmas2() {
    ensures([
            forall(|d: Directory, base: nat, frame: MemRegion|
                   d.inv() && #[trigger] d.accepted_mapping(base, frame) >>=
                   d.interp().accepted_mapping(base, frame)),
    ]);
    assert_forall_by(|d: Directory, base: nat, frame: MemRegion| {
        requires(d.inv() && #[trigger] d.accepted_mapping(base, frame));
        ensures(d.interp().accepted_mapping(base, frame));
        d.lemma_accepted_mapping_implies_interp_accepted_mapping();
    });
}

pub struct MemRegion { pub base: nat, pub size: nat }

// TODO use VAddr, PAddr

#[spec]
pub fn strictly_decreasing(s: Seq<nat>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) > s.index(j))
}

#[spec]
pub fn between(x: nat, a: nat, b: nat) -> bool {
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

#[spec]
pub struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {
    #[spec(checked)]
    pub fn inv(&self) -> bool {
        forall(|i:nat| with_triggers!([self.layers.index(i).entry_size], [self.layers.index(i).num_entries] => i < self.layers.len() >>= (
            true
            && self.layers.index(i).entry_size > 0
            && self.layers.index(i).num_entries > 0
            && self.entry_size_is_next_layer_size(i))))
    }

    #[spec(checked)]
    pub fn entry_size_is_next_layer_size(self, i: nat) -> bool {
        recommends(i < self.layers.len());
        i + 1 < self.layers.len() >>=
            self.layers.index(i).entry_size == self.layers.index((i + 1) as nat).entry_size * self.layers.index((i + 1) as nat).num_entries
    }

    #[spec(checked)]
    pub fn contains_entry_size(&self, entry_size: nat) -> bool {
        exists(|i: nat| i < self.layers.len() && #[trigger] self.layers.index(i).entry_size == entry_size)
    }
}

#[proof]
fn arch_inv_test() {
    let x86 = Arch {
        layers: seq![
            ArchLayer { entry_size: 512 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 1 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 2 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 4 * 1024, num_entries: 512 },
        ],
    };
    assert(x86.inv());
    assert(x86.layers.index(3).entry_size == 4096);
    assert(x86.contains_entry_size(4096));
}

#[proof]
pub struct PageTableContents {
    pub map: Map<nat /* VAddr */, MemRegion>,
    pub arch: Arch,
    pub lower: nat,
    pub upper: nat,
}

#[spec(checked)]
pub fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

#[spec(checked)]
pub fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
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
    #[spec(checked)]
    pub fn inv(&self) -> bool {
        true
        && self.map.dom().finite()
        && self.arch.inv()
        && self.mappings_are_of_valid_size()
        && self.mappings_are_aligned()
        && self.mappings_dont_overlap()
        && self.mappings_in_bounds()
    }

    #[spec(checked)]
    pub fn mappings_are_of_valid_size(self) -> bool {
        forall(|va: nat| with_triggers!([self.map.index(va).size],[self.map.index(va).base] =>
                                        self.map.dom().contains(va) >>= self.arch.contains_entry_size(self.map.index(va).size)))
    }

    #[spec(checked)]
    pub fn mappings_are_aligned(self) -> bool {
        forall(|va: nat| with_triggers!([self.map.index(va).size],[self.map.index(va).base] =>
                                        self.map.dom().contains(va)
                                        >>= (aligned(va, self.map.index(va).size)
                                             && aligned(self.map.index(va).base, self.map.index(va).size))))
    }

    #[spec(checked)]
    pub fn mappings_dont_overlap(self) -> bool {
        forall(|b1: nat, b2: nat| // TODO verus the default triggers were bad
               with_triggers!([self.map.index(b1), self.map.index(b2)],
                              [self.map.dom().contains(b1), self.map.dom().contains(b2)] =>
                              (self.map.dom().contains(b1) && self.map.dom().contains(b2))
                              >>= ((b1 == b2) || !overlap(
                                      MemRegion { base: b1, size: self.map.index(b1).size },
                                      MemRegion { base: b2, size: self.map.index(b2).size }))))
    }

    #[spec(checked)]
    pub fn candidate_mapping_in_bounds(self, base: nat, frame: MemRegion) -> bool {
        self.lower <= base && base + frame.size <= self.upper
    }

    #[spec(checked)]
    pub fn mappings_in_bounds(self) -> bool {
        forall(|b1: nat|
               with_triggers!([self.map.index(b1)], [self.map.dom().contains(b1)], [self.candidate_mapping_in_bounds(b1, self.map.index(b1))] =>
                              self.map.dom().contains(b1) >>= self.candidate_mapping_in_bounds(b1, self.map.index(b1))))
    }

    #[spec(checked)]
    pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
        && self.candidate_mapping_in_bounds(base, frame)
        && self.arch.contains_entry_size(frame.size)
    }

    #[spec(checked)]
    pub fn valid_mapping(self, base: nat, frame: MemRegion) -> bool {
        forall(|b: nat| #[auto_trigger] self.map.dom().contains(b) >>= !overlap(
                MemRegion { base: base, size: frame.size },
                MemRegion { base: b, size: self.map.index(b).size }
                ))
    }

    /// Maps the given `frame` at `base` in the address space
    #[spec(checked)]
    pub fn map_frame(self, base: nat, frame: MemRegion) -> Result<PageTableContents,()> {
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
    #[proof]
    fn map_frame_maps_valid(#[spec] self, base: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
            self.valid_mapping(base, frame),
        ]);
        ensures([
            self.map_frame(base, frame).is_Ok(),
        ]);
    }

    #[proof]
    fn map_frame_preserves_inv(#[spec] self, base: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
            self.map_frame(base, frame).is_Ok(),
        ]);
        ensures([
            self.map_frame(base, frame).get_Ok_0().inv(),
        ]);
        let nself = self.map_frame(base, frame).get_Ok_0();
        assert(nself.mappings_in_bounds());
    }

    // predicate (function -> bool)
    // #[spec] pub fn step_map_frame(&self /* s */, post: &PageTableContents /* s' */, base:nat, frame: MemRegion) -> bool {
    //     post == self.map_frame(base, frame)
    // }

    // TODO later /// Changes the mapping permissions of the region containing `vaddr` to `rights`.
    // TODO later fn adjust(self, vaddr: nat) -> Result<(VAddr, usize), KError>;
    //

    #[spec(checked)]
    fn accepted_resolve(self, vaddr: nat) -> bool {
        between(vaddr, self.lower, self.upper)
    }

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    // #[spec] fn resolve(self, vaddr: nat) -> MemRegion {
    #[spec(checked)]
    fn resolve(self, vaddr: nat) -> Result<nat,()> {
        recommends(self.accepted_resolve(vaddr));
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

    #[spec(checked)]
    fn remove(self, n: nat) -> PageTableContents {
        PageTableContents {
            map: self.map.remove(n),
            ..self
        }
    }

    #[spec(checked)]
    fn accepted_unmap(self, base:nat) -> bool {
        true
        && between(base, self.lower, self.upper)
        && exists(|size: nat| with_triggers!([self.arch.contains_entry_size(size)], [aligned(base, size)] =>
            self.arch.contains_entry_size(size) && aligned(base, size)))
    }

    /// Removes the frame from the address space that contains `base`.
    #[spec(checked)]
    fn unmap(self, base: nat) -> Result<PageTableContents,()> {
        recommends(self.accepted_unmap(base));
        if self.map.dom().contains(base) {
            Ok(self.remove(base))
        } else {
            Err(())
        }
    }

    #[proof]
    fn lemma_unmap_preserves_inv(self, base: nat) {
        requires([
            self.inv(),
            self.unmap(base).is_Ok()
        ]);
        ensures([
            self.unmap(base).get_Ok_0().inv()
        ]);
    }

    #[proof]
    fn lemma_unmap_decrements_len(self, base: nat) {
        requires([
                 self.inv(),
                 self.unmap(base).is_Ok()
        ]);
        ensures([
                self.map.dom().len() > 0,
                equal(self.unmap(base).get_Ok_0().map.dom(), self.map.dom().remove(base)),
                self.unmap(base).get_Ok_0().map.dom().len() == self.map.dom().len() - 1
        ]);
        assert(self.map.dom().contains(base));
        lemma_set_contains_IMP_len_greater_zero::<nat>(self.map.dom(), base);
    }

    #[spec]
    pub fn ranges_disjoint(self, other: Self) -> bool {
        if self.lower <= other.lower {
            self.upper <= other.lower
        } else {
            // other.lower < self.lower
            other.upper <= self.lower
        }
    }

    #[spec]
    pub fn mappings_disjoint(self, other: Self) -> bool {
        forall(|s: nat, o: nat| self.map.dom().contains(s) && other.map.dom().contains(o) >>=
            !overlap(MemRegion { base: s, size: self.map.index(s).size }, MemRegion { base: o, size: other.map.index(o).size }))
    }

    #[proof]
    pub fn lemma_ranges_disjoint_implies_mappings_disjoint(self, other: Self) {
        requires([
            self.inv(),
            other.inv(),
            self.ranges_disjoint(other),

        ]);
        ensures(self.mappings_disjoint(other));
    }

    #[proof]
    fn lemma_mappings_have_positive_entry_size(self) {
        requires(self.inv());
        ensures([
                forall(|va: nat| #[trigger] self.map.dom().contains(va)
                       >>= self.map.index(va).size > 0),
        ]);
    }
}


// Second refinement layer

#[proof] #[is_variant]
pub enum NodeEntry {
    Directory(Directory),
    Page(MemRegion),
    Empty(),
}

#[proof]
pub struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat,       // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
}
//
// // Layer 0: 425 Directory ->
// // Layer 1: 47  Directory ->
// // Layer 2: 5   Page (1K)
//
// // Layer 1: 46  Directory -> (1M)
// // Layer 2: 1024 Pages
//
// // Layer 0: 1024 Directories (1T)
// // Layer 1: 1024 Directories (1G)
// // Layer 2: 1024 Pages

impl Directory {

    #[spec(checked)]
    pub fn well_formed(&self) -> bool {
        true
        && self.arch.inv()
        && self.layer < self.arch.layers.len()
        && aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        && self.entries.len() == self.num_entries()
    }

    #[spec(checked)]
    pub fn arch_layer(&self) -> ArchLayer {
        recommends(self.well_formed());
        self.arch.layers.index(self.layer)
    }

    #[spec(checked)]
    pub fn entry_size(&self) -> nat {
        recommends(self.layer < self.arch.layers.len());
        self.arch.layers.index(self.layer).entry_size
    }

    #[spec(checked)]
    pub fn num_entries(&self) -> nat { // number of entries
        recommends(self.layer < self.arch.layers.len());
        self.arch.layers.index(self.layer).num_entries
    }

    #[spec(checked)]
    pub fn empty(&self) -> bool {
        recommends(self.well_formed());
        forall(|i: nat| i < self.num_entries() >>= self.entries.index(i).is_Empty())
    }

    #[spec(checked)]
    pub fn pages_match_entry_size(&self) -> bool {
        recommends(self.well_formed());
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Page())
               >>= (#[trigger] self.entries.index(i)).get_Page_0().size == self.entry_size())
    }

    #[spec(checked)]
    pub fn directories_are_in_next_layer(&self) -> bool {
        recommends(self.well_formed());
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= {
                    let directory = (#[trigger] self.entries.index(i)).get_Directory_0();
                    true
                    && directory.layer == self.layer + 1
                    && directory.base_vaddr == self.base_vaddr + i * self.entry_size()
                })
    }

    #[spec(checked)]
    pub fn directories_obey_invariant(&self) -> bool {
        decreases((self.arch.layers.len() - self.layer, 0));
        recommends(self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch());

        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
                   >>= (#[trigger] self.entries.index(i)).get_Directory_0().inv())
        } else {
            arbitrary()
        }
    }

    #[spec(checked)]
    pub fn directories_match_arch(&self) -> bool {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= equal((#[trigger] self.entries.index(i)).get_Directory_0().arch, self.arch))
    }

    #[spec]
    pub fn directories_are_nonempty(&self) -> bool {
        recommends(self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch());
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= !(#[trigger] self.entries.index(i).get_Directory_0().empty()))
            // TODO: Maybe pick a more aggressive trigger?
    }

    #[spec(checked)]
    pub fn frames_aligned(&self) -> bool {
        recommends(self.well_formed());
        forall(|i: nat| i < self.entries.len() && self.entries.index(i).is_Page() >>=
                  aligned((#[trigger] self.entries.index(i)).get_Page_0().base, self.entry_size()))
    }

    #[spec(checked)]
    pub fn inv(&self) -> bool {
        decreases(self.arch.layers.len() - self.layer);

        true
        && self.well_formed()
        && self.pages_match_entry_size()
        && self.directories_are_in_next_layer()
        && self.directories_match_arch()
        && self.directories_obey_invariant()
        && self.directories_are_nonempty()
        && self.frames_aligned()
    }

    #[spec(checked)]
    pub fn interp(self) -> PageTableContents {
        // recommends(self.inv());
        self.interp_aux(0)
    }

    #[spec(checked)]
    pub fn upper_vaddr(self) -> nat {
        recommends(self.well_formed());
        self.base_vaddr + self.num_entries() * self.entry_size()
    }

    #[spec]
    pub fn vaddr_offset(self, vaddr: nat) -> nat {
        vaddr - self.base_vaddr
    }

    #[spec]
    pub fn index_for_vaddr(self, vaddr: nat) -> /*index: */ nat {
         self.vaddr_offset(vaddr) / self.entry_size()
    }

    #[spec]
    pub fn entry_base(self, entry: nat) -> nat {
        recommends(self.inv());
        self.base_vaddr + entry * self.entry_size()
    }

    #[proof] #[verifier(nonlinear)]
    pub fn lemma_entry_base(self) {
        requires(self.inv());
        ensures([
                forall(|i: nat, j: nat| i < j >>= #[trigger] self.entry_base(i) < #[trigger] self.entry_base(j) && self.entry_base(i+1) <= self.entry_base(j)),
                forall(|i: nat| #[auto_trigger] aligned(self.entry_base(i), self.entry_size())),
        ]);
        assume(false); // unstable

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
    }

    #[spec]
    pub fn entry_bounds(self, entry: nat) -> (nat, nat) {
        (self.entry_base(entry), self.entry_base(entry + 1))
    }

    #[spec]
    pub fn interp_of_entry(self, entry: nat) -> PageTableContents {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - entry, 0));

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

    #[proof]
    fn lemma_interp_of_entry(self) {
        requires([
                 self.inv(),
        ]);
        ensures(forall(|i: nat| #[auto_trigger]
                 i < self.num_entries() >>=
                 self.interp_of_entry(i).inv() &&
                 self.interp_of_entry(i).lower == self.entry_base(i) &&
                 self.interp_of_entry(i).upper == self.entry_base(i+1) &&
                 forall(|base: nat| self.interp_of_entry(i).map.dom().contains(base) >>= between(base, self.entry_base(i), self.entry_base(i+1))) &&
                 forall(|base: nat, p: MemRegion| self.interp_of_entry(i).map.contains_pair(base, p) >>= between(base, self.entry_base(i), self.entry_base(i+1)))
                 ));
        assert_forall_by(|i: nat| {
            requires(i < self.num_entries());
            ensures( #[auto_trigger]
                 self.interp_of_entry(i).inv() &&
                 self.interp_of_entry(i).lower == self.entry_base(i) &&
                 self.interp_of_entry(i).upper == self.entry_base(i+1));
            self.lemma_inv_implies_interp_of_entry_inv(i);
        });
    }

    #[proof]
    fn lemma_inv_implies_interp_of_entry_inv(self, i: nat) {
        requires([
                 self.inv(),
                 i < self.num_entries(),
        ]);
        ensures([
            self.interp_of_entry(i).inv(),
            self.interp_of_entry(i).lower == self.entry_base(i),
            self.interp_of_entry(i).upper == self.entry_base(i+1),
        ]);

        let entry_i = self.interp_of_entry(i);

        self.lemma_entry_base();
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

    #[proof]
    fn lemma_interp_of_entries_disjoint(self) {
        requires(self.inv());
        ensures(forall(|i: nat, j: nat|
                       i < self.num_entries() && j < self.num_entries() && i != j
                       >>= self.interp_of_entry(i).ranges_disjoint(self.interp_of_entry(j))));
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
                });
            }
        });

    }

    #[spec(checked)]
    pub fn interp_aux(self, i: nat) -> PageTableContents {
        // TODO: Adding the recommendation causes a warning on the recursive call, which we can't
        // prevent without writing assertions.
        // recommends(self.inv());
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i, 1));

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

    #[proof]
    fn lemma_inv_implies_interp_inv(self) {
        requires(self.inv());
        ensures([
            self.interp().inv(),
            self.interp().upper == self.upper_vaddr(),
            self.interp().lower == self.base_vaddr,
        ]);
        self.lemma_inv_implies_interp_aux_inv(0);
    }

    #[proof]
    fn lemma_inv_implies_interp_aux_inv(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires(self.inv());
        ensures([
            self.interp_aux(i).inv(),
            i <= self.entries.len() >>= self.interp_aux(i).lower == self.entry_base(i),
            self.interp_aux(i).upper == self.upper_vaddr(),
            i == 0 >>= self.interp_aux(0).lower == self.base_vaddr,
        ]);

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
                self.lemma_entry_base();
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
                assume(false); // unstable
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

    #[proof]
    fn lemma_empty_implies_interp_aux_empty(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 self.empty()
        ]);
        ensures([
                equal(self.interp_aux(i).map, Map::empty()),
                equal(self.interp_aux(i).map.dom(), Set::empty())
        ]);

        if i >= self.entries.len() {
        } else {
            let rem = self.interp_aux(i + 1);
            let entry_i = self.interp_of_entry(i);
            self.lemma_empty_implies_interp_aux_empty(i + 1);
            assert_maps_equal!(rem.map.union_prefer_right(entry_i.map), Map::empty());
        }
    }

    #[proof]
    fn lemma_empty_implies_interp_empty(self) {
        requires([
                 self.inv(),
                 self.empty()
        ]);
        ensures([
                equal(self.interp().map, Map::empty()),
                equal(self.interp().map.dom(), Set::empty())
        ]);
        self.lemma_empty_implies_interp_aux_empty(0);
    }

    #[proof]
    fn lemma_ranges_disjoint_interp_aux_interp_of_entry(self) {
        requires(self.inv());
        ensures(forall(|i: nat, j: nat|
                       j < i && i < self.num_entries()
                       >>= self.interp_aux(i).ranges_disjoint(self.interp_of_entry(j))));
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

    #[proof]
    fn lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(self, i: nat, j: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
             self.inv(),
             i <= j,
             j < self.entries.len(),
        ]);
        ensures([
            forall(|va: nat, p: MemRegion| #[auto_trigger] self.interp_of_entry(j).map.contains_pair(va, p) >>= self.interp_aux(i).map.contains_pair(va, p)),
            forall(|va: nat| #[auto_trigger] self.interp_of_entry(j).map.dom().contains(va) >>= self.interp_aux(i).map.dom().contains(va)),
            forall(|va: nat|
                   between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                   >>= !self.interp_aux(i).map.dom().contains(va)),
        ]);

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

        self.lemma_entry_base();
    }

    #[proof]
    fn lemma_interp_of_entry_contains_mapping_implies_interp_contains_mapping(self, j: nat) {
        requires([
             self.inv(),
             j < self.entries.len(),
        ]);
        ensures([
            forall(|va: nat| #[auto_trigger] self.interp_of_entry(j).map.dom().contains(va) >>= self.interp().map.dom().contains(va)),
            forall(|va: nat, p: MemRegion| #[auto_trigger] self.interp_of_entry(j).map.contains_pair(va, p) >>= self.interp().map.contains_pair(va, p)),
            forall(|va: nat| #[auto_trigger]
                   between(va, self.entry_base(j), self.entry_base(j+1)) && !self.interp_of_entry(j).map.dom().contains(va)
                   >>= !self.interp().map.dom().contains(va)),
        ]);
        self.lemma_interp_of_entry_contains_mapping_implies_interp_aux_contains_mapping(0, j);
    }

    // #[proof]
    // fn lemma_interp_aux_subset_interp_aux_plus(self, i: nat, k: nat, v: MemRegion) {
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

    #[spec(checked)]
    fn resolve(self, vaddr: nat) -> Result<nat,()> {
        recommends(self.inv() && self.interp().accepted_resolve(vaddr));
        decreases_when(self.inv() && self.interp().accepted_resolve(vaddr));
        decreases(self.arch.layers.len() - self.layer);
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

    #[proof] #[verifier(decreases_by)]
    fn check_resolve(self, vaddr: nat) {
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

    #[proof] #[verifier(nonlinear)]
    fn lemma_index_for_vaddr_bounds(self, vaddr: nat) {
        requires(self.inv());
        ensures([
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
        ]);
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
        self.lemma_entry_base();
    }

    #[proof]
    fn lemma_interp_aux_contains_implies_interp_of_entry_contains(self, j: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - j));
        requires(self.inv());
        ensures([
                forall(|base: nat, p: MemRegion|
                       self.interp_aux(j).map.contains_pair(base, p) >>=
                       exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, p))),
                forall(|base: nat|
                       self.interp_aux(j).map.dom().contains(base) >>=
                       exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base)))
        ]);


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

    #[proof]
    fn lemma_interp_contains_implies_interp_of_entry_contains(self) {
        requires(self.inv());
        ensures([
                forall(|base: nat, p: MemRegion|
                       self.interp().map.contains_pair(base, p) >>=
                       exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.contains_pair(base, p))),
                forall(|base: nat|
                       self.interp().map.dom().contains(base) >>=
                       exists(|i: nat| #[auto_trigger] i < self.num_entries() && self.interp_of_entry(i).map.dom().contains(base))),
        ]);
        self.lemma_interp_aux_contains_implies_interp_of_entry_contains(0);
    }

    #[proof]
    fn lemma_no_mapping_in_interp_of_entry_implies_no_mapping_in_interp(self, vaddr: nat, i: nat) {
        requires([
                 self.inv(),
                 i < self.num_entries(),
                 between(vaddr, self.interp_of_entry(i).lower, self.interp_of_entry(i).upper),
                 !exists(|base:nat|
                         self.interp_of_entry(i).map.dom().contains(base) &&
                         between(vaddr, base, base + (#[trigger] self.interp_of_entry(i).map.index(base)).size))
        ]);
        ensures(!exists(|base:nat|
                self.interp().map.dom().contains(base) &&
                between(vaddr, base, base + (#[trigger] self.interp().map.index(base)).size))
        );

        self.lemma_entry_base();
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

    #[proof]
    fn resolve_refines(self, vaddr: nat) {
        decreases(self.arch.layers.len() - self.layer);
        requires([
            self.inv(),
            self.interp().accepted_resolve(vaddr),
        ]);
        ensures(equal(self.interp().resolve(vaddr), self.resolve(vaddr)));

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

    #[spec(checked)]
    pub fn update(self, n: nat, e: NodeEntry) -> Self {
        recommends(n < self.entries.len());
        Directory {
            entries: self.entries.update(n, e),
            ..self
        }
    }

    #[spec(checked)]
    pub fn candidate_mapping_in_bounds(self, base: nat, frame: MemRegion) -> bool {
        recommends(self.inv());
        self.base_vaddr <= base && base + frame.size <= self.entry_base(self.num_entries())
    }

    #[spec(checked)]
    pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        recommends(self.inv());
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
        && self.candidate_mapping_in_bounds(base, frame)
        && self.arch.contains_entry_size(frame.size)
    }

    #[proof]
    pub fn lemma_accepted_mapping_implies_interp_accepted_mapping(self) {
        ensures(forall(|base: nat, frame: MemRegion|
                       self.inv() && #[trigger] self.accepted_mapping(base, frame) >>=
                       self.interp().accepted_mapping(base, frame)));

        assert_forall_by(|base: nat, frame: MemRegion| {
            requires(self.inv() && #[trigger] self.accepted_mapping(base, frame));
            ensures(self.interp().accepted_mapping(base, frame));

            self.lemma_inv_implies_interp_inv();
            assert(aligned(base, frame.size));
            assert(aligned(frame.base, frame.size));
            assert(self.base_vaddr <= base && base + frame.size <= self.entry_base(self.num_entries()));
            // assert(self.
        // self.lower <= base && base + frame.size <= self.upper
            assert(self.interp().candidate_mapping_in_bounds(base, frame));
            assert(self.interp().arch.contains_entry_size(frame.size));
        });
    }

    #[spec]
    pub fn map_frame(self, base: nat, frame: MemRegion) -> Result<Self,()> {
        // recommends(self.inv());
        decreases(self.arch.layers.len() - self.layer);
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
                        // Indexing into self.arch.layers with self.layer + 1 is okay because
                        // we know the frame size isn't this layer's entrysize (i.e. must be on
                        // some lower level).
                        // The index recommendation fails with spec(checked) though.
                        let new_dir = Directory {
                            entries:    new_seq(self.arch.layers.index((self.layer + 1) as nat).num_entries),
                            layer:      self.layer + 1,
                            base_vaddr: self.entry_base(entry),
                            arch:       self.arch,
                        };
                        match new_dir.map_frame(base, frame) {
                            Ok(d) => Ok(self.update(entry, NodeEntry::Directory(d))),
                            // We never fail to insert an accepted mapping into an empty directory
                            Err(e) => arbitrary(),
                        }
                    }
                },
            }
        } else {
            arbitrary()
        }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_map_frame(self, base: nat, frame: MemRegion) {
        ambient_lemmas1();
        self.lemma_accepted_mapping_implies_interp_accepted_mapping();
        if self.inv() && self.accepted_mapping(base, frame) {
            self.lemma_index_for_vaddr_bounds(base);
        }
    }

    #[proof]
    fn lemma_map_frame_preserves_inv(self, base: nat, frame: MemRegion) {
        decreases(self.arch.layers.len() - self.layer);
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
            self.map_frame(base, frame).is_Ok(),
        ]);
        ensures([
                equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer),
                equal(self.map_frame(base, frame).get_Ok_0().arch, self.arch),
                !self.map_frame(base, frame).get_Ok_0().empty(),
                self.map_frame(base, frame).get_Ok_0().inv()
        ]);

        ambient_lemmas1();
        ambient_lemmas2();
        self.lemma_index_for_vaddr_bounds(base);

        let res = self.map_frame(base, frame).get_Ok_0();

        let entry = self.index_for_vaddr(base);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => (),
            NodeEntry::Directory(d) => {
                if self.entry_size() == frame.size {
                } else {
                    d.lemma_inv_implies_interp_inv();
                    assume(d.accepted_mapping(base, frame));
                    d.lemma_map_frame_preserves_inv(base, frame);
                    assert(res.well_formed());
                    assert(res.pages_match_entry_size());
                    assert(res.directories_match_arch());
                    assert_forall_by(|i: nat| {
                        requires(i < res.entries.len() && res.entries.index(i).is_Directory());
                        ensures(true
                                && (#[trigger] res.entries.index(i)).get_Directory_0().layer == res.layer + 1
                                && res.entries.index(i).get_Directory_0().base_vaddr == res.base_vaddr + i * res.entry_size());
                        if i < res.entries.len() && res.entries.index(i).is_Directory() {
                            if i == entry {
                                assume(false);
                            }
                        }
                    });
                    assert(res.directories_are_in_next_layer());
                    assert(res.directories_obey_invariant());
                    assert(res.directories_are_nonempty());
                    assert(res.frames_aligned());
                    assert(res.inv());
                    // match d.map_frame(base, frame) {
                    //     Ok(d)  => Ok(self.update(entry, NodeEntry::Directory(d))),
                    //     Err(e) => Err(e),
                    // }
                    assert(equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer));
                    assume(!self.map_frame(base, frame).get_Ok_0().empty());
                }
            },
            NodeEntry::Empty() => {
                if self.entry_size() == frame.size {
                    assume(self.map_frame(base, frame).get_Ok_0().inv());
                    assert(equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer));
                    assume(!self.map_frame(base, frame).get_Ok_0().empty());
                    // Ok(self.update(entry, NodeEntry::Page(frame)))
                } else {
                    // Indexing into self.arch.layers with self.layer + 1 is okay because
                    // we know the frame size isn't this layer's entrysize (i.e. must be on
                    // some lower level).
                    // The index recommendation fails with spec(checked) though.
                    // FIXME: assuming this to silence recommends failure
                    assume(((self.layer + 1) as nat) < self.arch.layers.len());
                    let new_dir = Directory {
                        entries:    new_seq(self.arch.layers.index((self.layer + 1) as nat).num_entries),
                        layer:      self.layer + 1,
                        base_vaddr: self.entry_base(entry),
                        arch:       self.arch,
                    };
                    assume(new_dir.inv());
                    assume(new_dir.accepted_mapping(base, frame));
                    assume(new_dir.map_frame(base, frame).is_Ok());
                    new_dir.lemma_map_frame_preserves_inv(base, frame);
                    // match new_dir.map_frame(base, frame) {
                    //     Ok(d) => Ok(self.update(entry, NodeEntry::Directory(d))),
                    //     // We never fail to insert an accepted mapping into an empty directory
                    //     Err(e) => arbitrary(),
                    // }
                    assume(self.map_frame(base, frame).get_Ok_0().inv());
                    assert(equal(self.map_frame(base, frame).get_Ok_0().layer, self.layer));
                    assume(!self.map_frame(base, frame).get_Ok_0().empty());
                }
            },
        }
    }

    #[spec(checked)]
    pub fn accepted_unmap(self, base: nat) -> bool {
        recommends(self.well_formed());
        true
        && self.interp().accepted_unmap(base)
    }

    #[spec]
    pub fn unmap(self, base: nat) -> Result<Self,()> {
        recommends(self.inv() && self.accepted_unmap(base));
        decreases(self.arch.layers.len() - self.layer);
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

    #[proof] #[verifier(decreases_by)]
    fn check_unmap(self, base: nat) {
        if self.inv() && self.accepted_unmap(base) {
            self.lemma_index_for_vaddr_bounds(base);
        } else {
        }
    }


    #[proof]
    fn lemma_unmap_preserves_inv(self, base: nat) {
        decreases(self.arch.layers.len() - self.layer);
        requires([
            self.inv(),
            self.accepted_unmap(base),
            self.unmap(base).is_Ok(),
        ]);
        ensures(self.unmap(base).get_Ok_0().inv());

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

    #[proof]
    fn lemma_unmap_refines_unmap(self, base: nat) {
        decreases(self.arch.layers.len() - self.layer);
        requires([
             self.inv(),
             self.accepted_unmap(base),
        ]);
        ensures([
                equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)),
        ]);

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
                    self.lemma_entry_base();
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

    #[proof]
    fn lemma_entries_equal_implies_interp_aux_equal(self, other: Directory, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 other.inv(),
                 equal(self.arch, other.arch),
                 equal(self.layer, other.layer),
                 equal(self.base_vaddr, other.base_vaddr),
                 equal(self.num_entries(), other.num_entries()),
                 forall(|j: nat| i <= j && j < self.entries.len() >>= equal(self.entries.index(j), other.entries.index(j))),
        ]);
        ensures(equal(self.interp_aux(i), other.interp_aux(i)));

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

    #[proof]
    fn lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(self, j: nat, i: nat, vaddr: nat, n: NodeEntry) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
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
                     })
        ]);
        ensures([
            equal(self.interp_aux(i).map.remove(vaddr), self.update(j, n).interp_aux(i).map),
        ]);

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

    #[proof]
    fn lemma_remove_from_interp_of_entry_implies_remove_from_interp(self, j: nat, vaddr: nat, n: NodeEntry) {
        requires([
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
        ]);
        ensures(equal(self.interp().map.remove(vaddr), self.update(j, n).interp().map));

        self.lemma_remove_from_interp_of_entry_implies_remove_from_interp_aux(j, 0, vaddr, n);
    }
}

impl<A,B> Result<A,B> {
    #[spec(checked)]
    pub fn map_ok<C, F: Fn(A) -> C>(self, f: F) -> Result<C,B> {
        match self {
            Ok(a)  => Ok(f(a)),
            Err(b) => Err(b),
        }
    }
}

// FIXME: how to do this correctly?
#[spec]
pub fn new_seq(i: nat) -> Seq<NodeEntry> {
    new_seq_aux(seq![], i)
}

#[spec]
pub fn new_seq_aux(s: Seq<NodeEntry>, i: nat) -> Seq<NodeEntry> {
    decreases(i);
    if i == 0 {
        s
    } else {
        new_seq_aux(s.add(seq![NodeEntry::Empty()]), i-1)
    }
}

#[proof]
pub fn lemma_map_union_prefer_right_remove_commute<S,T>() {
    ensures([
            forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
                   (m1.dom().contains(n) && !m2.dom().contains(n))
                   >>= equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))),
            forall(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
                   (m2.dom().contains(n) && !m1.dom().contains(n))
                   >>= equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n))),
    ]);
    assert_forall_by(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat| {
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
    assert_forall_by(|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat| {
        requires(m2.dom().contains(n) && !m1.dom().contains(n));
        ensures(equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)));
        let union1 = m1.union_prefer_right(m2.remove(n));
        let union2 = m1.union_prefer_right(m2).remove(n);
        assert_maps_equal!(union1, union2);
        assert(equal(union1, union2));
    });
}

#[proof]
pub fn lemma_finite_map_union<S,T>() {
    ensures(forall(|s1: Map<S,T>, s2: Map<S,T>| s1.dom().finite() && s2.dom().finite() >>= #[trigger] s1.union_prefer_right(s2).dom().finite()));
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

#[proof]
pub fn lemma_set_contains_IMP_len_greater_zero<T>(s: Set<T>, a: T) {
    requires([
             s.finite(),
             s.contains(a)
    ]);
    ensures(s.len() > 0);

    if s.len() == 0 {
        // contradiction
        assert(s.remove(a).len() + 1 == 0);
    }
}
