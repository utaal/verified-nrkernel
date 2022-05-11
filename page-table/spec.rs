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
use crate::{seq, seq_insert_rec, map, map_insert_rec, assert_maps_equal};
#[allow(unused_imports)]
use result::{*, Result::*};

#[proof]
fn ambient_lemmas() {
    ensures([
        true,
        //forall(|a: nat, b: nat| a * b == b * a),
    ]);

    // assert_forall_by(|a: nat, b: nat| {
    //     ensures(a * b == b * a);
    //     assert_nonlinear_by({
    //         ensures(a * b == b * a);
    //     });
    // });
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
                forall(|i: nat| #[trigger] self.entry_base(i + 1) == self.entry_base(i) + self.entry_size()),
        ]);

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
            });

            assert(interp.mappings_in_bounds());

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

        self.lemma_inv_implies_interp_inv();

        assert(between(vaddr, self.base_vaddr, self.upper_vaddr()));
        let entry = self.index_for_vaddr(vaddr);
        self.lemma_index_for_vaddr_bounds(vaddr);
        match self.entries.index(entry) {
            NodeEntry::Page(p) => {
            },
            NodeEntry::Directory(d) => {
                assert(self.directories_obey_invariant());
                assert(d.inv());
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
        // assume(false); // FIXME: extremely unstable lemma
        self.lemma_inv_implies_interp_inv();
        let i = self.index_for_vaddr(vaddr);
        // assume(aligned(vaddr, self.entry_size()) >>= vaddr == self.base_vaddr + i * self.entry_size());
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
                assert(self.directories_obey_invariant());
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

    // #[spec(checked)]
    // pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
    //     self.interp().accepted_mapping(base, frame)
    // }

    // #[spec]
    // pub fn map_frame(self, base: nat, frame: MemRegion) -> Result<Self,()> {
    //     decreases(self.arch.layers.len() - self.layer);
    //     decreases_by(Self::check_map_frame);

    //     if self.inv() && self.accepted_mapping(base, frame) {
    //         let offset = base - self.base_vaddr;
    //         let base_offset = offset - (offset % self.entry_size());
    //         let entry = base_offset / self.entry_size();
    //         if self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
    //             // this condition implies that "entry < self.entries.len()"
    //             match self.entries.index(entry) {
    //                 NodeEntry::Page(p) => {
    //                     Err(())
    //                 },
    //                 NodeEntry::Directory(d) => {
    //                     if self.entry_size() == frame.size {
    //                         Err(())
    //                     } else {
    //                         match d.map_frame(base, frame) {
    //                             Ok(d)  => Ok(self.update(entry, NodeEntry::Directory(d))),
    //                             Err(e) => Err(e),
    //                         }
    //                     }
    //                 },
    //                 NodeEntry::Empty() => {
    //                     if self.entry_size() == frame.size {
    //                         Ok(self.update(entry, NodeEntry::Page(frame)))
    //                     } else {
    //                         // Indexing into self.arch.layers with self.layer + 1 is okay because
    //                         // we know the frame size isn't this layer's entrysize (i.e. must be on
    //                         // some lower level).
    //                         // The index recommendation fails with spec(checked) though.
    //                         let new_dir = Directory {
    //                             entries:    new_seq(self.arch.layers.index((self.layer + 1) as nat).num_entries),
    //                             layer:      self.layer + 1,
    //                             base_vaddr: self.base_vaddr + offset,
    //                             arch:       self.arch,
    //                         }.map_frame(base, frame);
    //                             // FIXME: am i certain this mapping will always be ok? might be
    //                             // tricky to prove.
    //                         Ok(self.update(entry, NodeEntry::Directory(new_dir.get_Ok_0())))
    //                     }
    //                 },
    //             }
    //         } else {
    //             Err(())
    //         }
    //     } else {
    //         arbitrary()
    //     }
    // }

    // #[proof] #[verifier(decreases_by)]
    // fn check_map_frame(self, base: nat, frame: MemRegion) {
    //     if self.inv() && self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
    //         self.lemma_derive_entry_bounds_from_if_condition(base);
    //         assert(self.directories_obey_invariant());
    //     } else {
    //     }
    // }

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
                        Ok(self.update(entry, NodeEntry::Empty()))
                    } else {
                        Err(())
                    }
                },
                NodeEntry::Directory(d) => {
                    d.unmap(base).map_ok(|new_d|
                        self.update(entry, if d.empty() {
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

        let res = self.unmap(base).get_Ok_0();
        assert(self.directories_obey_invariant());

        let entry = self.index_for_vaddr(base);
        self.lemma_index_for_vaddr_bounds(base);

        let _ = self.interp_of_entry(entry);

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
                assume(equal(self.interp_of_entry(entry), d.interp())); // FIXME
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


    // // // This is only proved for NodeEntry::Empty() because we'd have to have more requirements on
    // // // pages and directories to ensure the invariant remains intact. Otherwise interp_aux is
    // // // arbitrary.
    // // #[proof]
    // // fn lemma_update_leq_interp_aux_idempotent(self, i: nat) {
    // //     decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
    // //     requires([
    // //              self.inv(),
    // //     ]);
    // //     ensures(forall(|n: nat| n < i && n < self.entries.len() >>= equal((#[trigger] self.update(n, NodeEntry::Empty())).interp_aux(i), self.interp_aux(i))));

    // //     assert_forall_by(|n: nat| {
    // //         requires(n < i && n < self.entries.len());
    // //         ensures(equal((#[trigger] self.update(n, NodeEntry::Empty())).interp_aux(i), self.interp_aux(i)));

    // //         assume(self.update(n, NodeEntry::Empty()).inv());
    // //         if i >= self.entries.len() {
    // //         } else {
    // //             self.lemma_update_leq_interp_aux_idempotent(i+1);
    // //         }
    // //     });
    // // }

    // // #[proof]
    // // fn lemma_update_empty_interp_aux_equal_interp_aux_remove(self, i: nat, n: nat) {
    // //     decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
    // //     requires([
    // //              self.inv(),
    // //              i <= n,
    // //              n < self.entries.len(),
    // //              self.entries.index(n).is_Page(),
    // //     ]);
    // //     ensures(equal(self.update(n, NodeEntry::Empty()).interp_aux(i), self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));

    // //     let n_vaddr = self.base_vaddr + n * self.entry_size();
    // //     let p = self.entries.index(n).get_Page_0();
    // //     assert_by(self.interp_aux(i).map.dom().contains(n_vaddr), {
    // //             self.lemma_interp_aux_facts_page(i, n);
    // //     });
    // //     self.lemma_inv_implies_interp_inv();
    // //     self.lemma_inv_implies_interp_aux_inv(i+1);
    // //     crate::lib::mul_distributive(i, self.entry_size());

    // //     let updi = self.update(n, NodeEntry::Empty());
    // //     assume(updi.inv());
    // //     if i >= self.entries.len() {
    // //     } else {
    // //         if i == n {
    // //             assert(equal(updi.interp_aux(i), updi.interp_aux(i+1)));
    // //             assert(!self.interp_aux(i+1).map.dom().contains(n_vaddr));
    // //             assert_maps_equal!(self.interp_aux(i).remove(n_vaddr).map, self.interp_aux(i+1).map);
    // //             assert(equal(self.interp_aux(i).remove(n_vaddr), self.interp_aux(i+1)));
    // //             if i+1 < self.entries.len() {
    // //                 self.lemma_update_leq_interp_aux_idempotent(i+1);
    // //             } else {
    // //             }
    // //             assert(equal(updi.interp_aux(i), self.interp_aux(i).remove(n_vaddr)));
    // //         } else {
    // //             assert(i < n);
    // //             self.lemma_update_empty_interp_aux_equal_interp_aux_remove(i+1, n);
    // //             assert(equal(
    // //                     updi.interp_aux(i+1),
    // //                     self.interp_aux(i+1).remove(self.base_vaddr + n * self.entry_size())));
    // //             self.lemma_interp_aux_disjoint(i);
    // //             let rem = self.interp_aux(i + 1).map;
    // //             match self.entries.index(i) {
    // //                 NodeEntry::Page(p)      => {
    // //                     assert(equal(self.interp_aux(i).map, rem.insert(self.base_vaddr + i * self.entry_size(), p)));
    // //                     assert(equal(updi.entries.index(i), self.entries.index(i)));
    // //                     assume(false);
    // //                     // assert(equal(
    // //                     //         self.update(n, NodeEntry::Empty()).interp_aux(i).map,
    // //                     //         self.update(n, NodeEntry::Empty()).interp_aux(i+1).map.insert(self.base_vaddr + i * self.entry_size(), p)));
    // //                     // assert(equal(self.update(n, NodeEntry::Empty()).interp_aux(i), self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));

    // //                     //rem.insert(self.base_vaddr + i * self.entry_size(), p),
    // //                     // assert(equal(
    // //                     //         self.update(n, NodeEntry::Empty()).interp_aux(i),
    // //                     //         self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));
    // //                 },
    // //                 NodeEntry::Directory(d) => {
    // //                     assume(false);
    // //                     //rem.union_prefer_right(d.interp_aux(0).map),
    // //                 },
    // //                 NodeEntry::Empty()      => (),
    // //             }
    // //         }
    // //     }
    // // }

    // // #[proof]
    // // fn lemma_update_empty_interp_equal_interp_remove(self, n: nat) {
    // //     requires(self.entries.index(n).is_Page());
    // //     ensures(equal(self.update(n, NodeEntry::Empty()).interp(), self.interp().remove(self.base_vaddr + n * self.entry_size())));
    // //     assume(false);
    // // }

    // #[proof]
    // fn lemma_derive_unmap_page_base_bound(self, base: nat) {
    //     requires([
    //              self.inv(),
    //              self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries(),
    //              { let offset = base - self.base_vaddr;
    //                let base_offset = offset - (offset % self.entry_size());
    //                let entry = base_offset / self.entry_size();
    //                self.entries.index(entry).is_Page()
    //              },
    //     ]);
    //     ensures({
    //         let offset = base - self.base_vaddr;
    //         let base_offset = offset - (offset % self.entry_size());
    //         let entry = base_offset / self.entry_size();
    //         if aligned(base, self.entry_size()) {
    //             base == self.base_vaddr + entry * self.entry_size()
    //         } else {
    //             base > self.base_vaddr + entry * self.entry_size()
    //         }
    //     });
    //     let offset = base - self.base_vaddr;
    //     let base_offset = offset - (offset % self.entry_size());
    //     let entry = base_offset / self.entry_size();
    //     if aligned(base, self.entry_size()) {
    //         assert_by(base == self.base_vaddr + entry * self.entry_size(), {
    //             crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
    //             crate::lib::subtract_mod_eq_zero(self.base_vaddr, base, self.entry_size());
    //             crate::lib::div_mul_cancel(base_offset, self.entry_size());
    //         });
    //     } else {
    //         assert_nonlinear_by({
    //             requires([
    //                 self.entry_size() > 0,
    //                 base % self.entry_size() > 0,
    //                 self.base_vaddr % (self.entry_size() * self.num_entries()) == 0,
    //                 self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries(),
    //                 offset == base - self.base_vaddr,
    //                 base_offset == offset - (offset % self.entry_size()),
    //                 entry == base_offset / self.entry_size(),
    //             ]);
    //             ensures([
    //                 base > self.base_vaddr + entry * self.entry_size(),
    //             ]);

    //             crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
    //             crate::lib::multiple_offsed_mod_gt_0(base, self.base_vaddr, self.entry_size());
    //             crate::lib::mod_less_eq(base, self.entry_size());
    //             crate::lib::mod_less_eq(offset, self.entry_size());
    //             crate::lib::subtract_mod_aligned(offset, self.entry_size());
    //         });
    //     }
    // }

    // #[proof]
    // fn unmap_preserves_inv(self, base: nat) {
    //     requires([
    //         self.inv(),
    //         self.accepted_unmap(base),
    //         self.unmap(base).is_Ok(),
    //     ]);
    //     ensures(self.unmap(base).get_Ok_0().inv());
    //     decreases(self.arch.layers.len() - self.layer);

    //     let offset = base - self.base_vaddr;
    //     let base_offset = offset - (offset % self.entry_size());
    //     let entry = base_offset / self.entry_size();
    //     self.lemma_derive_entry_bounds_from_if_condition(base);
    //     assert(entry < self.entries.len());
    //     match self.entries.index(entry) {
    //         NodeEntry::Page(p)      => {
    //             self.lemma_derive_unmap_page_base_bound(base);
    //             let nself = self.update(entry, NodeEntry::Empty());
    //             assert(self.directories_obey_invariant());
    //             assert(nself.directories_obey_invariant());
    //             assert(nself.inv());
    //             assert(self.unmap(base).get_Ok_0().inv());
    //         },
    //         NodeEntry::Directory(d) => {
    //             assert(self.directories_obey_invariant());

    //             assert(self.directories_obey_invariant());
    //             assert(d.inv());
    //             assert(d.well_formed());

    //             // LEMMA ?
    //             assert_nonlinear_by({
    //                 requires([
    //                     self.entry_size() > 0,
    //                     self.entry_size() == d.entry_size() * d.num_entries(),
    //                     offset == base - self.base_vaddr,
    //                     base_offset == offset - (offset % self.entry_size()),
    //                     entry == base_offset / self.entry_size(),
    //                     d.base_vaddr == self.base_vaddr + entry * self.entry_size(),
    //                     self.base_vaddr <= base,
    //                 ]);
    //                 ensures([
    //                     d.base_vaddr <= base,
    //                     base < d.base_vaddr + d.entry_size() * d.num_entries(), // TODO: extract as lemma
    //                 ]);
    //                 crate::lib::subtract_mod_aligned(offset, self.entry_size());
    //                 crate::lib::mod_add_zero(base_offset, self.entry_size(), self.entry_size());
    //             });
    //             // TODO assert(d.vaddr_in_bounds(base));
    //             assert(d.accepted_unmap(base));

    //             d.unmap_preserves_inv(base);
    //             let nself = self.unmap(base).get_Ok_0();
    //             assert(nself.directories_obey_invariant());
    //             assert(self.unmap(base).get_Ok_0().inv());
    //         },
    //         NodeEntry::Empty()      => {
    //             assert(self.unmap(base).get_Ok_0().inv());
    //         },
    //     }
    // }

    // #[proof]
    // fn unmap_refines_unmap(self, base: nat) {
    //     requires([
    //          self.inv(),
    //          self.accepted_unmap(base),
    //     ]);
    //     ensures(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));

    //     self.lemma_inv_implies_interp_inv();

    //     if let Ok(nself) = self.unmap(base) {
    //         self.unmap_preserves_inv(base);
    //         nself.lemma_inv_implies_interp_inv();
    //         assert(nself.interp().inv());
    //     }

    //     let nself_res = self.unmap(base);
    //     let nself = self.unmap(base).get_Ok_0();

    //     let i_nself_res = self.interp().unmap(base);
    //     let i_nself = i_nself_res.get_Ok_0();

    //     let offset = base - self.base_vaddr;
    //     let base_offset = offset - (offset % self.entry_size());
    //     let entry = base_offset / self.entry_size();
    //     assert(self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries());
    //     self.lemma_derive_entry_bounds_from_if_condition(base);
    //     assert(entry < self.entries.len());
    //     match self.entries.index(entry) {
    //         NodeEntry::Page(p)      => {
    //             self.lemma_derive_unmap_page_base_bound(base);
    //             if aligned(base, self.entry_size()) {
    //                 assert(nself_res.is_Ok());

    //                 assert(equal(nself, self.update(entry, NodeEntry::Empty())));

    //                 self.lemma_interp_facts_page(entry);
    //                 assert(base == self.base_vaddr + entry * self.entry_size());

    //                 assert(equal(self.interp().remove(base), self.update(entry, NodeEntry::Empty()).interp()));

    //                 assert(self.interp().map.contains_pair(base, p));

    //                 assert(equal(i_nself, self.interp().remove(base)));

    //                 assert(i_nself_res.is_Ok());
    //                 assert(equal(nself.interp(), i_nself));

    //                 assert(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));
    //             } else {
    //                 assume(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));
    //             }
    //         },
    //         NodeEntry::Directory(d) => {
    //             assume(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));
    //         },
    //         NodeEntry::Empty()      => {
    //             assume(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));
    //         },
    //     }
    // }

    // #[proof]
    // fn lemma_not_contains_from_if_condition(self, base: nat) {
    //     requires([
    //              self.inv(),
    //              !(self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries()),
    //     ]);
    //     ensures(!self.interp().map.dom().contains(base));
    //     self.lemma_inv_implies_interp_inv();
    // }
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
