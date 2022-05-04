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

pub struct MemRegion { pub base: nat, pub size: nat }

// TODO use VAddr, PAddr

#[spec]
pub fn strictly_decreasing(s: Seq<nat>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) > s.index(j))
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
        forall(|i:int| with_triggers!([self.layers.index(i).entry_size], [self.layers.index(i).num_entries] => 0 <= i && i < self.layers.len() >>= (
            true
            && self.layers.index(i).entry_size > 0
            && self.layers.index(i).num_entries > 0
            && self.entry_size_is_next_layer_size(i))))
    }

    #[spec(checked)]
    pub fn entry_size_is_next_layer_size(self, i: int) -> bool {
        recommends(0 <= i && i < self.layers.len());
        i + 1 < self.layers.len() >>=
            self.layers.index(i).entry_size == self.layers.index(i + 1).entry_size * self.layers.index(i + 1).num_entries
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
        && self.mappings_are_aligned()
        && self.mappings_dont_overlap()
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
    pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
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
    }

    // predicate (function -> bool)
    // #[spec] pub fn step_map_frame(&self /* s */, post: &PageTableContents /* s' */, base:nat, frame: MemRegion) -> bool {
    //     post == self.map_frame(base, frame)
    // }

    // TODO later /// Changes the mapping permissions of the region containing `vaddr` to `rights`.
    // TODO later fn adjust(self, vaddr: nat) -> Result<(VAddr, usize), KError>;

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    // #[spec] fn resolve(self, vaddr: nat) -> MemRegion {
    #[spec(checked)]
    fn resolve(self, vaddr: nat) -> Result<nat,()> {
        if exists(|n:nat|
                  self.map.dom().contains(n) &&
                  n <= vaddr && vaddr < n + (#[trigger] self.map.index(n)).size) {
            let n = choose(|n:nat|
                           self.map.dom().contains(n) &&
                           n <= vaddr && vaddr < n + (#[trigger] self.map.index(n)).size);
            let offset = vaddr - n;
            Ok(self.map.index(n).base + offset)
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
    fn unmap_preserves_inv(self, base: nat) {
        requires([
            self.inv(),
            self.unmap(base).is_Ok()
        ]);
        ensures([
            self.unmap(base).get_Ok_0().inv()
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

    // forall self :: self.directories_obey_invariant()

    #[spec(checked)]
    pub fn interp(self) -> PageTableContents {
        // recommends(self.inv());
        self.interp_aux(0)
    }

    #[spec(checked)]
    pub fn interp_aux(self, i: nat) -> PageTableContents {
        // TODO: Adding the recommendation causes a warning on the recursive call, which we can't
        // prevent without writing assertions.
        // recommends(self.inv());
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        // decreases_by(Self::check_interp_aux);

        if self.inv() {
            if i >= self.entries.len() {
                PageTableContents {
                    map: map![],
                    arch: self.arch,
                }
            } else { // i < self.entries.len()
                let rem = self.interp_aux(i + 1).map;
                PageTableContents {
                    map: match self.entries.index(i) {
                        NodeEntry::Page(p)      => rem.insert(self.base_vaddr + i * self.entry_size(), p),
                        NodeEntry::Directory(d) => rem.union_prefer_right(d.interp_aux(0).map),
                        NodeEntry::Empty()      => rem,
                    },
                    arch: self.arch,
                }
            }
        } else {
            arbitrary()
        }
    }

    #[proof]
    fn inv_implies_interp_aux_entries_positive_entry_size(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires(self.inv());
        ensures([
                forall(|va: nat| #[trigger] self.interp_aux(i).map.dom().contains(va)
                       >>= self.interp_aux(i).map.index(va).size > 0),
        ]);
        assert_forall_by(|va: nat| {
            requires(self.interp_aux(i).map.dom().contains(va));
            ensures(#[trigger] self.interp_aux(i).map.index(va).size > 0);

            if i >= self.entries.len() {
            } else {
                self.inv_implies_interp_aux_entries_positive_entry_size(i+1);
                match self.entries.index(i) {
                    NodeEntry::Page(p) => {
                        let new_va = self.base_vaddr + i * self.entry_size();
                        if new_va == va {
                        } else {
                            assert(self.interp_aux(i+1).map.index(va).size > 0);
                        }
                    },
                    NodeEntry::Directory(d) => {
                        assert(self.directories_obey_invariant());
                        d.inv_implies_interp_aux_entries_positive_entry_size(0);
                        if d.interp_aux(0).map.dom().contains(va) {
                        } else {
                            assert(self.interp_aux(i+1).map.dom().contains(va));
                        }
                    },
                    NodeEntry::Empty() => {
                        assert(self.interp_aux(i+1).map.index(va).size > 0);
                    },
                };
            }
        });
    }

    #[proof]
    fn inv_implies_interp_aux_inv(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires(self.inv());
        ensures([
            self.interp_aux(i).inv(),
            forall(|va: nat| #[trigger] self.interp_aux(i).map.dom().contains(va) >>= va >= self.base_vaddr + i * self.entry_size()),
            forall(|va: nat| #[trigger] self.interp_aux(i).map.dom().contains(va) >>= va <  self.base_vaddr + self.num_entries() * self.entry_size()),
            forall(|va: nat| self.interp_aux(i).map.dom().contains(va)
                   >>= va + #[trigger] self.interp_aux(i).map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size()),
        ]);

        let interp = self.interp_aux(i);

        assert(self.directories_obey_invariant());
        assert_forall_by(|i: nat| {
            requires(i < self.entries.len() && self.entries.index(i).is_Directory());
            ensures((#[trigger] self.entries.index(i)).get_Directory_0().interp_aux(0).inv());
            self.entries.index(i).get_Directory_0().inv_implies_interp_aux_inv(0);
        });
        assert_forall_by(|va: nat| {
            requires(interp.map.dom().contains(va));
            ensures(true
                && aligned(va, (#[trigger] interp.map.index(va)).size)
                && aligned(interp.map.index(va).base, interp.map.index(va).size)
            );

            if i >= self.entries.len() {
            } else {
                let j = i + 1;
                self.inv_implies_interp_aux_inv(j);
                if self.entries.index(i).is_Page() {
                    if va < self.base_vaddr + i * self.entry_size() {
                        assert_nonlinear_by({
                            ensures((i + 1) * self.entry_size() == i * self.entry_size() + self.entry_size());
                        });
                        assert(false);
                    } else if va == self.base_vaddr + i * self.entry_size() {
                        assert(aligned(self.base_vaddr, self.entry_size() * self.num_entries()));
                        assert_nonlinear_by({
                            requires([
                                self.layer < self.arch.layers.len(),
                                aligned(self.base_vaddr, self.entry_size() * self.num_entries()),
                                self.entry_size() > 0,
                                self.num_entries() > 0,
                            ]);
                            ensures(aligned(self.base_vaddr + i * self.entry_size(), self.entry_size()));

                            crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
                            // assert(aligned(self.base_vaddr, self.entry_size()));
                            crate::lib::mod_of_mul(i, self.entry_size());
                            // assert((i * self.entry_size()) % self.entry_size() == 0);
                            crate::lib::mod_add_zero(self.base_vaddr, i * self.entry_size(), self.entry_size());
                        });
                    } else {
                    }
                }
            }
        });
        assert_forall_by(|b1: nat, b2: nat| {
            requires(interp.map.dom().contains(b1) && interp.map.dom().contains(b2) && b1 != b2);
            ensures(!overlap(
                MemRegion { base: b1, size: interp.map.index(b1).size },
                MemRegion { base: b2, size: interp.map.index(b2).size }
            ));

            if i >= self.entries.len() {
            } else {
                self.inv_implies_interp_aux_inv(i + 1);
                let (c1, c2) = if b1 < b2 {
                    (b1, b2)
                } else {
                    (b2, b1)
                };
                match self.entries.index(i) {
                    NodeEntry::Page(p) => {
                        let new_va = self.base_vaddr + i * self.entry_size();
                        if c1 != new_va && c2 != new_va {
                        } else if c1 == new_va {
                            assert_nonlinear_by({
                                ensures((i + 1) * self.entry_size() == i * self.entry_size() + self.entry_size());
                            });
                        } else {
                            assert_nonlinear_by({
                                requires([
                                    c1 >= self.base_vaddr + (i + 1) * self.entry_size(),
                                    c2 == self.base_vaddr + i * self.entry_size(),
                                ]);
                                ensures(c1 >= c2);
                            });
                            assert(false);
                        }
                    },
                    NodeEntry::Directory(d) => {
                        d.inv_implies_interp_aux_inv(0);
                        assert_nonlinear_by({
                            requires(self.entry_size() == d.entry_size() * d.num_entries());
                            ensures([
                                self.entry_size() == d.num_entries() * d.entry_size(),
                                (i + 1) * self.entry_size() == i * self.entry_size() + self.entry_size(),
                            ]);
                        });

                        // let i1_interp = self.interp_aux(i + 1).map;
                        // let d_interp = d.interp_aux(0).map;
                        // if i1_interp.dom().contains(c1) && i1_interp.dom().contains(c2) {
                        // } else if d_interp.dom().contains(c1) && d_interp.dom().contains(c2) {
                        // } else if d_interp.dom().contains(c1) && i1_interp.dom().contains(c2) {
                        // } else {
                        //     assert(false);
                        // }
                    },
                    NodeEntry::Empty() => (),
                }
            }
        });

        // Prove the other postconditions
        assert_forall_by(|va: nat| {
            requires(self.interp_aux(i).map.dom().contains(va));
            ensures(#[auto_trigger] true
                && va >= self.base_vaddr + i * self.entry_size()
                && va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size()
                && va < self.base_vaddr + self.num_entries() * self.entry_size());

            if i >= self.entries.len() {
            } else {
                assert_nonlinear_by({
                    ensures((va >= self.base_vaddr + (i + 1) * self.entry_size()) >>= (va >= self.base_vaddr + i * self.entry_size()));
                });

                self.inv_implies_interp_aux_inv(i + 1);
                match self.entries.index(i) {
                    NodeEntry::Page(p) => {
                        let new_va = self.base_vaddr + i * self.entry_size();
                        if va == new_va {
                            assert_nonlinear_by({
                                requires([
                                    p.size == self.entry_size(),
                                    i < self.num_entries(),
                                ]);
                                ensures([
                                    i * self.entry_size() + p.size == (i + 1) * self.entry_size(),
                                    (i + 1) * self.entry_size() <= self.num_entries() * self.entry_size(),
                                ]);
                            });
                            assert(va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size());
                        } else {
                        }
                    },
                    NodeEntry::Directory(d) => {
                        d.inv_implies_interp_aux_inv(0);
                        let i1_interp = self.interp_aux(i + 1).map;
                        let d_interp = d.interp_aux(0).map;
                        if d_interp.dom().contains(va) {
                            assert(self.entry_size() == d.entry_size() * d.num_entries());
                            assert_nonlinear_by({
                                ensures([
                                    d.entry_size() * d.num_entries() == d.num_entries() * d.entry_size(),
                                    (i + 1) * self.entry_size() == i * self.entry_size() + self.entry_size(),
                                ]);
                            });

                            assert(va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + i * self.entry_size() + self.entry_size());
                            assert(i + 1 <= self.num_entries());

                            assert_nonlinear_by({
                                requires(i + 1 <= self.num_entries());
                                ensures((i + 1) * self.entry_size() <= self.num_entries() * self.entry_size());
                            });

                            assert_nonlinear_by({
                                requires([
                                    self.layer < self.arch.layers.len(),
                                    self.entry_size() == d.entry_size() * d.num_entries(),
                                    va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + i * self.entry_size() + self.entry_size(),
                                    i + 1 <= self.num_entries(),
                                ]);
                                ensures([
                                    va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + (i + 1) * self.entry_size(),
                                    (i + 1) * self.entry_size() <= self.num_entries() * self.entry_size(),
                                ]);
                            });
                        } else {
                        }
                    },
                    NodeEntry::Empty() => {
                    },
                }
                // Post3
                self.inv_implies_interp_aux_entries_positive_entry_size(i);
            }
        });
    }

    #[proof]
    fn inv_implies_interp_inv(self) {
        requires(self.inv());
        ensures([
            self.interp().inv(),
            forall(|va: nat| #[trigger] self.interp().map.dom().contains(va) >>= va >= self.base_vaddr),
            forall(|va: nat| #[trigger] self.interp().map.dom().contains(va) >>= va <  self.base_vaddr + self.num_entries() * self.entry_size()),
            forall(|va: nat| self.interp().map.dom().contains(va)
                   >>= va + #[trigger] self.interp().map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size()),
        ]);
        self.inv_implies_interp_aux_inv(0);
    }

    #[proof]
    fn lemma_interp_aux_disjoint(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i < self.entries.len(),
        ]);
        ensures([
                #[trigger] self.entries.index(i).is_Directory()
                >>= equal(self.interp_aux(i+1).map.union_prefer_right(self.entries.index(i).get_Directory_0().interp_aux(0).map),
                          self.entries.index(i).get_Directory_0().interp_aux(0).map.union_prefer_right(self.interp_aux(i+1).map)),
                forall(|va: nat| #[trigger] self.interp_aux(i+1).map.dom().contains(va) >>= va > self.base_vaddr + i * self.entry_size()),
        ]);

        // Post1
        if self.entries.index(i).is_Directory() {
            let rem = self.interp_aux(i+1).map;
            let d = self.entries.index(i).get_Directory_0();
            let d_interp = d.interp_aux(0).map;
            assert_forall_by(|va: nat| {
                ensures(!rem.dom().contains(va) || !d_interp.dom().contains(va));

                if rem.dom().contains(va) && d_interp.dom().contains(va) {
                    self.inv_implies_interp_aux_inv(i+1);
                    assert(self.directories_obey_invariant());
                    d.inv_implies_interp_aux_inv(0);
                    assert_nonlinear_by({
                        requires([
                            self.entry_size() > 0,
                            d.base_vaddr == self.base_vaddr + i * self.entry_size(),
                            va >= self.base_vaddr + (i+1) * self.entry_size(),
                            va < d.base_vaddr + d.num_entries() * d.entry_size(),
                            d.entry_size() * d.num_entries() == self.entry_size(),
                        ]);
                        ensures([
                            va < self.base_vaddr + (i+1) * self.entry_size(),
                        ]);
                    });
                }
            });
            let un1 = rem.union_prefer_right(d_interp);
            let un2 = d_interp.union_prefer_right(rem);
            assert(un1.ext_equal(un2));
        }

        // Post2
        self.inv_implies_interp_aux_inv(i+1);
        assert_nonlinear_by({
            requires([
                self.entry_size() > 0,
                forall(|va: nat| #[trigger] self.interp_aux(i+1).map.dom().contains(va) >>= va >= self.base_vaddr + (i+1) * self.entry_size()),
            ]);
            ensures(forall(|va: nat| #[trigger] self.interp_aux(i+1).map.dom().contains(va) >>= va > self.base_vaddr + i * self.entry_size()));
        });
    }

    #[proof]
    fn lemma_interp_aux_facts_page(self, i: nat, n: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i <= n,
                 n < self.entries.len(),
                 self.entries.index(n).is_Page()
        ]);
        ensures(self.interp_aux(i).map.contains_pair(self.base_vaddr + n * self.entry_size(), self.entries.index(n).get_Page_0()));

        let addr = self.base_vaddr + n * self.entry_size();
        let frame = self.entries.index(n).get_Page_0();

        if i >= self.entries.len() {
        } else {
            if i == n {
            } else {
                self.lemma_interp_aux_facts_page(i + 1, n);
                self.lemma_interp_aux_disjoint(i);
            }
        }
    }

    #[proof]
    fn lemma_interp_facts_page(self, n: nat) {
        requires([
                 self.inv(),
                 n < self.entries.len(),
                 self.entries.index(n).is_Page()
        ]);
        ensures(self.interp().map.contains_pair(self.base_vaddr + n * self.entry_size(), self.entries.index(n).get_Page_0()));
        self.lemma_interp_aux_facts_page(0, n);
    }

    #[proof]
    fn lemma_interp_aux_facts_dir(self, i: nat, n: nat, va: nat, f: MemRegion) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i <= n,
                 n < self.entries.len(),
                 self.entries.index(n).is_Directory(),
                 self.entries.index(n).get_Directory_0().interp_aux(0).map.contains_pair(va, f),
        ]);
        ensures(self.interp_aux(i).map.contains_pair(va, f));

        if i >= self.entries.len() {
        } else { // i < self.entries.len()
            if i == n {
            } else {
                self.lemma_interp_aux_disjoint(i);
                self.lemma_interp_aux_facts_dir(i+1, n, va, f);
            }
        }
    }

    #[proof]
    fn lemma_interp_facts_dir(self, n: nat, va: nat, f: MemRegion) {
        requires([
                 self.inv(),
                 n < self.entries.len(),
                 self.entries.index(n).is_Directory(),
                 self.entries.index(n).get_Directory_0().interp().map.contains_pair(va, f),
        ]);
        ensures(self.interp().map.contains_pair(va, f));
        self.lemma_interp_aux_facts_dir(0, n, va, f);
    }

    #[proof]
    fn lemma_interp_aux_facts_empty(self, i: nat, n: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i <= n,
                 n < self.entries.len(),
                 self.entries.index(n).is_Empty(),
        ]);
        ensures([
                forall(|va: nat|
                       (#[trigger] self.interp_aux(i).map.dom().contains(va))
                       >>= (va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + n * self.entry_size())
                       || (self.base_vaddr + (n+1) * self.entry_size() <= va)),
                equal(self.interp_aux(n), self.interp_aux(n+1)),
        ]);

        assert_forall_by(|va: nat| {
            requires(#[trigger] self.interp_aux(i).map.dom().contains(va));
            ensures((va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + n * self.entry_size())
                    || (self.base_vaddr + (n+1) * self.entry_size() <= va));
            if i >= self.entries.len() {
            } else {
                if i == n {
                    assert(self.interp_aux(i+1).map.dom().contains(va));
                    self.inv_implies_interp_aux_inv(i+1);
                    // assert(va >= self.base_vaddr + (i+1) * self.entry_size());
                } else {
                    self.lemma_interp_aux_facts_empty(i+1, n);
                    if va + self.interp_aux(i).map.index(va).size <= self.base_vaddr + n * self.entry_size() {
                    } else {
                        assert_nonlinear_by({
                            ensures([
                                (i + 1) * self.entry_size() == i * self.entry_size() + self.entry_size(),
                                i + 1 <= n >>= (i + 1) * self.entry_size() <= n * self.entry_size(),
                            ]);
                        });
                        match self.entries.index(i) {
                            NodeEntry::Page(p) => {
                                if va == self.base_vaddr + i * self.entry_size() {
                                } else {
                                    assert(self.interp_aux(i+1).map.dom().contains(va));
                                }
                            },
                            NodeEntry::Directory(d) => {
                                if !d.interp().map.dom().contains(va) {
                                    assert(self.interp_aux(i+1).map.dom().contains(va));
                                } else {
                                    assert(self.directories_obey_invariant());
                                    d.inv_implies_interp_inv();
                                    assert(va + d.interp().map.index(va).size <= d.base_vaddr + d.num_entries() * d.entry_size());
                                }
                            },
                            NodeEntry::Empty() => {
                                self.inv_implies_interp_aux_inv(i+1);
                            },
                        }
                    }
                }
            }
        });
    }

    #[proof]
    fn lemma_interp_facts_empty(self, n: nat) {
        requires([
                 self.inv(),
                 n < self.entries.len(),
                 self.entries.index(n).is_Empty(),
        ]);
        ensures([
                forall(|va: nat|
                       (#[trigger] self.interp().map.dom().contains(va))
                       >>= (va + self.interp().map.index(va).size <= self.base_vaddr + n * self.entry_size())
                       || (self.base_vaddr + (n+1) * self.entry_size() <= va)),
                forall(|va: nat|
                       self.base_vaddr + n * self.entry_size() <= va
                       && va < self.base_vaddr + (n+1) * self.entry_size()
                       >>= !(#[trigger] self.interp().map.dom().contains(va))),
        ]);
        self.lemma_interp_aux_facts_empty(0, n);
        assert_forall_by(|va: nat| {
            requires(self.base_vaddr + n * self.entry_size() <= va
                     && va < self.base_vaddr + (n+1) * self.entry_size());
            ensures(!(#[trigger] self.interp().map.dom().contains(va)));

            if self.interp().map.dom().contains(va) {
                assert(va + self.interp().map.index(va).size <= self.base_vaddr + n * self.entry_size()
                       || self.base_vaddr + (n+1) * self.entry_size() <= va);
                if va + self.interp().map.index(va).size <= self.base_vaddr + n * self.entry_size() {
                    self.inv_implies_interp_aux_entries_positive_entry_size(0);
                    assert(self.interp().map.index(va).size > 0);
                    assert(va < self.base_vaddr + n * self.entry_size());
                } else {
                }
            }
        });
    }

    #[proof]
    fn lemma_interp_aux_subset_interp_aux_plus(self, i: nat, k: nat, v: MemRegion) {
        requires([
                 self.inv(),
                 self.interp_aux(i+1).map.contains_pair(k,v),
        ]);
        ensures(self.interp_aux(i).map.contains_pair(k,v));

        if i >= self.entries.len() {
        } else {
            self.lemma_interp_aux_disjoint(i);
        }
    }

    #[spec(checked)]
    fn resolve(self, vaddr: nat) -> Result<nat,()> {
        decreases(self.arch.layers.len() - self.layer);
        decreases_by(Self::check_resolve);

        if self.inv() {
            if self.base_vaddr <= vaddr && vaddr < self.base_vaddr + self.entry_size() * self.num_entries() {
                // this condition implies that "entry < self.entries.len()"
                let offset = vaddr - self.base_vaddr;
                let base_offset = offset - (offset % self.entry_size());
                let entry = base_offset / self.entry_size();
                // let _ = spec_assert(0 <= entry);
                // let _ = spec_assert(entry < self.num_entries());
                // if entry < self.entries.len() {
                match self.entries.index(entry) {
                    NodeEntry::Page(p) => {
                        Ok(p.base + offset % self.entry_size())
                    },
                    NodeEntry::Directory(d) => {
                        d.resolve(vaddr)
                    },
                    NodeEntry::Empty() => {
                        Err(())
                    },
                }
            } else {
                Err(())
            }
        } else {
            arbitrary()
        }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_resolve(self, vaddr: nat) {
        if self.inv() && self.base_vaddr <= vaddr && vaddr < self.base_vaddr + self.entry_size() * self.num_entries() {
            self.lemma_derive_entry_bounds_from_if_condition(vaddr);
            assert(self.directories_obey_invariant());
        } else {
        }
    }

    // Proves 'entry < self.entries.len()', given the if condition
    #[proof]
    fn lemma_derive_entry_bounds_from_if_condition(self, vaddr: nat) {
        requires([
                 self.inv(),
                 self.base_vaddr <= vaddr,
                 vaddr < self.base_vaddr + self.entry_size() * self.num_entries(),
        ]);
        ensures({
            let offset = vaddr - self.base_vaddr;
            let base_offset = offset - (offset % self.entry_size());
            let entry = base_offset / self.entry_size();
            entry < self.entries.len()
        });
        let offset = vaddr - self.base_vaddr;
        let base_offset = offset - (offset % self.entry_size());
        let entry: nat = base_offset / self.entry_size();
        if self.inv() && self.base_vaddr <= vaddr && vaddr < self.base_vaddr + self.entry_size() * self.num_entries() {
            assert_nonlinear_by({
                requires([
                    self.entry_size() > 0,
                    self.num_entries() > 0,
                    base_offset == offset - (offset % self.entry_size()),
                    entry == base_offset / self.entry_size(),
                    offset < self.entry_size() * self.num_entries(),
                ]);
                ensures([
                    base_offset / self.entry_size() < self.num_entries(),
                    entry < self.num_entries(),
                ]);
                crate::lib::mod_less_eq(offset, self.entry_size());
                crate::lib::subtract_mod_aligned(offset, self.entry_size());
            });
        } else {
        }
    }

    #[proof]
    fn lemma_no_dir_interp_aux_mapping_implies_no_self_interp_aux_mapping(self, i: nat, n: nat, vaddr: nat, d: Directory) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i <= n,
                 n < self.num_entries(),
                 self.entries.index(n).is_Directory(),
                 equal(d, self.entries.index(n).get_Directory_0()),
                 d.base_vaddr <= vaddr,
                 vaddr < d.base_vaddr + d.num_entries() * d.entry_size(),
                 forall(|va: nat|
                         #[trigger] d.interp().map.dom().contains(va) >>=
                         (vaddr < va || vaddr >= va + d.interp().map.index(va).size))
        ]);
        ensures(forall(|va: nat|
                       #[trigger] self.interp_aux(i).map.dom().contains(va) >>=
                       (vaddr < va || vaddr >= va + self.interp_aux(i).map.index(va).size)));

        if i >= self.entries.len() {
        } else {
            if i == n {
                assert_forall_by(|va: nat| {
                    requires(self.interp_aux(i).map.dom().contains(va));
                    ensures(vaddr < va || vaddr >= va + #[trigger] self.interp_aux(i).map.index(va).size);

                    self.inv_implies_interp_aux_inv(i+1);
                    assert(self.directories_obey_invariant());
                    d.inv_implies_interp_inv();

                    if d.interp().map.dom().contains(va) {
                    } else {
                        assert(self.interp_aux(i+1).map.dom().contains(va));

                        assert(vaddr < d.base_vaddr + d.num_entries() * d.entry_size());
                        assert(vaddr < self.base_vaddr + i * self.entry_size() + d.num_entries() * d.entry_size());
                        crate::lib::mul_commute(d.entry_size(), d.num_entries());
                        assert(vaddr < self.base_vaddr + i * self.entry_size() + self.entry_size());
                        crate::lib::mul_distributive(i, self.entry_size());
                        assert(vaddr < self.base_vaddr + (i+1) * self.entry_size());
                        assert(vaddr < va);
                    }

                });
            } else {
                self.lemma_no_dir_interp_aux_mapping_implies_no_self_interp_aux_mapping(i+1, n, vaddr, d);
                match self.entries.index(i) {
                    NodeEntry::Page(p)      => {
                        assert_forall_by(|va: nat| {
                            requires(self.interp_aux(i).map.dom().contains(va));
                            ensures(vaddr < va || vaddr >= va + #[trigger] self.interp_aux(i).map.index(va).size);

                            if self.base_vaddr + i * self.entry_size() == va {
                                assert(equal(self.interp_aux(i).map.index(va), p));
                                assert(p.size == self.entry_size());

                                assert(d.base_vaddr <= vaddr);
                                assert(self.base_vaddr + n * self.entry_size() <= vaddr);
                                assert(n >= i + 1);
                                crate::lib::mult_leq_mono1(i+1, n, self.entry_size());
                                assert(self.base_vaddr + (i+1) * self.entry_size() <= vaddr);
                                crate::lib::mul_distributive(i, self.entry_size());
                                assert(self.base_vaddr + i * self.entry_size() + self.entry_size() <= vaddr);
                                assert(self.base_vaddr + i * self.entry_size() + p.size <= vaddr);
                                assert(va + p.size <= vaddr);
                            } else {
                                assert(self.interp_aux(i+1).map.dom().contains(va));
                            }
                        });
                    },
                    NodeEntry::Directory(d2) => {
                        assert(self.directories_obey_invariant());
                        d2.inv_implies_interp_inv();
                        // assert(forall(|va: nat| #[trigger] d2.interp().map.dom().contains(va) >>= va <  d2.base_vaddr + d2.num_entries() * d2.entry_size()));
                        assert_forall_by(|va: nat| {
                            requires(self.interp_aux(i).map.dom().contains(va));
                            ensures(vaddr < va || vaddr >= va + #[trigger] self.interp_aux(i).map.index(va).size);

                            if d2.interp().map.dom().contains(va) {
                                assert(va + d2.interp().map.index(va).size <= d2.base_vaddr + d2.num_entries() * d2.entry_size());
                                assert(d.base_vaddr <= vaddr);
                                assert(self.base_vaddr + n * self.entry_size() <= vaddr);
                                assert(n >= i + 1);
                                crate::lib::mult_leq_mono1(i+1, n, self.entry_size());
                                assert(self.base_vaddr + (i+1) * self.entry_size() <= vaddr);
                                crate::lib::mul_distributive(i, self.entry_size());
                                assert(self.base_vaddr + i * self.entry_size() + self.entry_size() <= vaddr);
                                assert(d2.base_vaddr + self.entry_size() <= vaddr);
                                crate::lib::mul_commute(d2.entry_size(), d2.num_entries());
                                assert(d2.base_vaddr + d2.num_entries() * d2.entry_size() <= vaddr);
                            } else {
                                assert(self.interp_aux(i+1).map.dom().contains(va));
                            }
                        });
                    },
                    NodeEntry::Empty()      => {
                        assert(equal(self.interp_aux(i), self.interp_aux(i+1)));
                    },
                }
            }
        }
    }

    // This lemma is designed to be used with the negated abstract resolve condition, i.e.:
    // assert(!exists(|n:nat| d.interp().map.dom().contains(n) && n <= vaddr && vaddr < n + (#[trigger] d.interp().map.index(n)).size));
    // The forall version in this lemma is just easier to work with. Taking d as an argument is also done to simplify the preconditions.
    #[proof]
    fn lemma_no_dir_interp_mapping_implies_no_self_interp_mapping(self, n: nat, vaddr: nat, d: Directory) {
        requires([
                 self.inv(),
                 n < self.num_entries(),
                 self.entries.index(n).is_Directory(),
                 equal(d, self.entries.index(n).get_Directory_0()),
                 d.base_vaddr <= vaddr,
                 vaddr < d.base_vaddr + d.num_entries() * d.entry_size(),
                 forall(|va: nat|
                         #[trigger] d.interp().map.dom().contains(va) >>=
                         (vaddr < va || vaddr >= va + d.interp().map.index(va).size))
        ]);
        ensures(forall(|va: nat|
                       #[trigger] self.interp().map.dom().contains(va) >>=
                       (vaddr < va || vaddr >= va + self.interp().map.index(va).size)));

        assert(equal(self.entries.index(n).get_Directory_0().interp(), self.entries.index(n).get_Directory_0().interp_aux(0)));

        self.lemma_no_dir_interp_aux_mapping_implies_no_self_interp_aux_mapping(0, n, vaddr, d);
    }

    #[proof]
    fn resolve_refines(self, vaddr: nat) {
        decreases(self.arch.layers.len() - self.layer);
        requires(self.inv());
        ensures(equal(self.interp().resolve(vaddr), self.resolve(vaddr)));

        // self.inv_implies_interp_aux_inv(0);

        if self.base_vaddr <= vaddr && vaddr < self.base_vaddr + self.entry_size() * self.num_entries() {
            let offset = vaddr - self.base_vaddr;
            let base_offset = offset - (offset % self.entry_size());
            let entry = base_offset / self.entry_size();
            self.lemma_derive_entry_bounds_from_if_condition(vaddr);
            let va_base = self.base_vaddr + entry * self.entry_size();
            assert_by(
                true
                && va_base == vaddr - ((vaddr - self.base_vaddr) % self.entry_size())
                && va_base <= vaddr
                && vaddr - va_base == offset % self.entry_size(), {
                crate::lib::subtract_mod_aligned(offset, self.entry_size());
                crate::lib::div_mul_cancel(base_offset, self.entry_size());
                crate::lib::mod_less_eq(offset, self.entry_size());
            });
            match self.entries.index(entry) {
                NodeEntry::Page(p) => {
                    let va_base_offset = vaddr - va_base;

                    self.lemma_interp_facts_page(entry);
                    self.inv_implies_interp_aux_inv(0);
                },
                NodeEntry::Directory(d) => {
                    assert(self.directories_obey_invariant());
                    d.resolve_refines(vaddr);
                    assert(equal(d.interp().resolve(vaddr), d.resolve(vaddr)));

                    if d.resolve(vaddr).is_Ok() {
                        assert(self.resolve(vaddr).is_Ok());
                        assert(exists(|n: nat|
                                        d.interp().map.dom().contains(n) &&
                                        n <= vaddr && vaddr < n + (#[trigger] d.interp().map.index(n)).size));

                        let n1 = choose(|n:nat|
                                        self.interp().map.dom().contains(n) &&
                                        n <= vaddr && vaddr < n + (#[trigger] self.interp().map.index(n)).size);
                        let n2 = choose(|n:nat|
                                        d.interp().map.dom().contains(n) &&
                                        n <= vaddr && vaddr < n + (#[trigger] d.interp().map.index(n)).size);

                        assert(self.entries.index(entry).get_Directory_0().interp().map.contains_pair(n2, d.interp().map.index(n2)));
                        self.lemma_interp_facts_dir(entry, n2, d.interp().map.index(n2));

                        assert_forall_by(|n1: nat, n2: nat| {
                            requires(
                                self.interp().map.dom().contains(n1) &&
                                n1 <= vaddr && vaddr < n1 + (#[trigger] self.interp().map.index(n1)).size &&
                                self.interp().map.dom().contains(n2) &&
                                n2 <= vaddr && vaddr < n2 + (#[trigger] self.interp().map.index(n2)).size);
                            ensures(n1 == n2);
                            self.inv_implies_interp_inv();
                            assert(self.interp().inv());
                        });

                        assert(n1 == n2);
                        let n = n1;
                        assert(self.interp().map.dom().contains(n));
                        assert(d.resolve(vaddr).is_Ok());
                        assert(d.interp().resolve(vaddr).is_Ok());
                        assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
                    } else {
                        assert(d.resolve(vaddr).is_Err());
                        assert(self.resolve(vaddr).is_Err());
                        if self.interp().resolve(vaddr).is_Ok() {
                            assert(exists(|n:nat|
                                          self.interp().map.dom().contains(n) &&
                                          n <= vaddr && vaddr < n + (#[trigger] self.interp().map.index(n)).size));
                            let n = choose(|n:nat|
                                           self.interp().map.dom().contains(n) &&
                                           n <= vaddr && vaddr < n + (#[trigger] self.interp().map.index(n)).size);
                            assert_nonlinear_by({
                                requires([
                                    self.entry_size() == d.entry_size() * d.num_entries(),
                                    self.entry_size() > 0,
                                    offset == vaddr - self.base_vaddr,
                                    base_offset == offset - (offset % self.entry_size()),
                                    entry == base_offset / self.entry_size(),
                                    self.base_vaddr + entry * self.entry_size() == d.base_vaddr,
                                ]);
                                ensures([
                                    vaddr < d.base_vaddr + d.num_entries() * d.entry_size(),
                                ]);
                                crate::lib::subtract_mod_aligned(offset, self.entry_size());
                                assert(aligned(base_offset, self.entry_size()));
                                assert(vaddr < self.base_vaddr + (base_offset + self.entry_size()));
                                crate::lib::mod_add_zero(base_offset, self.entry_size(), self.entry_size());
                                assert(vaddr < self.base_vaddr + ((base_offset + self.entry_size()) / self.entry_size()) * self.entry_size());
                            });

                            self.lemma_no_dir_interp_mapping_implies_no_self_interp_mapping(entry, vaddr, d);
                            assert(self.interp().map.dom().contains(n) && n <= vaddr && vaddr < n + self.interp().map.index(n).size);
                        }
                        assert(self.interp().resolve(vaddr).is_Err());
                        assert(d.interp().resolve(vaddr).is_Err());
                        assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));
                    }
                    assert(equal(d.interp().resolve(vaddr), self.interp().resolve(vaddr)));

                },
                NodeEntry::Empty() => {
                    assert(self.resolve(vaddr).is_Err());

                    assert_forall_by(|n: nat| {
                        requires(#[trigger] self.interp().map.dom().contains(n) && n <= vaddr && vaddr < n + self.interp().map.index(n).size);
                        ensures(false);

                        self.lemma_interp_facts_empty(entry);
                        assert((n + self.interp().map.index(n).size <= self.base_vaddr + entry * self.entry_size())
                               || (self.base_vaddr + (entry+1) * self.entry_size() <= n));
                        if n + self.interp().map.index(n).size <= self.base_vaddr + entry * self.entry_size() {
                        } else {
                            self.inv_implies_interp_inv();
                            assert_nonlinear_by({
                                requires([
                                    self.entry_size() > 0,
                                    offset == vaddr - self.base_vaddr,
                                    base_offset == offset - (offset % self.entry_size()),
                                    entry == base_offset / self.entry_size(),
                                ]);
                                ensures([
                                    vaddr < self.base_vaddr + (entry + 1) * self.entry_size(),
                                ]);
                                crate::lib::subtract_mod_aligned(offset, self.entry_size());
                                assert(vaddr < self.base_vaddr + (base_offset + self.entry_size()));
                                crate::lib::mod_add_zero(base_offset, self.entry_size(), self.entry_size());
                                assert(vaddr < self.base_vaddr + ((base_offset + self.entry_size()) / self.entry_size()) * self.entry_size());
                            });
                        }
                    });
                    assert(self.interp().resolve(vaddr).is_Err());
                },
            }
        } else {
            assert(self.resolve(vaddr).is_Err());

            self.inv_implies_interp_inv();
            if vaddr >= self.base_vaddr + self.entry_size() * self.num_entries() {
                assert(forall(|va: nat| self.interp().map.dom().contains(va)
                              >>= va + #[trigger] self.interp().map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size()));
                assert(self.base_vaddr <= vaddr);
                if self.interp().resolve(vaddr).is_Ok() {
                    assert(exists(|n: nat| #[trigger] self.interp().map.dom().contains(n) && n <= vaddr && vaddr < n + self.interp().map.index(n).size));
                    let va = choose(|n: nat| #[trigger] self.interp().map.dom().contains(n) && n <= vaddr && vaddr < n + self.interp().map.index(n).size);
                    assert(va + self.interp().map.index(va).size <= self.base_vaddr + self.num_entries() * self.entry_size());
                    assert(false);
                }
            } else {
            }
            assert(self.interp().resolve(vaddr).is_Err());
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
    pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        self.interp().accepted_mapping(base, frame)
    }

    #[spec]
    pub fn map_frame(self, base: nat, frame: MemRegion) -> Result<Self,()> {
        decreases(self.arch.layers.len() - self.layer);
        decreases_by(Self::check_map_frame);

        if self.inv() && self.accepted_mapping(base, frame) {
            let offset = base - self.base_vaddr;
            let base_offset = offset - (offset % self.entry_size());
            let entry = base_offset / self.entry_size();
            if self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
                // this condition implies that "entry < self.entries.len()"
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
                                base_vaddr: self.base_vaddr + offset,
                                arch:       self.arch,
                            }.map_frame(base, frame);
                                // FIXME: am i certain this mapping will always be ok? might be
                                // tricky to prove.
                            Ok(self.update(entry, NodeEntry::Directory(new_dir.get_Ok_0())))
                        }
                    },
                }
            } else {
                Err(())
            }
        } else {
            arbitrary()
        }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_map_frame(self, base: nat, frame: MemRegion) {
        if self.inv() && self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
            self.lemma_derive_entry_bounds_from_if_condition(base);
            assert(self.directories_obey_invariant());
        } else {
        }
    }

    #[spec(checked)]
    pub fn unmap(self, base: nat) -> Result<Self,()> {
        decreases(self.arch.layers.len() - self.layer);
        decreases_by(Self::check_unmap);

        if self.inv() {
            let offset = base - self.base_vaddr;
            let base_offset = offset - (offset % self.entry_size());
            let entry = base_offset / self.entry_size();
            if self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
                // this condition implies that "entry < self.entries.len()"
                match self.entries.index(entry) {
                    NodeEntry::Page(p)      => {
                        if aligned(base, self.entry_size()) {
                            // This implies base == self.base_vaddr + entry * self.entry_size()
                            Ok(self.update(entry, NodeEntry::Empty()))
                        } else {
                            // This implies base > self.base_vaddr + entry * self.entry_size()
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
                    NodeEntry::Empty()      => Err(()),
                }
            } else {
                Err(())
            }
        } else {
            arbitrary()
        }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_unmap(self, base: nat) {
        if self.inv() && self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
            self.lemma_derive_entry_bounds_from_if_condition(base);
            assert(self.directories_obey_invariant());
        } else {
        }
    }

    // This is only proved for NodeEntry::Empty() because we'd have to have more requirements on
    // pages and directories to ensure the invariant remains intact. Otherwise interp_aux is
    // arbitrary.
    #[proof]
    fn lemma_update_leq_interp_aux_idempotent(self, i: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
        ]);
        ensures(forall(|n: nat| n < i && n < self.entries.len() >>= equal((#[trigger] self.update(n, NodeEntry::Empty())).interp_aux(i), self.interp_aux(i))));

        assert_forall_by(|n: nat| {
            requires(n < i && n < self.entries.len());
            ensures(equal((#[trigger] self.update(n, NodeEntry::Empty())).interp_aux(i), self.interp_aux(i)));

            assume(self.update(n, NodeEntry::Empty()).inv());
            if i >= self.entries.len() {
            } else {
                self.lemma_update_leq_interp_aux_idempotent(i+1);
            }
        });
    }

    #[proof]
    fn lemma_update_empty_interp_aux_equal_interp_aux_remove(self, i: nat, n: nat) {
        decreases((self.arch.layers.len() - self.layer, self.num_entries() - i));
        requires([
                 self.inv(),
                 i <= n,
                 n < self.entries.len(),
                 self.entries.index(n).is_Page(),
        ]);
        ensures(equal(self.update(n, NodeEntry::Empty()).interp_aux(i), self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));

        let n_vaddr = self.base_vaddr + n * self.entry_size();
        let p = self.entries.index(n).get_Page_0();
        assert_by(self.interp_aux(i).map.dom().contains(n_vaddr), {
                self.lemma_interp_aux_facts_page(i, n);
        });
        self.inv_implies_interp_inv();
        self.inv_implies_interp_aux_inv(i+1);
        crate::lib::mul_distributive(i, self.entry_size());

        let updi = self.update(n, NodeEntry::Empty());
        assume(updi.inv());
        if i >= self.entries.len() {
        } else {
            if i == n {
                assert(equal(updi.interp_aux(i), updi.interp_aux(i+1)));
                assert(!self.interp_aux(i+1).map.dom().contains(n_vaddr));
                assert_maps_equal!(self.interp_aux(i).remove(n_vaddr).map, self.interp_aux(i+1).map);
                assert(equal(self.interp_aux(i).remove(n_vaddr), self.interp_aux(i+1)));
                if i+1 < self.entries.len() {
                    self.lemma_update_leq_interp_aux_idempotent(i+1);
                } else {
                }
                assert(equal(updi.interp_aux(i), self.interp_aux(i).remove(n_vaddr)));
            } else {
                assert(i < n);
                self.lemma_update_empty_interp_aux_equal_interp_aux_remove(i+1, n);
                assert(equal(
                        updi.interp_aux(i+1),
                        self.interp_aux(i+1).remove(self.base_vaddr + n * self.entry_size())));
                self.lemma_interp_aux_disjoint(i);
                let rem = self.interp_aux(i + 1).map;
                match self.entries.index(i) {
                    NodeEntry::Page(p)      => {
                        assert(equal(self.interp_aux(i).map, rem.insert(self.base_vaddr + i * self.entry_size(), p)));
                        assert(equal(updi.entries.index(i), self.entries.index(i)));
                        assume(false);
                        // assert(equal(
                        //         self.update(n, NodeEntry::Empty()).interp_aux(i).map,
                        //         self.update(n, NodeEntry::Empty()).interp_aux(i+1).map.insert(self.base_vaddr + i * self.entry_size(), p)));
                        // assert(equal(self.update(n, NodeEntry::Empty()).interp_aux(i), self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));

                        //rem.insert(self.base_vaddr + i * self.entry_size(), p),
                        // assert(equal(
                        //         self.update(n, NodeEntry::Empty()).interp_aux(i),
                        //         self.interp_aux(i).remove(self.base_vaddr + n * self.entry_size())));
                    },
                    NodeEntry::Directory(d) => {
                        assume(false);
                        //rem.union_prefer_right(d.interp_aux(0).map),
                    },
                    NodeEntry::Empty()      => (),
                }
            }
        }
    }

    #[proof]
    fn lemma_update_empty_interp_equal_interp_remove(self, n: nat) {
        requires(self.entries.index(n).is_Page());
        ensures(equal(self.update(n, NodeEntry::Empty()).interp(), self.interp().remove(self.base_vaddr + n * self.entry_size())));
        assume(false);
    }

    #[proof]
    fn lemma_derive_unmap_page_base_bound(self, base: nat) {
        requires([
                 self.inv(),
                 self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries(),
                 { let offset = base - self.base_vaddr;
                   let base_offset = offset - (offset % self.entry_size());
                   let entry = base_offset / self.entry_size();
                   self.entries.index(entry).is_Page()
                 },
        ]);
        ensures({
            let offset = base - self.base_vaddr;
            let base_offset = offset - (offset % self.entry_size());
            let entry = base_offset / self.entry_size();
            if aligned(base, self.entry_size()) {
                base == self.base_vaddr + entry * self.entry_size()
            } else {
                base > self.base_vaddr + entry * self.entry_size()
            }
        });
        let offset = base - self.base_vaddr;
        let base_offset = offset - (offset % self.entry_size());
        let entry = base_offset / self.entry_size();
        if aligned(base, self.entry_size()) {
            assert_by(base == self.base_vaddr + entry * self.entry_size(), {
                crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
                crate::lib::subtract_mod_eq_zero(self.base_vaddr, base, self.entry_size());
                crate::lib::div_mul_cancel(base_offset, self.entry_size());
            });
        } else {
            assert_nonlinear_by({
                requires([
                    self.entry_size() > 0,
                    base % self.entry_size() > 0,
                    self.base_vaddr % (self.entry_size() * self.num_entries()) == 0,
                    self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries(),
                    offset == base - self.base_vaddr,
                    base_offset == offset - (offset % self.entry_size()),
                    entry == base_offset / self.entry_size(),
                ]);
                ensures([
                    base > self.base_vaddr + entry * self.entry_size(),
                ]);

                crate::lib::mod_mult_zero_implies_mod_zero(self.base_vaddr, self.entry_size(), self.num_entries());
                crate::lib::multiple_offsed_mod_gt_0(base, self.base_vaddr, self.entry_size());
                crate::lib::mod_less_eq(base, self.entry_size());
                crate::lib::mod_less_eq(offset, self.entry_size());
                crate::lib::subtract_mod_aligned(offset, self.entry_size());
            });
        }
    }

    #[proof]
    fn unmap_preserves_inv(self, base: nat) {
        requires([
                 self.inv(),
                 self.unmap(base).is_Ok()
        ]);
        ensures(self.unmap(base).get_Ok_0().inv());
        decreases(self.arch.layers.len() - self.layer);

        let offset = base - self.base_vaddr;
        let base_offset = offset - (offset % self.entry_size());
        let entry = base_offset / self.entry_size();
        if self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
            self.lemma_derive_entry_bounds_from_if_condition(base);
            match self.entries.index(entry) {
                NodeEntry::Page(p)      => {
                    self.lemma_derive_unmap_page_base_bound(base);
                    if aligned(base, self.entry_size()) {
                        let nself = self.update(entry, NodeEntry::Empty());
                        assert(self.directories_obey_invariant());
                        assert(nself.directories_obey_invariant());
                        assert(nself.inv());
                    } else {
                    }
                },
                NodeEntry::Directory(d) => {
                    assert(self.directories_obey_invariant());
                    d.unmap_preserves_inv(base);
                    let nself = self.unmap(base).get_Ok_0();
                    assert(nself.directories_obey_invariant());
                },
                NodeEntry::Empty()      => (),
            }
        } else {
        }
    }

    #[proof]
    fn unmap_refines_unmap(self, base: nat) {
        requires(self.inv());
        ensures(equal(self.unmap(base).map_ok(|d| d.interp()), self.interp().unmap(base)));

        self.inv_implies_interp_inv();
        crate::lib::mul_commute(self.entry_size(), self.num_entries());

        let offset = base - self.base_vaddr;
        let base_offset = offset - (offset % self.entry_size());
        let entry = base_offset / self.entry_size();
        if self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries() {
            self.lemma_derive_entry_bounds_from_if_condition(base);
            match self.entries.index(entry) {
                NodeEntry::Page(p) => {
                    self.lemma_derive_unmap_page_base_bound(base);
                    if aligned(base, self.entry_size()) {
                        assert(base == self.base_vaddr + entry * self.entry_size());
                        self.lemma_interp_facts_page(entry);
                        self.unmap_preserves_inv(base);
                        self.lemma_update_empty_interp_equal_interp_remove(entry);
                        assert(equal(self.update(entry, NodeEntry::Empty()).interp(), self.interp().remove(base)));
                    } else {
                        assert(self.unmap(base).is_Err());
                        self.lemma_interp_facts_page(entry);
                        assert(self.interp().map.contains_pair(self.base_vaddr + entry * self.entry_size(), p));
                        assert(self.interp().map.dom().contains(self.base_vaddr + entry * self.entry_size()));
                        assert(base > self.base_vaddr + entry * self.entry_size());
                        assert_by(!self.interp().map.dom().contains(base), {
                            if self.interp().map.dom().contains(base) {
                                let p2 = self.interp().map.index(base);
                                assert(base > self.base_vaddr + entry * self.entry_size());

                                assert(base < self.base_vaddr + base_offset + self.entry_size());
                                crate::lib::subtract_mod_aligned(offset, self.entry_size());
                                // TODO: nonlinear
                                assume((base_offset + self.entry_size()) % self.entry_size() == 0);
                                crate::lib::div_mul_cancel(base_offset+self.entry_size(), self.entry_size());
                                assert(base < self.base_vaddr + (base_offset+self.entry_size()) / self.entry_size() * self.entry_size());
                                // TODO: nonlinear
                                assume(base < self.base_vaddr + (base_offset / self.entry_size()+1) * self.entry_size());
                                assert(base < self.base_vaddr + (entry+1) * self.entry_size());
                                crate::lib::mul_distributive(entry, self.entry_size());
                                assert(base < self.base_vaddr + entry * self.entry_size() + self.entry_size());
                                assert(base < self.base_vaddr + entry * self.entry_size() + p.size);
                                assert(overlap(
                                        MemRegion { base: base, size: p2.size },
                                        MemRegion { base: self.base_vaddr + entry * self.entry_size(), size: p.size }
                                        ));
                            }
                        });
                        assert(self.interp().unmap(base).is_Err());
                    }
                },
                NodeEntry::Directory(d) => {
                    assume(false);
                    // d.unmap(base),
                },
                NodeEntry::Empty() => {
                    self.lemma_interp_facts_empty(entry);
                    if self.interp().map.dom().contains(entry) {
                        assume(false);
                    } else {
                        assume(false);
                    }
                },
            }
        } else {
            self.lemma_not_contains_from_if_condition(base);
        }
    }

    #[proof]
    fn lemma_not_contains_from_if_condition(self, base: nat) {
        requires([
                 self.inv(),
                 !(self.base_vaddr <= base && base < self.base_vaddr + self.entry_size() * self.num_entries()),
        ]);
        ensures(!self.interp().map.dom().contains(base));
        self.inv_implies_interp_inv();
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
