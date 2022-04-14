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
use crate::{seq, seq_insert_rec, map, map_insert_rec};
use result::{*, Result::*};

pub struct MemRegion { pub base: nat, pub size: nat }

// TODO use VAddr, PAddr

#[spec]
pub fn strictly_decreasing(s: Seq<nat>) -> bool {
    forall(|i: nat, j: nat| i < j && j < s.len() >>= s.index(i) > s.index(j))
}

// Root [8, 16, 24]

#[spec]
pub struct Arch {
    /// Size of each entry at this layer
    pub layer_sizes: Seq<nat>, // 1 GiB, 2 MiB, 4 KiB
}

impl Arch {
    #[spec]
    pub fn inv(&self) -> bool {
        strictly_decreasing(self.layer_sizes)
    }
}

#[proof]
pub struct PageTableContents {
    pub map: Map<nat /* VAddr */, MemRegion>,
    pub arch: Arch,
}

#[spec]
pub fn base_page_aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

// TODO: overlap probably shouldn't be defined in terms of MemRegion, since it's never actually
// used that way. We always check overlap of the virtual address space.
#[spec]
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
    #[spec]
    pub fn ext_equal(self, pt2: PageTableContents) -> bool {
        self.map.ext_equal(pt2.map)
    }

    #[spec]
    pub fn inv(&self) -> bool {
        true
        && self.arch.inv()
        && forall(|va: nat| with_triggers!([self.map.index(va).size],[self.map.index(va).base] => self.map.dom().contains(va) >>=
                  (base_page_aligned(va, self.map.index(va).size)
                   && base_page_aligned(self.map.index(va).base, self.map.index(va).size))))
        && forall(|b1: nat, b2: nat|
        // TODO: let vregion1, vregion2
            (self.map.dom().contains(b1) && self.map.dom().contains(b2)) >>= ((b1 == b2) || !overlap(
                MemRegion { base: b1, size: self.map.index(b1).size },
                MemRegion { base: b2, size: self.map.index(b2).size }
            )))
    }

    #[spec] pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && base_page_aligned(base, frame.size)
        && base_page_aligned(frame.base, frame.size)
        && self.arch.layer_sizes.contains(frame.size)
    }

    #[spec] pub fn valid_mapping(self, base: nat, frame: MemRegion) -> bool {
        forall(|b: nat| #[auto_trigger] self.map.dom().contains(b) >>= !overlap(
                MemRegion { base: base, size: frame.size },
                MemRegion { base: b, size: self.map.index(b).size }
                ))
    }

    /// Maps the given `frame` at `base` in the address space
    #[spec] pub fn map_frame(self, base: nat, frame: MemRegion) -> Result<PageTableContents,()> {
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
    #[proof] fn map_frame_maps_valid(#[spec] self, base: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
            self.valid_mapping(base, frame),
        ]);
        ensures([
            self.map_frame(base, frame).is_Ok(),
        ]);
    }

    #[proof] fn map_frame_preserves_inv(#[spec] self, base: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
            self.map_frame(base, frame).is_Ok(),
        ]);
        ensures([
            self.map_frame(base, frame).get_Ok_0().inv(),
        ]);
    }

    #[proof]
    pub fn lemma_overlap_IMP_equal_base(self, va1: nat, base: nat, size: nat) {
        requires([
                 self.inv(),
                 self.map.dom().contains(va1),
                 base_page_aligned(base, size),
                 size == self.map.index(va1).size,
                 size > 0, // TODO: this should probably be self.arch.layer_sizes.contains(size), along with 0 not being a valid size in the invariant
                 overlap(
                     MemRegion { base: va1, size: self.map.index(va1).size },
                     MemRegion { base: base, size: size }),
        ]);
        ensures(va1 == base);

        if va1 <= base {
            // assert(va1 + va1_size <= base);
            if va1 < base {
                assert(va1 < base);
                assert(base < va1 + size);
                assert(base % size == 0);
                assert(va1 % size == 0);
                // TODO: same as below
                assume(false);
                assert(va1 == base);
            } else { }
        } else {
            assert(base < va1);
            assert(va1 < base + size);
            assert(va1 % size == 0);
            assert(base % size == 0);
            // assert(va1 % size == va1 - base);

            // base    size
            // |-------|
            //     |-------|
            //     va1     size
            // TODO: need nonlinear reasoning? (isabelle sledgehammer can prove this)
            assume(false);
            assert(va1 == base);
        }
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
    #[spec] fn resolve(self, vaddr: nat) -> nat {
        if exists(|n:nat|
                  self.map.dom().contains(n) &&
                  n <= vaddr && vaddr < n + (#[trigger] self.map.index(n)).size) {
            let n = choose(|n:nat|
                           self.map.dom().contains(n) &&
                           n <= vaddr && vaddr < n + (#[trigger] self.map.index(n)).size);
            let offset = vaddr - n;
            self.map.index(n).base + offset
        } else {
            arbitrary()
        }
    }

    /// Removes the frame from the address space that contains `base`.
    #[spec] fn unmap(self, base: nat) -> PageTableContents {
        if self.map.dom().contains(base) {
            PageTableContents {
                map: self.map.remove(base),
                ..self
            }
        } else {
            arbitrary()
        }
    }

    #[proof] fn unmap_preserves_inv(self, base: nat) {
        requires([
            self.inv(),
            self.map.dom().contains(base),
        ]);
        ensures([
            self.unmap(base).inv()
        ]);
    }
}



// Second refinement layer

#[proof] #[is_variant]
pub enum NodeEntry {
    Directory(PrefixTreeNode),
    Page(MemRegion),
}

#[proof]
pub struct PrefixTreeNode {
    pub map: Map<nat /* addr */, Box<NodeEntry>>, // consider using the entry index
    pub layer: nat,       // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
    pub interp_map: Map<nat, MemRegion>,
}

// page_size, next_sizes
// 2**40    , [ 2 ** 30, 2 ** 20 ]
// 2**30    , [ 2 ** 20 ]
// 2**20    , [ ]

fndecl!(pub fn pow2(v: nat) -> nat);


impl PrefixTreeNode {
    #[spec]
    pub fn entry_size(&self) -> nat {
        self.arch.layer_sizes.index(self.layer as int + 1)
    }

    #[spec]
    pub fn layer_size(&self) -> nat {
        self.arch.layer_sizes.index(self.layer as int)
    }

    #[spec]
    pub fn entries_are_entry_size_aligned(&self) -> bool {
        forall(|offset: nat| #[auto_trigger] self.map.dom().contains(offset) >>= base_page_aligned(offset, self.entry_size()))
    }

    #[spec]
    pub fn entries_fit_in_layer_size(&self) -> bool {
        forall(|offset: nat| self.map.dom().contains(offset) >>= offset < self.layer_size())
    }

    #[spec]
    pub fn pages_match_entry_size(&self) -> bool {
        forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Page())
               >>= (#[trigger] self.map.index(offset)).get_Page_0().size == self.entry_size())
    }

    #[spec]
    pub fn directories_are_in_next_layer(&self) -> bool {
        forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Directory())
               >>= {
                    let directory = (#[trigger] self.map.index(offset)).get_Directory_0();
                    true
                    && directory.layer == self.layer + 1
                    && directory.base_vaddr == self.base_vaddr + offset
                })
    }

    #[spec]
    pub fn directories_obey_invariant(&self) -> bool {
        decreases((self.arch.layer_sizes.len() - self.layer, 0));

        if self.layer < self.arch.layer_sizes.len() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Directory())
                   >>= (#[trigger] self.map.index(offset)).get_Directory_0().inv())
        } else {
            arbitrary()
        }
    }

    #[spec]
    pub fn directories_match_arch(&self) -> bool {
        forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Directory())
               >>= equal((#[trigger] self.map.index(offset)).get_Directory_0().arch, self.arch))
    }

    #[spec]
    pub fn inv(&self) -> bool {
        decreases((self.arch.layer_sizes.len() - self.layer, 1));

        true
        && self.interp().inv()

        && self.map.dom().finite()
        && self.layer < self.arch.layer_sizes.len()
        && self.entries_are_entry_size_aligned()
        && self.entries_fit_in_layer_size()
        && self.pages_match_entry_size()
        && self.directories_are_in_next_layer()
        && self.directories_obey_invariant()
        && self.directories_match_arch()

        && equal(self.interp_map, self.interp().map)
    }

    // #[spec]
    // pub fn termination_test(self) {
    //     decreases(self);

    //     if self.inv() && self.arch.inv() {
    //         if self.map.dom().len() == 0 {
    //             ()
    //         } else {
    //             let k = self.map.dom().choose();
    //             if self.map.index(k).is_Directory() {
    //                 self.map.index(k).get_Directory_0().termination_test()
    //             } else {
    //                 ()
    //             }
    //         }
    //     } else {
    //         ()
    //     }
    // }

    #[spec]
    pub fn interp_pre(self, start: nat) -> bool {
        self.map.dom().finite()
    }

    #[spec]
    pub fn interp(self) -> PageTableContents {
        self.interp_aux(0)
    }
    #[spec]
    pub fn interp_aux(self, start: nat) -> PageTableContents {
        decreases((self, self.layer_size() - start));
        decreases_by(Self::check_interp_aux);

        if self.interp_pre(start) {
            if start >= self.layer_size() {
                PageTableContents {
                    map: map![],
                    arch: self.arch,
                }
            } else { // start < self.layer_size()
                let rem = self.interp_aux(start+1).map;
                PageTableContents {
                    map: match *self.map.index(start) {
                        NodeEntry::Page(p)      => rem.union_prefer_right(map![self.base_vaddr + start => p]),
                        NodeEntry::Directory(d) => rem.union_prefer_right(d.interp_aux(0).map),
                    },
                    arch: self.arch,
                }
            }
        } else {
            arbitrary()
        }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_interp_aux(self, start: nat) {
        requires(self.interp_pre(start));
        if start >= self.layer_size() {
        } else {
            let x = self.map.dom().choose();
            if let NodeEntry::Directory(d) = *self.map.index(x) {
            }
            // TODO
            assume(false);
        }
    }

    // pub fn valid_index_lemmas() {
    //     ensures([forall(|ptn: PrefixTreeNode, i: Seq<nat>|
    //             ...
    //     ]);
    // }

    // #[spec]
    // pub fn valid_index(self, i: Seq<nat>) -> bool {
    //     decreases(i.len());

    //     if i.len() == 0 {
    //         false
    //     } else {
    //         if i.len() == 1 {
    //             self.map.dom().contains(i.index(0)) && self.map.index(i.index(0)).is_Page()
    //         } else {
    //             if self.map.dom().contains(i.index(0)) {
    //                 match *self.map.index(i.index(0)) {
    //                     NodeEntry::Directory(d) => d.valid_index(i.subrange(1,i.len())),
    //                     NodeEntry::Page(_)      => false,
    //                 }
    //             } else {
    //                 false
    //             }
    //         }
    //     }
    // }

    // #[proof]
    // pub fn lemma_valid_index_is_nonempty(self, i: Seq<nat>) {
    //     requires(self.valid_index(i));
    //     ensures(i.len() > 0);
    // }

    // #[proof]
    // pub fn lemma(self, i: Seq<nat>) {
    //     requires(self.valid_index(i));
    //     ensures(self.interp().map.dom().contains(self.base_vaddr + i.index(0))); // TODO: it's actually the sum of the indices. maybe too complicated.
    // }

    // #[proof]
    // pub fn lemma_interp_dom_contains(self, a: nat) {
    //     requires([
    //              self.map.dom().finite(),
    //              self.map.dom().contains(a),
    //              self.map.index(a).is_Page(),
    //     ]);
    //     ensures(self.interp().map.dom().contains(self.base_vaddr + a));

    //     let s = self.map.dom();

    //     lemma_set_contains_IMP_len_greater_zero::<nat>(s, a);
    //     assert(s.len() != 0);

    //     let x = self.map.dom().choose();
    //     match *self.map.index(x) {
    //         NodeEntry::Page(p) => {
    //             if x == a {
    //                 assert(map![self.base_vaddr + x => p].dom().contains(self.base_vaddr + x));
    //             }
    //         },
    //         NodeEntry::Directory(d) => { }
    //     }
    //     let rem = PrefixTreeNode {
    //         map: self.map.remove(x),
    //         ..self
    //     };
    //     if x == a {
    //     } else {
    //         // TODO: the arg needs to be something like a % rem.entry_size()
    //         // rem.lemma_interp_dom_contains(a);
    //     }
    // }

    // #[spec]
    // pub fn interp_fold(self, acc: Map<nat, MemRegion>, rest: Map<nat, Box<NodeEntry>>) -> Map<nat, MemRegion> {
    //     decreases((acc.dom().len(), 0));

    //     if acc.dom().finite() && rest.dom().finite() {
    //         if rest.dom().len() > 0 {
    //             let x = rest.dom().choose();
    //             match *self.map.index(x) {
    //                  NodeEntry::Page(p) =>
    //                      self.interp_fold(acc.union_prefer_right(map![self.base_vaddr + x => p]), self.map.remove(x)),
    //                  NodeEntry::Directory(d) =>
    //                      self.interp_fold(acc.union_prefer_right(d.interp().map), self.map.remove(x)),
    //             }
    //         } else {
    //             acc
    //         }
    //     } else {
    //         arbitrary()
    //     }
    // }

    // #[spec]
    // pub fn interp(self) -> PageTableContents {
    //     decreases((self, 1));

    //     PageTableContents {
    //         map: self.interp_fold(map![], self.map)
    //     }
    // }

    #[spec] pub fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && self.interp().accepted_mapping(base, frame)
    }

    // // sanity check lemma
    // #[proof]
    // pub fn lemma_valid_map_frame_is_ok(self, vaddr: nat, frame: MemRegion) {
    //     requires([
    //              self.inv(),
    //              self.accepted_mapping(vaddr, frame),
    //              self.valid_mapping(vaddr, frame),
    //     ]);
    //     ensures(self.map_frame(vaddr, frame).is_Ok());
    // }

    #[spec]
    pub fn map_frame(self, vaddr: nat, frame: MemRegion) -> Result<PrefixTreeNode,()> {
        decreases(self.arch.layer_sizes.len() - self.layer);

        if self.inv() && self.accepted_mapping(vaddr, frame) {
            let offset = vaddr - self.base_vaddr;
            if frame.size == self.entry_size() {
                if self.map.dom().contains(offset) {
                    Err(())
                } else {
                    Ok(PrefixTreeNode {
                        map: self.map.insert(offset, box NodeEntry::Page(frame)),
                        interp_map: self.interp_map.insert(self.base_vaddr + offset, frame),
                        ..self
                    })
                }
            } else {
                let binding_offset = offset - (offset % self.entry_size()); // 0xf374 -- entry_size 0x100 --> 0xf300
                if self.map.dom().contains(offset) {
                    match *self.map.index(binding_offset) {
                        NodeEntry::Page(_)      => Err(()),
                        NodeEntry::Directory(d) =>
                            match d.map_frame(vaddr, frame) {
                                Ok(upd_d) =>
                                    Ok(PrefixTreeNode {
                                        map: self.map.insert(binding_offset, box NodeEntry::Directory(upd_d)),
                                        interp_map: self.interp_map.insert(self.base_vaddr + offset, frame),
                                        ..self
                                    }),
                                Err(e) => Err(e),
                            }
                    }
                } else {
                    let d =
                        PrefixTreeNode {
                            map: map![],
                            layer: self.layer + 1,
                            base_vaddr: self.base_vaddr + binding_offset,
                            arch: self.arch,
                            interp_map: map![],
                        };

                    // TODO: can we get ? syntax for results?
                    // use map_ok
                    match d.map_frame(vaddr, frame) {
                        Ok(upd_d) =>
                            Ok(PrefixTreeNode {
                                map: self.map.insert(binding_offset, box NodeEntry::Directory(upd_d)),
                                interp_map: self.interp_map.insert(self.base_vaddr + offset, frame),
                                ..self
                            }),
                        Err(e) => Err(e),
                    }
                }
            }
        } else {
            arbitrary()
        }
    }

    #[proof] fn map_frame_maintains_interp_map_correspondence(#[spec] self, vaddr: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(vaddr, frame),
            self.map_frame(vaddr, frame).is_Ok(),
        ]);
        ensures([
            equal(self.map_frame(vaddr, frame).get_Ok_0().interp_map, self.map_frame(vaddr, frame).get_Ok_0().interp().map)
        ]);

        let res = self.map_frame(vaddr, frame).get_Ok_0();

        let offset = vaddr - self.base_vaddr;
        if frame.size == self.entry_size() {
            if self.map.dom().contains(offset) {
            } else {
                assert(equal(res.map, self.map.insert(offset, box NodeEntry::Page(frame))));
                assert(equal(res.interp_map, res.interp().map));
                assume(false);
                // Ok(PrefixTreeNode {
                //     map: self.map.insert(offset, box NodeEntry::Page(frame)),
                //     interp_map: self.interp_map.insert(offset, frame),
                //     ..self
                // })
            }
        } else {
            assume(false);
            let binding_offset = offset - (offset % self.entry_size()); // 0xf374 -- entry_size 0x100 --> 0xf300
            if self.map.dom().contains(offset) {
                assume(false);
            } else {
                assume(false);
            }
        }
    }

    // TODO: maybe we should wait with this proof until we know for sure what interp looks like?
    // Given a PrefixTreeNode:
    //
    // +------+ ----> +------+
    // |      |/      |      |
    // +------+       +------+
    // | dir  |       | page |
    // +------+       +------+
    // |      |\      |      |
    // +------+ ----> +------+
    // |      |
    // +------+
    //
    // Then in any of its directories we have the two bounds shown by the arrows:
    // - Upper arrow: dir.base_vaddr <= page.base
    // - Lower arrow: page.base + page.size <= dir.base_vaddr + self.entry_size()
    // (including for pages in nested directories)
    #[proof]
    pub fn lemma_pages_obey_boundaries(self) {
        requires([
                 self.inv(),
        ]);
        ensures(forall(|d: nat, b: nat|
                       self.map.dom().contains(d) && self.map.index(d).is_Directory() &&
                       self.map.index(d).get_Directory_0().interp().map.dom().contains(b) >>= {
                           let dir = self.map.index(d).get_Directory_0();
                           let MemRegion { base, size } = dir.interp().map.index(b);
                           dir.base_vaddr <= base && base + size <= dir.base_vaddr + self.entry_size()
                       }));
        assume(false);
    }

    #[proof]
    fn map_frame_ok_refines(self, vaddr: nat, frame: MemRegion) {
        requires([
                 self.inv(),
                 self.accepted_mapping(vaddr, frame),
                 // equal(self.layer, 0)
        ]);
        ensures([
                self.interp().map_frame(vaddr, frame).is_Ok() == self.map_frame(vaddr, frame).is_Ok(),
                equal(self.map_frame(vaddr, frame).get_Ok_0().interp(), self.interp().map_frame(vaddr, frame).get_Ok_0())
        ]);

        let offset = vaddr - self.base_vaddr;
        if frame.size == self.entry_size() {
            if self.map.dom().contains(offset) {
                // assert(!self.map_frame(vaddr, frame).is_Ok());
                // assert(self.interp().map_frame(vaddr, frame).is_Ok() == self.map_frame(vaddr, frame).is_Ok());
                // assert(equal(self.map_frame(vaddr, frame).get_Ok_0().interp(), self.interp().map_frame(vaddr, frame).get_Ok_0()));
                assume(false);
            } else {
                assert(self.map_frame(vaddr, frame).is_Ok());
                // assert(forall(|o:nat,n:PrefixTreeNode|
                //               o < vaddr &&
                //               self.map.contains(o,n) && n.is_Page()
                //                   >>= o + self.entry_size() <= vaddr));

                if !self.interp().valid_mapping(vaddr, frame) {
                    assert(exists(|b: nat| #[auto_trigger] self.interp().map.dom().contains(b) && overlap(
                            MemRegion { base: vaddr, size: frame.size },
                            MemRegion { base: b,     size: self.interp().map.index(b).size }
                            )));
                    let b = choose(|b: nat| #[auto_trigger] self.interp().map.dom().contains(b) && overlap(
                            MemRegion { base: vaddr, size: frame.size },
                            MemRegion { base: b,     size: self.interp().map.index(b).size }
                            ));
                    let MemRegion { base, size } = self.interp().map.index(b);
                    self.lemma_pages_obey_boundaries();
                    assume(self.interp().map.dom().contains(vaddr));
                    // self.interp().lemma_overlap_IMP_equal_base(b, vaddr, frame.size);
                    // assert(b == vaddr);
                    // assume(self.map.dom().contains(b));
                    assume(false);

                    // assume(forall(|d: nat, b: nat|
                    //               self.map.dom().contains(d) && self.map.index(d).is_Directory() &&
                    //     self.map.index(d).get_Directory_0().interp().map.dom().contains(b) >>= {
                    //         let dir = self.map.index(d).get_Directory_0();
                    //         let MemRegion { base, size } = #[trigger] dir.interp().map.index(b);
                    //         dir.base_vaddr <= base && base + size <= dir.base_vaddr + self.entry_size()
                    //     }));
                    // assert(self.map.dom().contains(b) && overlap(
                    //         MemRegion { base: vaddr, size: frame.size },
                    //         MemRegion { base: b, size: self.map.index(b).size }
                    //         ));
                    assert(false);
                }
                // suppose overlapping mapping exists
                //
                assert(self.interp().valid_mapping(vaddr, frame));
                assert(self.interp().map_frame(vaddr, frame).is_Ok());
                assert(self.interp().map_frame(vaddr, frame).is_Ok() == self.map_frame(vaddr, frame).is_Ok());
                assume(false);
                assert(equal(self.map_frame(vaddr, frame).get_Ok_0().interp(), self.interp().map_frame(vaddr, frame).get_Ok_0()));
            }
        } else {
            assume(false);
        }
    }

    // NOTE: maybe return whether the frame was unmapped
    // #[spec] pub fn unmap_frame(self, base: nat) -> (nat /* size */, PrefixTreeNode) {
    //     decreases(self.next_sizes.len());

    //     if base % self.page_size == 0 {
    //         if self.map.dom().contains(base) {
    //             (
    //                 self.page_size,
    //                 PrefixTreeNode {
    //                     map: self.map.remove(base),
    //                     ..self
    //                 }
    //             )
    //         } else {
    //             arbitrary()
    //         }
    //     } else {
    //         let directory_addr = base % self.page_size;
    //         if self.map.dom().contains(directory_addr) {
    //             let (page_size, directory) = self.map.index(directory_addr).get_Directory_0().unmap_frame(base);
    //             (
    //                 page_size,
    //                 if directory.map.dom().len() > 0 {
    //                     PrefixTreeNode {
    //                         map: self.map.insert(directory_addr, box NodeEntry::Directory(directory)),
    //                         ..self
    //                     }
    //                 } else {
    //                     PrefixTreeNode {
    //                         map: self.map.remove(directory_addr),
    //                         ..self
    //                     }
    //                 }
    //             )
    //         } else {
    //             arbitrary()
    //         }
    //     }
    // }
}

// #[proof]
// fn next_sizes_len_decreases(node: PrefixTreeNode) {
//     requires(node.inv());
//     ensures(forall(|i: nat| i < node.next_sizes.len() >>= node.page_size > node.next_sizes.index(i)));
//
//     if node.next_sizes.len() == 0 {
//     } else {
//         forall(|i: nat| {
//             requires(i < node.next_sizes.len());
//             ensures(node.page_size > node.next_sizes.index(i));
//
//             if i == 0 {
//             } else {
//             }
//         });
//     }
// }
//
// #[proof]
// fn map_frame_preserves_inv_2(node: PrefixTreeNode, base: nat, frame: MemRegion) {
//     requires(node.inv() && node.view().accepted_mapping(base, frame) && frame.size <= node.page_size);
//     ensures(node.map_frame(base, frame).inv());
// }


// #[proof]
// fn map_frame_contradiction(node: PrefixTreeNode, base: nat, frame: MemRegion) {
//     #[spec] let new_node = node.map_frame(base, frame);
//     assert(false);
// }

// #[exec] fn unmap_frame(&mut self, vaddr: usize) {
//     requires(self.view().map.dom().contains(vaddr));
//     ensures(self.view().map == old(self).view().map.remove(vaddr));
// }

// #[exec] fn unmap_frame(&mut self, vaddr: usize) -> (Option<()>, Frame) {
//     ensures(|res: Option<()>| [
//         if self.view().map.dom().contains(vaddr) {
//             true
//             && res == Some(())
//             && self.view().map == old(self).view().map.remove(vaddr)
//         } else {
//             true
//             && res == None
//             && equal(self, old(self))
//         }
//     ])
// }

// #[exec] fn actually_resolve(self, vaddr: usize) -> ActualMemRegion {
//     requires(self.view().map.dom().contains(vaddr));
// }
//

// NOTE: pages are 1 GiB, 2 MiB, 4 KiB
// NOTE: on ARM consecutive entries in vspace and physical space, one TLB entry
// NOTE: the memory alloc may fail
// NOTE: use linearity to prevent a frame being mapped in the kernel and user-space at the same
// time

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
