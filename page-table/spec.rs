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
        true
        && strictly_decreasing(self.layer_sizes)
        && forall(|i:nat| i < self.layer_sizes.len() >>= self.layer_sizes.index(i) > 0)
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
    Empty(),
}

#[proof]
pub struct PrefixTreeNode {
    pub entries: Seq<NodeEntry>,
    pub layer: nat,       // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
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

    // #[spec]
    // pub fn entries_are_entry_size_aligned(&self) -> bool {
    //     forall(|offset: nat| #[auto_trigger] self.map.dom().contains(offset) >>= base_page_aligned(offset, self.entry_size()))
    // }

    // #[spec]
    // pub fn entries_fit_in_layer_size(&self) -> bool {
    //     forall(|offset: nat| self.map.dom().contains(offset) >>= offset < self.layer_size())
    // }

    #[spec]
    pub fn pages_match_entry_size(&self) -> bool {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Page())
               >>= (#[trigger] self.entries.index(i)).get_Page_0().size == self.entry_size())
    }

    #[spec]
    pub fn directories_are_in_next_layer(&self) -> bool {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= {
                    let directory = (#[trigger] self.entries.index(i)).get_Directory_0();
                    true
                    && directory.layer == self.layer + 1
                    && directory.base_vaddr == self.base_vaddr + i * self.entry_size()
                })
    }

    #[spec]
    pub fn directories_obey_invariant(&self) -> bool {
        decreases((self.arch.layer_sizes.len() - self.layer, 0));

        if self.layer < self.arch.layer_sizes.len() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
                   >>= (#[trigger] self.entries.index(i)).get_Directory_0().inv())
        } else {
            arbitrary()
        }
    }

    #[spec]
    pub fn directories_match_arch(&self) -> bool {
        forall(|i: nat| (i < self.entries.len() && self.entries.index(i).is_Directory())
               >>= equal((#[trigger] self.entries.index(i)).get_Directory_0().arch, self.arch))
    }

    #[spec]
    pub fn inv(&self) -> bool {
        decreases((self.arch.layer_sizes.len() - self.layer, 1));

        true
        && self.interp().inv()

        && self.entries.len() == self.layer_size()
        && self.layer < self.arch.layer_sizes.len()
        // && self.entries_are_entry_size_aligned()
        // && self.entries_fit_in_layer_size()
        && self.pages_match_entry_size()
        && self.directories_are_in_next_layer()
        && self.directories_obey_invariant()
        && self.directories_match_arch()
    }

    #[spec]
    pub fn interp(self) -> PageTableContents {
        self.interp_aux(0)
    }

    #[spec]
    pub fn interp_aux(self, i: nat) -> PageTableContents {
        decreases((self, self.layer_size() - i, 0));
        decreases_by(Self::check_interp_aux);

        // if self.inv() {
        if i >= self.entries.len() {
            PageTableContents {
                map: map![],
                arch: self.arch,
            }
        } else { // i < self.entries.len()
                 // TODO: using map also impossible (like fold)?
                 // let maps = self.entries.map(|i:nat| );
            let rem = self.interp_aux(i+1).map;
            PageTableContents {
                map: match self.entries.index(i) {
                    NodeEntry::Page(p)      => rem.union_prefer_right(map![self.base_vaddr + i * self.entry_size() => p]),
                    NodeEntry::Directory(d) => rem.union_prefer_right(d.interp_aux(0).map),
                    NodeEntry::Empty()      => rem,
                },
                arch: self.arch,
            }
        }
        // } else {
        //     arbitrary()
        // }
    }

    #[proof] #[verifier(decreases_by)]
    fn check_interp_aux(self, i: nat) {
        assume(false);
        // if i >= self.entries.len() {
        //     assume(false);
        // } else {
        //     // TODO
        //     assume(false);
        // }
    }

    // #[proof]
    // fn x0(i: nat, m1: Map<nat,nat>, m2: Map<nat,nat>) {
    //     requires(m1.dom().contains(i));
    //     ensures([
    //             m1.union_prefer_right(m2).dom().contains(i),
    //             m2.union_prefer_right(m1).dom().contains(i)
    //     ]);
    // }

    #[proof]
    fn x1(self, j: nat, i: nat) {
        decreases(self.entries.len() - i);
        requires([
                 // self.entry_size() > 0,
                 // self.inv(),
                 // self.entries.index(i).is_Page()
                 j >= i,
                 j < self.entries.len(),
                 self.entries.index(j).is_Page(),
        ]);
        ensures([
                self.interp_aux(i).map.dom().contains(self.base_vaddr + j * self.entry_size()),
                // equal(self.interp_aux(i).map.index(self.base_vaddr + i * self.entry_size()), self.entries(i))
        ]);

        if i >= self.entries.len() {
        } else {
            if j == i {
                assume(false);
            } else {
                assert(j > i);
                // assert(self.inv());
                // reveal_with_fuel(Self::interp_aux, 2);
                assert(j >= i +1);
                assert(j < self.entries.len());
                assert(self.entries.index(j).is_Page());
                self.x1(j, i+1);
                assert(self.interp_aux(i+1).map.dom().contains(self.base_vaddr + j * self.entry_size()));
                // assume(self.interp_aux(i+1).map.dom().contains(self.base_vaddr + j * self.entry_size()));
                let rem = self.interp_aux(i+1).map;
                match self.entries.index(i) {
                    NodeEntry::Page(p) => {
                        assume(false);
                        assume(self.entry_size() > 0);
                        assert(self.base_vaddr + i * self.entry_size() < self.base_vaddr + j * self.entry_size());
                        assert(rem.union_prefer_right(map![self.base_vaddr + i * self.entry_size() => p]).dom().contains(self.base_vaddr + j * self.entry_size()));
                    },
                    NodeEntry::Directory(d) => {
                        assume(false);
                        let dmap = d.interp_aux(0).map;
                        assume(forall(|k:nat|
                                      dmap.dom().contains(k)
                                      >>= self.base_vaddr + i * self.entry_size() <= k
                                      && k + dmap.index(k).size <= self.base_vaddr + (i+1) * self.entry_size()));
                        assert(!dmap.dom().contains(self.base_vaddr + j * self.entry_size()));
                    },
                };
            }
        }
    }

    #[proof]
    fn x2(self) {
        requires(self.inv());
        // ensures(forall(|offset:nat|
        //                self.interp().map.contains(offset)
        //                >>= self.base_vaddr <= self.interp().map.index(offset).base
        //                     && self.interp().map.index(offset).base + self.interp().map.index(offset).size <= self.base_vaddr + self.layer_size() * self.entry_size()));
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
