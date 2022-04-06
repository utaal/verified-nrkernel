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

pub struct MemRegion { pub base: nat, pub size: nat }

// TODO use VAddr, PAddr

#[proof]
pub struct PageTableContents {
    pub map: Map<nat /* VAddr */, MemRegion>,
}

#[spec]
pub fn base_page_aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

#[spec]
pub fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region1.base + region1.size <= region2.base
    } else {
        region2.base + region2.size <= region1.base
    }
}

impl PageTableContents {
    #[spec]
    pub fn ext_equal(self, pt2: PageTableContents) -> bool {
        self.map.ext_equal(pt2.map)
    }

    #[spec]
    pub fn inv(&self) -> bool {
        true
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
        && forall(|b: nat| self.map.dom().contains(b) >>= !overlap(
                MemRegion { base: base, size: frame.size },
                MemRegion { base: b, size: self.map.index(b).size }
           ))
    }

    /// Maps the given `frame` at `base` in the address space
    #[spec] pub fn map_frame(self, base: nat, frame: MemRegion) -> PageTableContents {
        PageTableContents {
            map: self.map.insert(base, frame),
            ..self
        }
    }

    #[proof] fn map_frame_preserves_inv(#[spec] self, base: nat, frame: MemRegion) {
        requires([
            self.inv(),
            self.accepted_mapping(base, frame),
        ]);
        ensures([
            self.map_frame(base, frame).inv()
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
    #[spec] fn resolve(self, vaddr: nat) -> nat {
        if exists(|n:nat|
                  self.map.dom().contains(n) &&
                  n <= vaddr && vaddr < n + self.map.index(n).size) {
            let n = choose(|n:nat|
                           self.map.dom().contains(n) &&
                           n <= vaddr && vaddr < n + self.map.index(n).size);
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
pub struct PrefixTreeNode {
    pub map: Map<nat /* addr */, Box<NodeEntry>>, // consider using the entry index
    pub layer: nat,       // index into layer_sizes
    pub base_vaddr: nat,
}

// page_size, next_sizes
// 2**40    , [ 2 ** 30, 2 ** 20 ]
// 2**30    , [ 2 ** 20 ]
// 2**20    , [ ]

fndecl!(pub fn pow2(v: nat) -> nat);


impl PrefixTreeNode {
    #[spec]
    pub fn entry_size(&self, arch: &Arch) -> nat {
        arch.layer_sizes.index(self.layer as int + 1)
    }

    #[spec]
    pub fn layer_size(&self, arch: &Arch) -> nat {
        arch.layer_sizes.index(self.layer as int)
    }

    #[spec]
    pub fn entries_are_entry_size_aligned(&self, arch: &Arch) -> bool {
        forall(|offset: nat| self.map.dom().contains(offset) >>= base_page_aligned(offset, self.entry_size(arch)))
    }

    #[spec]
    pub fn entries_fit_in_layer_size(&self, arch: &Arch) -> bool {
        forall(|offset: nat| self.map.dom().contains(offset) >>= offset < self.layer_size(arch))
    }

    #[spec]
    pub fn pages_match_entry_size(&self, arch: &Arch) -> bool {
        forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Page())
               >>= self.map.index(offset).get_Page_0().size == self.entry_size(arch))
    }

    #[spec]
    pub fn directories_are_in_next_layer(&self, arch: &Arch) -> bool {
        forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Directory())
               >>= {
                    let directory = self.map.index(offset).get_Directory_0();
                    true
                    && directory.layer == self.layer + 1
                    && directory.base_vaddr == self.base_vaddr + offset
                })
    }

    #[spec]
    pub fn directories_obey_invariant(&self, arch: &Arch) -> bool {
        decreases((arch.layer_sizes.len() - self.layer, 0));

        if self.layer < arch.layer_sizes.len() && self.directories_are_in_next_layer(arch) { 
            forall(|offset: nat| (self.map.dom().contains(offset) && self.map.index(offset).is_Directory())
                   >>= self.map.index(offset).get_Directory_0().inv(arch))
        } else {
            arbitrary()
        }
    }

    #[spec]
    pub fn inv(&self, arch: &Arch) -> bool {
        decreases((arch.layer_sizes.len() - self.layer, 1));

        true
        && self.interp(arch).inv()

        && self.map.dom().finite()
        && self.layer < arch.layer_sizes.len()
        && self.entries_are_entry_size_aligned(arch)
        && self.entries_fit_in_layer_size(arch)
        && self.pages_match_entry_size(arch)
        && self.directories_are_in_next_layer(arch)
        && self.directories_obey_invariant(arch)
    }

    // #[spec]
    // pub fn termination_test(self, arch: &Arch) {
    //     decreases(self);

    //     if self.inv(arch) && arch.inv() {
    //         if self.map.dom().len() == 0 {
    //             ()
    //         } else {
    //             let k = self.map.dom().choose();
    //             if self.map.index(k).is_Directory() {
    //                 self.map.index(k).get_Directory_0().termination_test(arch)
    //             } else {
    //                 ()
    //             }
    //         }
    //     } else {
    //         ()
    //     }
    // }

    #[spec]
    pub fn interp_fold(self, arch: &Arch, acc: Map<nat, MemRegion>, rest: Map<nat, Box<NodeEntry>>) -> Map<nat, MemRegion> {
        decreases((acc.dom().len(), 0));

        if acc.dom().finite() && rest.dom().finite() {
            if rest.dom().len() > 0 {
                let x = rest.dom().choose();
                match *self.map.index(x) {
                     NodeEntry::Page(p) =>
                         self.interp_fold(arch, acc.union_prefer_right(map![self.base_vaddr + x => p]), self.map.remove(x)),
                     NodeEntry::Directory(d) =>
                         self.interp_fold(arch, acc.union_prefer_right(d.interp(arch).map), self.map.remove(x)),
                }
            } else {
                acc
            }
        } else {
            arbitrary()
        }
    }

    #[spec]
    pub fn interp(self, arch: &Arch) -> PageTableContents {
        decreases((self, 1));

        PageTableContents {
            map: self.interp_fold(arch, map![], self.map)
        }
    }

    #[spec] pub fn accepted_mapping(self, arch: &Arch, base: nat, frame: MemRegion) -> bool {
        true
        && self.interp(arch).accepted_mapping(base, frame)
    }

    #[spec]
    pub fn map_frame(self, arch: &Arch, vaddr: nat, frame: MemRegion) -> PrefixTreeNode {
        decreases(arch.layer_sizes.len() - self.layer);

        let offset = vaddr - self.base_vaddr;
        if frame.size == self.entry_size(arch) {
            PrefixTreeNode {
                map: self.map.insert(offset, box NodeEntry::Page(frame)),
                ..self
            }
        } else {
            let binding_offset = offset - (offset % self.entry_size(arch)); // 0xf374 -- entry_size 0x100 --> 0xf300
            let directory: PrefixTreeNode = if self.map.dom().contains(offset) {
                self.map.index(binding_offset).get_Directory_0()
            } else {
                PrefixTreeNode {
                    map: map![],
                    layer: self.layer + 1,
                    base_vaddr: self.base_vaddr + binding_offset
                }
            };
            let updated_directory = directory.map_frame(arch, vaddr, frame);
            PrefixTreeNode {
                map: self.map.insert(binding_offset, box NodeEntry::Directory(updated_directory)),
                ..self
            }
        }
    }

    #[proof]
    fn map_frame_refines(self, arch: &Arch, vaddr: nat, frame: MemRegion) {
        requires(self.inv(arch) && arch.inv());
        ensures(equal(self.map_frame(arch, vaddr, frame).interp(arch), self.interp(arch).map_frame(vaddr, frame)));
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
