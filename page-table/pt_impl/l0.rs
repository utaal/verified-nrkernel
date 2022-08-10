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

#[verifier(nonlinear)]
pub proof fn ambient_arith()
    ensures
        forall_arith(|a: nat, b: nat| a == 0 ==> #[trigger] (a * b) == 0),
        forall_arith(|a: nat, b: nat| b == 0 ==> #[trigger] (a * b) == 0),
        forall_arith(|a: nat, b: nat| a > 0 && b > 0 ==> #[trigger] (a * b) > 0),
        forall_arith(|a: int, b: int| #[trigger] (a * b) == (b * a)),
        forall|a:nat| a != 0 ==> aligned(0, a)
{
    crate::lib::aligned_zero();
}

pub proof fn ambient_lemmas1()
    ensures
        forall|s1: Map<nat,MemRegion>, s2: Map<nat,MemRegion>| s1.dom().finite() && s2.dom().finite() ==> #[trigger] s1.union_prefer_right(s2).dom().finite(),
        forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
        forall|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
            (m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)),
        forall|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat|
            (m2.dom().contains(n) && !m1.dom().contains(n))
            ==> equal(m1.union_prefer_right(m2.remove(n)), m1.union_prefer_right(m2).remove(n)),
        forall|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat, v: MemRegion|
            (!m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.insert(n, v).union_prefer_right(m2), m1.union_prefer_right(m2).insert(n, v)),
        forall|m1: Map<nat, MemRegion>, m2: Map<nat, MemRegion>, n: nat, v: MemRegion|
            (!m1.dom().contains(n) && !m2.dom().contains(n))
            ==> equal(m1.union_prefer_right(m2.insert(n, v)), m1.union_prefer_right(m2).insert(n, v)),
        // forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().upper == d.upper_vaddr())),
        // forall(|d: Directory| d.inv() ==> (#[trigger] d.interp().lower == d.base_vaddr)),
    {
    lemma_finite_map_union::<nat,MemRegion>();
    // assert_nonlinear_by({ ensures(forall|d: Directory| equal(d.num_entries() * d.entry_size(), d.entry_size() * d.num_entries())); });
    // assert_forall_by(|d: Directory, i: nat| {
    //     requires(#[auto_trigger] d.inv() && i < d.num_entries() && d.entries.index(i).is_Directory());
    //     ensures(#[auto_trigger] d.entries.index(i).get_Directory_0().inv());
    //     assert(d.directories_obey_invariant());
    // });
    lemma_map_union_prefer_right_remove_commute::<nat,MemRegion>();
    lemma_map_union_prefer_right_insert_commute::<nat,MemRegion>();
    assert(forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a)) by (nonlinear_arith) { };
}


// #[proof]
// fn ambient_lemmas3() {
//     ensures([
//             forall(|d: Directory, base: nat, frame: MemRegion|
//                    d.inv() && #[trigger] d.accepted_mapping(base, frame) ==>
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

#[derive(PartialEq, Eq, Structural)]
pub struct MemRegionExec { pub base: usize, pub size: usize }

impl MemRegionExec {
    pub open spec fn view(self) -> MemRegion {
        MemRegion {
            base: self.base as nat,
            size: self.size as nat,
        }
    }
}

// TODO use VAddr, PAddr

pub open spec fn strictly_decreasing(s: Seq<nat>) -> bool {
    forall|i: nat, j: nat| i < j && j < s.len() ==> s.index(i) > s.index(j)
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

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

impl ArchLayerExec {
    pub open spec fn view(self) -> ArchLayer {
        ArchLayer {
            entry_size: self.entry_size,
            num_entries: self.num_entries,
        }
    }
}

pub struct ArchExec {
    // TODO: This could probably be an array, once we have support for that
    pub layers: Vec<ArchLayerExec>,
}

impl ArchExec {
    pub open spec fn view(self) -> Arch {
        Arch {
            layers: self.layers@.map(|i: int, l: ArchLayerExec| l@),
        }
    }

    pub fn entry_size(&self, layer: usize) -> (res: usize)
        requires layer < self@.layers.len()
        ensures  res == self@.entry_size(layer)
    {
        self.layers.index(layer).entry_size
    }

    pub fn num_entries(&self, layer: usize) -> (res: usize)
        requires layer < self@.layers.len()
        ensures  res == self@.num_entries(layer)
    {
        self.layers.index(layer).num_entries
    }

    pub fn index_for_vaddr(&self, layer: usize, base: usize, vaddr: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            vaddr >= base,
        ensures
            res == self@.index_for_vaddr(layer, base, vaddr)
    {
        let es = self.entry_size(layer);
        assert(es == self@.entry_size(layer));
        let offset = vaddr - base;
        assert((vaddr as nat - base as nat) == (vaddr - base) as nat);
        assume((offset as nat) / (es as nat) < 0x1_0000_0000);
        // by (nonlinear_arith)
        //     requires
        //         offset as nat == (vaddr as nat - base as nat),
        //         ...
        // {}
        let res = offset / es;

        // NOTE: necessary to prove
        //   (assert (=
        //    (uClip SZ (EucDiv (uClip SZ offset) es))
        //    (nClip (EucDiv (nClip offset) es))
        //   ))
        assert(res as nat == offset as nat / es as nat) by (nonlinear_arith)
            requires
                res == offset / es,
                (offset as nat) / (es as nat) < 0x1_0000_0000,
                0 <= offset as int,
                0 < es as int,
        {
            assert(0 <= (offset as nat) / (es as nat));
        }
        res
    }

    #[verifier(nonlinear)]
    pub fn entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= MAX_NUM_ENTRIES,
        ensures
            res == self@.entry_base(layer, base, idx)
    {
        proof {
            crate::lib::mult_leq_mono_both(idx, self@.entry_size(layer), MAX_NUM_ENTRIES, MAX_ENTRY_SIZE);
        }
        base + idx * self.entry_size(layer)
    }

    pub fn next_entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= MAX_NUM_ENTRIES,
        ensures
            res == self@.next_entry_base(layer, base, idx)
    {
        proof {
            overflow_bounds();
            let es = self@.entry_size(layer);
            assert(0 <= (idx + 1) * es <= MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1)) by (nonlinear_arith)
                requires es <= MAX_ENTRY_SIZE, idx <= MAX_NUM_ENTRIES
                { /* New instability with z3 4.10.1 */ };
        }
        let offset = (idx + 1) * self.entry_size(layer);
        proof {
            assert(base + offset <= MAX_BASE + MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1)) by (nonlinear_arith)
                requires
                    0 <= offset <= MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1),
                    0 <= base <= MAX_BASE,
                {};
        }
        base + offset
    }
}

pub ghost struct ArchLayer {
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

pub const MAX_ENTRY_SIZE:   nat = 512 * 1024 * 1024 * 1024;
pub const MAX_NUM_LAYERS:   nat = 4;
pub const MAX_NUM_ENTRIES:  nat = 512;
pub const MAX_BASE:         nat = MAX_ENTRY_SIZE * MAX_NUM_ENTRIES;

// Sometimes z3 needs these concrete bounds to prove the no-overflow VC
pub proof fn overflow_bounds()
    ensures
        MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1) < 0x10000000000000000,
        MAX_BASE + MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1) < 0x10000000000000000,
{
    assert(MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
    assert(MAX_BASE + MAX_ENTRY_SIZE * (MAX_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
}

impl Arch {
    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends layer < self.layers.len()
    {
        self.layers.index(layer).entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends layer < self.layers.len()
    {
        self.layers.index(layer).num_entries
    }

    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        base + self.num_entries(layer) * self.entry_size(layer)
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= MAX_NUM_LAYERS
        &&& forall|i:nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i)  <= MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= MAX_NUM_ENTRIES
                &&& self.entry_size_is_next_layer_size(i)
            }
    }

    pub open spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends i < self.layers.len()
    {
        i + 1 < self.layers.len() ==>
            self.entry_size(i) == self.entry_size((i + 1) as nat) * self.num_entries((i + 1) as nat)
    }

    pub open spec(checked) fn contains_entry_size_at_index_atleast(&self, entry_size: nat, min_idx: nat) -> bool {
        exists|i: nat| min_idx <= i && i < self.layers.len() && #[trigger] self.entry_size(i) == entry_size
    }

    pub open spec(checked) fn contains_entry_size(&self, entry_size: nat) -> bool {
        self.contains_entry_size_at_index_atleast(entry_size, 0)
    }

    pub proof fn lemma_entry_sizes_aligned(self, i: nat, j: nat)
        requires
            self.inv(),
            i <= j,
            j < self.layers.len(),
        ensures
            aligned(self.entry_size(i), self.entry_size(j))
        decreases (self.layers.len() - i)
    {
        ambient_lemmas1();
        if i == j {
            assert(aligned(self.entry_size(i), self.entry_size(j))) by (nonlinear_arith)
                requires i == j, self.entry_size(i) > 0,
            { };
        } else {
            self.lemma_entry_sizes_aligned(i+1,j);
            crate::lib::mod_of_mul_auto();
            crate::lib::aligned_transitive_auto();
            assert(aligned(self.entry_size(i), self.entry_size(j)));
        }
    }

    pub proof fn lemma_entry_sizes_aligned_auto(self)
        ensures
            forall|i: nat, j: nat|
                self.inv() && i <= j && j < self.layers.len() ==>
                aligned(self.entry_size(i), self.entry_size(j))
    {
        assert_forall_by(|i: nat, j: nat| {
            requires(self.inv() && i <= j && j < self.layers.len());
            ensures(aligned(self.entry_size(i), self.entry_size(j)));
            self.lemma_entry_sizes_aligned(i, j);
        });
    }

    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
         ((vaddr - base) as nat) / self.entry_size(layer)
    }

    pub proof fn lemma_index_for_vaddr(self, layer: nat, base: nat, vaddr: nat)
        requires
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
            vaddr < self.upper_vaddr(layer, base),
        ensures
            ({
                let idx = self.index_for_vaddr(layer, base, vaddr);
                &&& idx < self.num_entries(layer)
                &&& between(vaddr, self.entry_base(layer, base, idx), self.next_entry_base(layer, base, idx))
                &&& aligned(vaddr, self.entry_size(layer)) ==> vaddr == self.entry_base(layer, base, idx)
                &&& idx < MAX_NUM_ENTRIES
            }),
    {
        // FIXME: prove all this stuff
        let idx = self.index_for_vaddr(layer, base, vaddr);
        assert(idx < self.num_entries(layer)) by(nonlinear_arith)
            requires
                self.inv(),
                layer < self.layers.len(),
                between(vaddr, base, self.upper_vaddr(layer, base)),
                idx == self.index_for_vaddr(layer, base, vaddr),
        { };
        assert(between(vaddr, self.entry_base(layer, base, idx), self.next_entry_base(layer, base, idx))) by(nonlinear_arith)
            requires
                self.inv(),
                layer < self.layers.len(),
                between(vaddr, base, self.upper_vaddr(layer, base)),
                idx == self.index_for_vaddr(layer, base, vaddr),
                idx < self.num_entries(layer),
        { };
        assert(aligned(vaddr, self.entry_size(layer)) ==> vaddr == self.entry_base(layer, base, idx)) by (nonlinear_arith)
            requires
                self.inv(),
                layer < self.layers.len(),
                base <= vaddr,
                vaddr < self.upper_vaddr(layer, base),
                idx == self.index_for_vaddr(layer, base, vaddr),
                idx < self.num_entries(layer),
                between(vaddr, self.entry_base(layer, base, idx), self.next_entry_base(layer, base, idx)),
        {
            assume(false);
        };
        assert(idx < MAX_NUM_ENTRIES);
    }

    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        base + idx * self.entry_size(layer)
    }

    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        base + (idx + 1) * self.entry_size(layer)
    }

    // #[verifier(nonlinear)]
    // pub proof fn lemma_entry_base_manual(self, i: nat)
    //     requires
    //         self.inv(),
    //     ensures
    //         forall_arith(|j: nat| j < i ==> self.entry_base(j) < self.entry_base(i) && self.entry_base(#[trigger] (j+1)) <= self.entry_base(i)),
    //         aligned(self.entry_base(i), self.entry_size()),
    //         // forall(|i: nat| i < self.num_entries() && self.entries.index(i).is_Directory() ==> {
    //         //     let d = self.entries.index(i).get_Directory_0();
    //         //     d.upper_vaddr() == self.entry_base(i+1)
    //         // })
    // {
    //     self.lemma_entry_base_auto();
    // }

    // #[verifier(nonlinear)]
    pub proof fn lemma_entry_base(self)
        requires
            self.inv(),
        ensures
            forall|idx: nat, j: nat, base: nat, layer: nat|
                #![trigger self.entry_base(layer, base, idx), self.entry_base(layer, base, j)]
                layer < self.layers.len() && idx < j ==>
                          self.entry_base(layer, base, idx) <  self.entry_base(layer, base, j),
                       // && self.next_entry_base(layer, base, idx) <= self.entry_base(layer, base, j),
            // TODO: The line above can't be a separate postcondition because it doesn't have any valid triggers.
            // The trigger for it is pretty bad.
            forall|idx: nat, j: nat, base: nat, layer: nat| idx < j
                ==> self.next_entry_base(layer, base, idx) <= self.entry_base(layer, base, j),
            // forall|a: nat, base: nat, layer: nat|
            //     aligned(base, self.entry_size(layer) * a) ==> #[trigger] aligned(base, self.entry_size(layer)),
            // TODO: Have to use a less general postcondition because the one above doesn't have
            // any valid triggers
            forall|idx: nat, base: nat, layer: nat| #![trigger self.next_entry_base(layer, base, idx)]
                layer < self.layers.len() ==>
            {
                &&& self.next_entry_base(layer, base, idx) == self.entry_base(layer, base, idx) + self.entry_size(layer)
                &&& self.next_entry_base(layer, base, idx) == self.entry_size(layer) + self.entry_base(layer, base, idx)
            },
            forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() && aligned(base, self.entry_size(layer)) ==> #[trigger] aligned(self.entry_base(layer, base, idx), self.entry_size(layer)),
            forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() ==> base <= self.entry_base(layer, base, idx),
            forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() && idx < self.num_entries(layer) ==> self.entry_base(layer, base, idx) < self.upper_vaddr(layer, base),
            forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() && idx <= self.num_entries(layer) ==> self.entry_base(layer, base, idx) <= self.upper_vaddr(layer, base),
            forall|idx: nat, base: nat, layer: nat|
                layer + 1 < self.layers.len() ==> #[trigger] self.next_entry_base(layer, base, idx) == self.upper_vaddr(layer + 1, self.entry_base(layer, base, idx)),
            // Support postconditions:
            forall|base: nat, layer: nat| // Used to infer lhs of next postcondition's implication
                layer < self.layers.len() && aligned(base, self.entry_size(layer) * self.num_entries(layer)) ==> #[trigger] aligned(base, self.entry_size(layer)),
    {
        // FIXME: prove this
        assert(forall|idx: nat, j: nat, base: nat, layer: nat|
                #![trigger self.entry_base(layer, base, idx), self.entry_base(layer, base, j)]
                layer < self.layers.len() && idx < j ==> self.entry_base(layer, base, idx)     <  self.entry_base(layer, base, j)
                       && self.entry_base(layer, base, idx + 1) <= self.entry_base(layer, base, j)) by(nonlinear_arith)
            requires
                self.inv(),
        { };


        assert(forall|idx: nat, j: nat, base: nat, layer: nat| idx < j
                ==> self.next_entry_base(layer, base, idx) <= self.entry_base(layer, base, j)) by (nonlinear_arith)
            requires self.inv(),
        { }

        assert forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() implies
            {
                &&& #[trigger] self.next_entry_base(layer, base, idx) == self.entry_base(layer, base, idx) + self.entry_size(layer)
                &&& self.next_entry_base(layer, base, idx) == self.entry_size(layer) + self.entry_base(layer, base, idx)
            } by {

            assert(
                #[trigger] self.next_entry_base(layer, base, idx) == self.entry_base(layer, base, idx) + self.entry_size(layer)) by (nonlinear_arith)
                requires self.inv(), layer < self.layers.len(),
            { };

            assert(
                self.next_entry_base(layer, base, idx) == self.entry_size(layer) + self.entry_base(layer, base, idx)) by (nonlinear_arith)
                requires self.inv(), layer < self.layers.len(),
            { };
        }

        assert forall|idx: nat, base: nat, layer: nat|
                layer < self.layers.len() && aligned(base, self.entry_size(layer)) implies #[trigger] aligned(self.entry_base(layer, base, idx), self.entry_size(layer)) by {

            assert(aligned(self.entry_base(layer, base, idx), self.entry_size(layer))) by (nonlinear_arith)
                requires self.inv(), layer < self.layers.len(), aligned(base, self.entry_size(layer)),
            {
                assume(false);
            }
        }
        assume(false);
    }

}

#[verifier(nonlinear)]
proof fn arch_inv_test() {
    let x86 = Arch {
        layers: seq![
            ArchLayer { entry_size: 512 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 1 * 1024 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 2 * 1024 * 1024, num_entries: 512 },
            ArchLayer { entry_size: 4 * 1024, num_entries: 512 },
        ],
    };
    assert(x86.entry_size(3) == 4096);
    assert(x86.contains_entry_size(4096));
    assert(x86.layers.len() <= MAX_NUM_LAYERS);
    assert forall|i:nat| i < x86.layers.len() implies {
            &&& 0 < #[trigger] x86.entry_size(i)  <= MAX_ENTRY_SIZE
            &&& 0 < #[trigger] x86.num_entries(i) <= MAX_NUM_ENTRIES
            &&& x86.entry_size_is_next_layer_size(i)
        } by {
        assert(0 < #[trigger] x86.entry_size(i)  <= MAX_ENTRY_SIZE);
        assert(0 < #[trigger] x86.num_entries(i) <= MAX_NUM_ENTRIES);
        assert(x86.entry_size_is_next_layer_size(i));
    }
    assert(x86.inv());
}

pub ghost struct PageTableContents {
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
    pub open spec(checked) fn inv(&self) -> bool {
        true
        && self.map.dom().finite()
        && self.arch.inv()
        && self.mappings_are_of_valid_size()
        && self.mappings_are_aligned()
        && self.mappings_dont_overlap()
        && self.mappings_in_bounds()
    }

    pub open spec(checked) fn mappings_are_of_valid_size(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).size] #![trigger self.map.index(va).base]
            self.map.dom().contains(va) ==> self.arch.contains_entry_size(self.map.index(va).size)
    }

    pub open spec(checked) fn mappings_are_aligned(self) -> bool {
        forall|va: nat|
            #![trigger self.map.index(va).size] #![trigger self.map.index(va).base]
            self.map.dom().contains(va) ==>
            aligned(va, self.map.index(va).size) && aligned(self.map.index(va).base, self.map.index(va).size)
    }

    pub open spec(checked) fn mappings_dont_overlap(self) -> bool {
        forall|b1: nat, b2: nat|
            // TODO verus the default triggers were bad
            #![trigger self.map.index(b1), self.map.index(b2)] #![trigger self.map.dom().contains(b1), self.map.dom().contains(b2)]
            self.map.dom().contains(b1) && self.map.dom().contains(b2) ==>
            ((b1 == b2) || !overlap(
                    MemRegion { base: b1, size: self.map.index(b1).size },
                    MemRegion { base: b2, size: self.map.index(b2).size }))
    }

    pub open spec(checked) fn candidate_mapping_in_bounds(self, base: nat, frame: MemRegion) -> bool {
        self.lower <= base && base + frame.size <= self.upper
    }

    pub open spec(checked) fn mappings_in_bounds(self) -> bool {
        forall|b1: nat|
            #![trigger self.map.index(b1)] #![trigger self.map.dom().contains(b1)]
            #![trigger self.candidate_mapping_in_bounds(b1, self.map.index(b1))]
            self.map.dom().contains(b1) ==> self.candidate_mapping_in_bounds(b1, self.map.index(b1))
    }

    pub open spec(checked) fn accepted_mapping(self, base: nat, frame: MemRegion) -> bool {
        true
        && aligned(base, frame.size)
        && aligned(frame.base, frame.size)
        && self.candidate_mapping_in_bounds(base, frame)
        && self.arch.contains_entry_size(frame.size)
    }

    pub open spec(checked) fn valid_mapping(self, base: nat, frame: MemRegion) -> bool {
        forall|b: nat| #![auto]
            self.map.dom().contains(b) ==> !overlap(
                MemRegion { base: base, size: frame.size },
                MemRegion { base: b, size: self.map.index(b).size })
    }

    /// Maps the given `frame` at `base` in the address space
    pub open spec(checked) fn map_frame(self, base: nat, frame: MemRegion) -> Result<PageTableContents,()> {
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

    pub open spec(checked) fn accepted_resolve(self, vaddr: nat) -> bool {
        between(vaddr, self.lower, self.upper)
    }

    /// Given a virtual address `vaddr` it returns the corresponding `PAddr`
    /// and access rights or an error in case no mapping is found.
    // #[spec] fn resolve(self, vaddr: nat) -> MemRegion {
    pub open spec(checked) fn resolve(self, vaddr: nat) -> Result<nat,()>
        recommends self.accepted_resolve(vaddr)
    {
        if exists|base:nat|
            self.map.dom().contains(base) &&
            between(vaddr, base, base + (#[trigger] self.map.index(base)).size) {
            let base = choose(|base:nat|
                           self.map.dom().contains(base) &&
                           between(vaddr, base, base + (#[trigger] self.map.index(base)).size));
            let offset = vaddr - base;
            Ok((self.map.index(base).base + offset) as nat)
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
    pub open spec(checked) fn unmap(self, base: nat) -> Result<PageTableContents,()>
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
            !overlap(MemRegion { base: s, size: self.map.index(s).size }, MemRegion { base: o, size: other.map.index(o).size })
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
            forall|va: nat| #[trigger] self.map.dom().contains(va) ==> self.map.index(va).size > 0;
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
