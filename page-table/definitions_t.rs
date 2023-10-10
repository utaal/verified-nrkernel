#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::modes::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::map::*;
use vstd::set::*;
use vstd::set_lib::*;
use vstd::view::View;
use crate::impl_u::lib;
use crate::impl_u::indexing;

verus! {

pub const X86_NUM_LAYERS:  usize = 4;
pub const X86_NUM_ENTRIES: usize = 512;
pub const MAXPHYADDR_BITS: u64 = 52;
// FIXME: is this correct?
// spec const MAXPHYADDR: nat      = ((1u64 << 52u64) - 1u64) as nat;
// TODO: Probably easier to use computed constant because verus can't deal with the shift except in
// bitvector assertions.
pub spec const MAXPHYADDR: nat = 0xFFFFFFFFFFFFF;

pub const WORD_SIZE: usize = 8;
pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 1024 * 1024 * 1024;
pub spec const MAX_BASE:           nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

pub spec const PT_BOUND_LOW:  nat = 0;
// Upper bound for x86 4-level paging.
// 512 entries, each mapping 512*1024*1024*1024 bytes
pub const PT_BOUND_HIGH: usize = 512 * 512 * 1024 * 1024 * 1024;
pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;
pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;
pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;
pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn candidate_mapping_in_bounds(base: nat, pte: PageTableEntry) -> bool {
    base + pte.frame.size < x86_arch_spec.upper_vaddr(0, 0)
}

pub open spec fn candidate_mapping_overlaps_existing_vmem(mappings: Map<nat, PageTableEntry>, base: nat, pte: PageTableEntry) -> bool {
    exists|b: nat| #![auto] {
        &&& mappings.dom().contains(b)
        &&& overlap(
            MemRegion { base: base, size: pte.frame.size },
            MemRegion { base: b,    size: mappings[b].frame.size })
    }
}

pub open spec fn candidate_mapping_overlaps_existing_pmem(mappings: Map<nat, PageTableEntry>, base: nat, pte: PageTableEntry) -> bool {
    exists|b: nat| #![auto] {
        &&& mappings.dom().contains(b)
        &&& overlap(pte.frame, mappings.index(b).frame)
    }
}

pub exec fn aligned_exec(addr: usize, size: usize) -> (res: bool)
    requires
        size > 0
    ensures
        res == aligned(addr as nat, size as nat)
{
    addr % size == 0
}

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
}

pub open spec fn new_seq<T>(i: nat, e: T) -> Seq<T>
    decreases i
{
    if i == 0 {
        seq![]
    } else {
        new_seq((i-1) as nat, e).add(seq![e])
    }
}

pub proof fn lemma_new_seq<T>(i: nat, e: T)
    ensures
        new_seq(i, e).len() == i,
        forall|j: nat| j < i ==> new_seq(i, e).index(j as int) === e,
    decreases i
{
    if i == 0 {
    } else {
        lemma_new_seq::<T>((i-1) as nat, e);
    }
}

#[is_variant]
pub enum MapResult {
    ErrOverlap,
    Ok,
}

#[is_variant]
pub enum UnmapResult {
    ErrNoSuchMapping,
    Ok,
}

#[is_variant]
pub enum ResolveResultExec {
    ErrUnmapped,
    Ok(usize, PageTableEntryExec),
}

impl ResolveResultExec {
    pub open spec fn view(self) -> ResolveResult {
        match self {
            ResolveResultExec::ErrUnmapped => ResolveResult::ErrUnmapped,
            ResolveResultExec::Ok(base, pte) => ResolveResult::Ok(base as nat, pte@),
        }
    }
}

#[is_variant]
pub enum ResolveResult {
    ErrUnmapped,
    Ok(nat, PageTableEntry),
}

#[is_variant]
pub enum LoadResult {
    Pagefault,
    Value(nat), // word-sized load
}

#[is_variant]
pub enum StoreResult {
    Pagefault,
    Ok,
}

#[is_variant]
pub enum RWOp {
    Store { new_value: nat, result: StoreResult },
    Load { is_exec: bool, result: LoadResult },
}

pub struct MemRegion { pub base: nat, pub size: nat }

impl MemRegion {
    pub open spec fn contains(self, addr: nat) -> bool {
        between(addr, self.base, self.base + self.size)
    }
}

// only well-defined for sizes > 0
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

pub struct MemRegionExec { pub base: usize, pub size: usize }

impl MemRegionExec {
    pub open spec fn view(self) -> MemRegion {
        MemRegion {
            base: self.base as nat,
            size: self.size as nat,
        }
    }
}

pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

// We always set permissive flags on directories. Restrictions happen on the frame mapping.
pub spec const permissive_flags: Flags = Flags {
    is_writable:     true,
    is_supervisor:   false,
    disable_execute: false,
};

pub struct PageTableEntry {
    pub frame: MemRegion,
    /// The `flags` field on a `PageTableEntry` denotes the combined flags of the entire
    /// translation path to the entry. (See page table walk definition in hardware model,
    /// `spec_t::hardware`.) However, because we always set the flags on directories to be
    /// permissive these flags also correspond to the flags that we set for the frame mapping
    /// corresponding to this `PageTableEntry`.
    pub flags: Flags,
}

pub struct PageTableEntryExec {
    pub frame: MemRegionExec,
    pub flags: Flags,
}

impl PageTableEntryExec {
    pub open spec fn view(self) -> PageTableEntry {
        PageTableEntry {
            frame: self.frame@,
            flags: self.flags,
        }
    }
}

// Architecture

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

impl Clone for ArchLayerExec {
    fn clone(&self) -> Self {
        ArchLayerExec {
            entry_size: self.entry_size,
            num_entries: self.num_entries,
        }
    }
}

impl ArchLayerExec {
    pub open spec fn view(self) -> ArchLayer {
        ArchLayer {
            entry_size: self.entry_size as nat,
            num_entries: self.num_entries as nat,
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
        ensures  res == self@.entry_size(layer as nat)
    {
        self.layers[layer].entry_size
    }

    pub fn num_entries(&self, layer: usize) -> (res: usize)
        requires layer < self@.layers.len()
        ensures  res == self@.num_entries(layer as nat)
    {
        self.layers[layer].num_entries
    }

    pub fn index_for_vaddr(&self, layer: usize, base: usize, vaddr: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            vaddr >= base,
        ensures
            res == self@.index_for_vaddr(layer as nat, base as nat, vaddr as nat),
            res == indexing::index_from_base_and_addr(base as nat, vaddr as nat, self@.entry_size(layer as nat)),
    {
        let es = self.entry_size(layer);
        let offset = vaddr - base;
        let res = offset / es;
        assert(res as nat == offset as nat / es as nat) by (nonlinear_arith)
            requires
                res == offset / es,
                0 < es as int,
        { };
        res
    }

    #[verifier(nonlinear)]
    pub fn entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= X86_NUM_ENTRIES,
        ensures
            res == self@.entry_base(layer as nat, base as nat, idx as nat)
    {
        proof {
            // FIXME: Weird error message when using the spec const here
            // lib::mult_leq_mono_both(idx as nat, self@.entry_size(layer as nat), X86_NUM_ENTRIES as nat, X86_MAX_ENTRY_SIZE);
            lib::mult_leq_mono_both(idx as nat, self@.entry_size(layer as nat), X86_NUM_ENTRIES as nat, 512 * 1024 * 1024 * 1024);
        }
        base + idx * self.entry_size(layer)
    }

    pub fn next_entry_base(&self, layer: usize, base: usize, idx: usize) -> (res: usize)
        requires
            self@.inv(),
            layer < self@.layers.len(),
            base <= MAX_BASE,
            idx <= X86_NUM_ENTRIES,
        ensures
            res == self@.next_entry_base(layer as nat, base as nat, idx as nat)
    {
        proof {
            overflow_bounds();
            let es = self@.entry_size(layer as nat);
            assert(0 <= (idx + 1) * es <= X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1)) by (nonlinear_arith)
                requires es <= X86_MAX_ENTRY_SIZE, idx <= X86_NUM_ENTRIES
                { /* New instability with z3 4.10.1 */ };
        }
        let offset = (idx + 1) * self.entry_size(layer);
        proof {
            assert(base + offset <= MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1)) by (nonlinear_arith)
                requires
                    0 <= offset <= X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1),
                    0 <= base <= MAX_BASE,
                {};
        }
        base + offset
    }
}

pub struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    pub num_entries: nat,
}

pub struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

// Sometimes z3 needs these concrete bounds to prove the no-overflow VC
pub proof fn overflow_bounds()
    ensures
        X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
        MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
{
    assert(X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
    assert(MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
}

impl Arch {
    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends layer < self.layers.len()
    {
        self.layers.index(layer as int).entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends layer < self.layers.len()
    {
        self.layers.index(layer as int).num_entries
    }

    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        self.entry_base(layer, base, self.num_entries(layer))
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= X86_NUM_LAYERS
        &&& forall|i:nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i)  <= X86_MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= X86_NUM_ENTRIES
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
        decreases self.layers.len() - i
    {
        if i == j {
            assert(aligned(self.entry_size(i), self.entry_size(j))) by (nonlinear_arith)
                requires i == j, self.entry_size(i) > 0,
            { };
        } else {
            assert(forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a));
            self.lemma_entry_sizes_aligned(i+1,j);
            lib::mod_of_mul_auto();
            lib::aligned_transitive_auto();
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

    #[verifier(inline)]
    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
        indexing::index_from_base_and_addr(base, vaddr, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        // base + idx * self.entry_size(layer)
        indexing::entry_base_from_index(base, idx, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        // base + (idx + 1) * self.entry_size(layer)
        indexing::next_entry_base_from_index(base, idx, self.entry_size(layer))
    }

    pub proof fn lemma_entry_sizes_increase(self, i: nat, j: nat)
        requires
            self.inv(),
            i < j,
            j < self.layers.len(),
        ensures
            self.entry_size(i) >= self.entry_size(j),
        decreases j - i
    {
        assert(self.entry_size(i) >= self.entry_size(i + 1))
            by (nonlinear_arith)
            requires
                i + 1 < self.layers.len(),
                self.entry_size_is_next_layer_size(i),
                self.num_entries(i + 1) > 0,
        { };
        if j == i + 1 {
        } else {
            self.lemma_entry_sizes_increase(i + 1, j);

        }
    }
}

// Why does this exec_spec function even exist:
// - In some places we need to refer to the `Exec` versions of the structs in spec mode.
// - We can't make x86_arch_exec a const because Verus panics if we initialize the vec directly,
//   i.e. we need to push to a mut vec instead. (Does rust even support vecs in a const? Otherwise
//   would need arrays.)
// - Since x86_arch_exec is a function it has to have a mode, i.e. we need a version for exec usage
//   and a version for spec usage. In the spec version we can't initialize the vec (same problem as
//   above and can't use mut), i.e. we have to axiomatize their equivalence.
// - We can't even have a proof function axiom because we need to show
//   `x86_arch_exec_spec() == x86_arch_exec()`, where the second function call is an exec function.
//   Thus the axiom is an assumed postcondition on the exec function itself.
// - In addition to adding the postcondition, we also need a separate axiom to show that the view
//   of x86_arch_exec_spec is the same as x86_arch_spec. This is provable but only with the
//   postconditions on x86_arch_exec, which is an exec function. Consequently we can't use that
//   postcondition in proof mode.
// - All this mess should go away as soon as we can make that exec function the constant it ought
//   to be.
pub open spec fn x86_arch_exec_spec() -> ArchExec;

#[verifier(external_body)]
pub proof fn axiom_x86_arch_exec_spec()
    ensures
        x86_arch_exec_spec()@ == x86_arch_spec;

pub exec fn x86_arch_exec() -> (res: ArchExec)
    ensures
        res.layers@ == seq![
            ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 },
            ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 },
        ],
        res@ === x86_arch_spec,
        res === x86_arch_exec_spec(),
{
    // Can we somehow just initialize an immutable vec directly? Verus panics when I try do so
    // (unless the function is external_body).
    let mut v = Vec::new();
    v.push(ArchLayerExec { entry_size: L0_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L1_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L2_ENTRY_SIZE, num_entries: 512 });
    v.push(ArchLayerExec { entry_size: L3_ENTRY_SIZE, num_entries: 512 });
    let res = ArchExec {
        layers: v,
    };
    proof {
        assert_seqs_equal!(res@.layers, x86_arch_spec.layers);
        // This is an axiom to establish the equivalence with x86_arch_exec_spec; See comments
        // further up for explanation why this workaround is necessary.
        assume(res === x86_arch_exec_spec());
    }
    res
}

pub spec const x86_arch_spec: Arch = Arch {
    layers: seq![
        ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
    ],
};

#[verifier(nonlinear)]
pub proof fn x86_arch_inv()
    ensures
        x86_arch_spec.inv()
{
    assert(x86_arch_spec.entry_size(3) == 4096);
    assert(x86_arch_spec.contains_entry_size(4096));
    assert(x86_arch_spec.layers.len() <= X86_NUM_LAYERS);
    assert forall|i:nat| i < x86_arch_spec.layers.len() implies {
            &&& 0 < #[trigger] x86_arch_spec.entry_size(i)  <= X86_MAX_ENTRY_SIZE
            &&& 0 < #[trigger] x86_arch_spec.num_entries(i) <= X86_NUM_ENTRIES
            &&& x86_arch_spec.entry_size_is_next_layer_size(i)
        } by {
        assert(0 < #[trigger] x86_arch_spec.entry_size(i)  <= X86_MAX_ENTRY_SIZE);
        assert(0 < #[trigger] x86_arch_spec.num_entries(i) <= X86_NUM_ENTRIES);
        assert(x86_arch_spec.entry_size_is_next_layer_size(i));
    }
    assert(x86_arch_spec.inv());
}

}
