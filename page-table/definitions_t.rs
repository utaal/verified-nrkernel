#![verus::trusted]

// trusted: these are used in trusted definitions
// 
// `overlap_sanity_check` hardens a spec, so we don't count it as trusted

use vstd::prelude::*;

verus! {

macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0u64 << (($high+1u64)-$low))) << $low
    }
}
pub(crate) use bitmask_inc;

macro_rules! bit {
    ($v:expr) => {
        1u64 << $v
    }
}
pub(crate) use bit;

pub const X86_NUM_LAYERS:  usize = 4;
pub const X86_NUM_ENTRIES: usize = 512;

// The maximum physical address width is between 32 and 52 bits.
#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: u64 = unimplemented!();

#[verifier(external_body)]
pub proof fn axiom_max_phyaddr_width_facts()
    ensures 32 <= MAX_PHYADDR_WIDTH <= 52;

// We cannot use a dual exec/spec constant for MAX_PHYADDR, because for those Verus currently
// doesn't support manually guiding the no-overflow proofs.
pub spec const MAX_PHYADDR_SPEC: u64 = ((1u64 << MAX_PHYADDR_WIDTH) - 1u64) as u64;
#[verifier::when_used_as_spec(MAX_PHYADDR_SPEC)]
pub exec const MAX_PHYADDR: u64 ensures MAX_PHYADDR == MAX_PHYADDR_SPEC {
    axiom_max_phyaddr_width_facts();
    assert(1u64 << 32 == 0x100000000) by (compute);
    assert(forall|m:u64,n:u64|  n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
    (1u64 << MAX_PHYADDR_WIDTH) - 1u64
}

pub const WORD_SIZE: usize = 8;
pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;
pub spec const MAX_BASE:           nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

pub spec const PT_BOUND_LOW:  nat = 0;
// Upper bound for x86 4-level paging.
// 512 entries, each mapping 512*1024*1024*1024 bytes
pub const PT_BOUND_HIGH: usize = 512 * 512 * 1024 * 1024 * 1024;
pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;
pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;
pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;
pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends
        entry_size > 0,
{
    offset / entry_size
}

pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}


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
        new_seq((i-1) as nat, e).push(e)
    }
}

pub enum LoadResult {
    Pagefault,
    Value(nat), // word-sized load
}

pub enum StoreResult {
    Pagefault,
    Ok,
}

#[allow(inconsistent_fields)]
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

// hardens spec for overlap
#[verus::line_count::ignore]
proof fn overlap_sanity_check() {
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

pub ghost struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
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

    #[verifier(inline)]
    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
        index_from_base_and_addr(base, vaddr, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        // base + idx * self.entry_size(layer)
        entry_base_from_index(base, idx, self.entry_size(layer))
    }

    #[verifier(inline)]
    pub open spec(checked) fn next_entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len()
    {
        // base + (idx + 1) * self.entry_size(layer)
        next_entry_base_from_index(base, idx, self.entry_size(layer))
    }
}

pub struct ArchLayerExec {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: usize,
    /// Number of entries of at this layer
    pub num_entries: usize,
}

pub struct ArchExec {
    // TODO: This could probably be an array, once we have support for that
    pub layers: Vec<ArchLayerExec>,
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
        assert(res@.layers =~= x86_arch_spec.layers);
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

}
