use vstd::prelude::*;

use crate::definitions_t::{MAX_PHYADDR, axiom_max_phyaddr_width_facts, aligned, new_seq, Flags, ArchExec, ArchLayerExec};

verus! {
pub proof fn lemma_maxphyaddr_facts()
    ensures 0xFFFFFFFF <= MAX_PHYADDR <= 0xFFFFFFFFFFFFF
{
    axiom_max_phyaddr_width_facts();
    assert(1u64 << 32 == 0x100000000) by (compute);
    assert(1u64 << 52 == 0x10000000000000) by (compute);
    assert(forall|m:u64,n:u64|  n < m < 64 ==> 1u64 << n < 1u64 << m) by (bit_vector);
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

pub exec fn aligned_exec(addr: usize, size: usize) -> (res: bool)
    requires
        size > 0
    ensures
        res == aligned(addr as nat, size as nat)
{
    addr % size == 0
}

/// We always set permissive flags on directories. Restrictions happen on the frame mapping.
pub spec const permissive_flags: Flags = Flags {
    is_writable:     true,
    is_supervisor:   false,
    disable_execute: false,
};

// Sometimes z3 needs these concrete bounds to prove the no-overflow VC
pub proof fn overflow_bounds()
    ensures
        X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
        MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000,
{
    assert(X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
    assert(MAX_BASE + X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES + 1) < 0x10000000000000000) by (nonlinear_arith);
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

use crate::definitions_t::{Arch, ArchLayer, MAX_BASE, X86_MAX_ENTRY_SIZE, X86_NUM_ENTRIES, x86_arch_spec, X86_NUM_LAYERS};

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
            res == crate::definitions_t::index_from_base_and_addr(base as nat, vaddr as nat, self@.entry_size(layer as nat)),
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
            crate::extra::mult_leq_mono_both(idx as nat, self@.entry_size(layer as nat), X86_NUM_ENTRIES as nat, 512 * 1024 * 1024 * 1024);
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

impl Arch {
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
            assert(forall|a: int, b: int| #[trigger] (a * b) == b * a);
            self.lemma_entry_sizes_aligned(i+1,j);
            assert(aligned(self.entry_size(i+1), self.entry_size(j)));
            assert(self.entry_size(i) % self.entry_size(i + 1) == 0) by {
                // assert(self.inv());
                // assert(self.entry_size_is_next_layer_size(i));
                // assert(self.entry_size_is_next_layer_size(i + 1));
                // assert(self.entry_size(i) == self.entry_size((i + 1) as nat) * self.num_entries((i + 1) as nat));
                assert(self.entry_size(i) % self.entry_size(i + 1) == 0) by (nonlinear_arith)
                    requires i != j, self.entry_size(i) > 0, self.entry_size(i + 1) > 0,
                    self.entry_size(i) == self.entry_size((i + 1) as nat) * self.num_entries((i + 1) as nat),
                { };

            };
            assert(aligned(self.entry_size(i), self.entry_size(i+1)));
            crate::extra::aligned_transitive(self.entry_size(i), self.entry_size(i+1), self.entry_size(j));
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

