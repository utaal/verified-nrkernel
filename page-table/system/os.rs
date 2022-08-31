#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;
use map::*;
use seq::*;

use crate::system::spec as system;
use crate::pt;
use crate::aux_defs::{ between, MemRegion, overlap, PageTableEntry, IoOp, MapResult, UnmapResult, Arch, aligned, new_seq, candidate_mapping_overlaps_existing_mapping };
use crate::aux_defs::{ PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE, L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE, WORD_SIZE };
use crate::high_level_spec as hlspec;
use crate::mem::{ word_index_spec };
use option::{ *, Option::* };

verus! {

pub struct OSVariables {
    pub system: system::SystemVariables,
}

impl OSVariables {
    pub open spec fn inv(self) -> bool {
        self.pt_variables().inv()
    }

    pub open spec fn pt_variables(self) -> pt::PageTableVariables {
        pt::PageTableVariables {
            map: self.interp_mappings(),
        }
    }

    pub open spec fn interp_mappings(self) -> Map<nat, PageTableEntry> {
        system::interp_pt_mem(self.system.pt_mem)
    }

    pub open spec fn interp(self) -> hlspec::AbstractVariables {
        let mappings = self.interp_mappings();
        let mem: Map<nat,nat> = Map::new(
            |word_idx: nat| hlspec::mem_domain_from_mappings_contains(word_idx, mappings),
            |word_idx: nat| {
                let vaddr = word_idx * WORD_SIZE;
                let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
                let phys_addr = (pte.frame.base + (vaddr - base)) as nat;
                self.system.mem[phys_addr]
            });
        hlspec::AbstractVariables {
            mem,
            mappings,
        }
    }

    proof fn lemma_interp(self, other: OSVariables)
        requires
            other.system.mem === self.system.mem,
            forall|base, pte| self.interp_mappings().contains_pair(base, pte) ==> other.interp_mappings().contains_pair(base, pte),
            self.inv(),
            other.inv(),
        ensures
            forall|word_idx: nat|
                self.interp().mem.dom().contains(word_idx)
                ==> {
                    &&& #[trigger] other.interp().mem.dom().contains(word_idx)
                    &&& other.interp().mem[word_idx] == self.interp().mem[word_idx]
                },
    {
        assert forall|word_idx: nat|
            self.interp().mem.dom().contains(word_idx)
            implies {
                &&& #[trigger] other.interp().mem.dom().contains(word_idx)
                &&& other.interp().mem[word_idx] == self.interp().mem[word_idx]
            } by
        {
            let vaddr = word_idx * WORD_SIZE;
            let self_mappings = self.interp_mappings();
            let other_mappings = other.interp_mappings();
            assert(hlspec::mem_domain_from_mappings_contains(word_idx, self_mappings));
            let (base, pte): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] self_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
            assert(self_mappings.contains_pair(base, pte));
            assert(between(vaddr, base, base + pte.frame.size));
            assert(other_mappings.contains_pair(base, pte));

            assert(other.interp().mem.dom().contains(word_idx));
            if other.interp().mem[word_idx] !== self.interp().mem[word_idx] {
                let (base2, pte2): (nat, PageTableEntry) = choose|base: nat, pte: PageTableEntry| #![auto] other_mappings.contains_pair(base, pte) && between(vaddr, base, base + pte.frame.size);
                assert(other_mappings.contains_pair(base, pte));
                assert(other_mappings.contains_pair(base2, pte2));
                assert(between(vaddr, base2, base2 + pte2.frame.size));
                assert(overlap(
                        MemRegion { base: base, size: base + pte.frame.size },
                        MemRegion { base: base2, size: base2 + pte2.frame.size }));
                assert(other.pt_variables().mappings_dont_overlap());
                assert(((base == base2) || !overlap(
                               MemRegion { base: base, size: pte.frame.size },
                               MemRegion { base: base2, size: pte2.frame.size })));
                assert(base != base2);
                assert(false);
            }
        };
    }
}

pub open spec fn step_System(s1: OSVariables, s2: OSVariables, system_step: system::SystemStep) -> bool {
    &&& !system_step.is_PTMemOp()
    &&& system::next_step(s1.system, s2.system, system_step)
    &&& pt::step_Stutter(s1.pt_variables(), s2.pt_variables())
}

pub open spec fn step_Map(s1: OSVariables, s2: OSVariables, base: nat, pte: PageTableEntry, result: MapResult) -> bool {
    &&& system::step_PTMemOp(s1.system, s2.system)
    &&& pt::step_Map(s1.pt_variables(), s2.pt_variables(), base, pte, result)
}

pub open spec fn step_Unmap(s1: OSVariables, s2: OSVariables, base: nat, result: UnmapResult) -> bool {
    // &&& s1.system.tlb
    &&& system::step_PTMemOp(s1.system, s2.system)
    &&& pt::step_Unmap(s1.pt_variables(), s2.pt_variables(), base, result)
}

pub enum OSStep {
    System { step: system::SystemStep },
    Map    { base: nat, pte: PageTableEntry, result: MapResult },
    Unmap  { base: nat, result: UnmapResult },
}

impl OSStep {
    pub open spec fn interp(self) -> hlspec::AbstractStep {
        match self {
            OSStep::System { step } =>
                match step {
                    system::SystemStep::IoOp { vaddr, paddr, op, pte } => hlspec::AbstractStep::IoOp { vaddr, op, pte },
                    system::SystemStep::PTMemOp                        => arbitrary(),
                    system::SystemStep::TLBFill { base, pte }          => hlspec::AbstractStep::Stutter,
                    system::SystemStep::TLBEvict { base }              => hlspec::AbstractStep::Stutter,
                },
            OSStep::Map    { base, pte, result } => hlspec::AbstractStep::Map { base, pte, result },
            OSStep::Unmap  { base, result } => hlspec::AbstractStep::Unmap { base, result },
        }
    }
}

pub open spec fn next_step(s1: OSVariables, s2: OSVariables, step: OSStep) -> bool {
    match step {
        OSStep::System { step }              => step_System(s1, s2, step),
        OSStep::Map    { base, pte, result } => step_Map(s1, s2, base, pte, result),
        OSStep::Unmap  { base, result }      => step_Unmap(s1, s2, base, result),
    }
}

pub open spec fn next(s1: OSVariables, s2: OSVariables) -> bool {
    exists|step: OSStep| next_step(s1, s2, step)
}

proof fn next_step_refines_hl_next_step(s1: OSVariables, s2: OSVariables, step: OSStep)
    requires
        s1.inv(),
        next_step(s1, s2, step)
    ensures
        hlspec::next_step(s1.interp(), s2.interp(), step.interp())
{
    // FIXME:
    assume(false);
    assume(s2.inv());
    let abs_s1   = s1.interp();
    let abs_s2   = s2.interp();
    let abs_step = step.interp();
    match step {
        OSStep::System { step } =>
            match step {
                system::SystemStep::IoOp { vaddr, paddr, op, pte } => {
                    // hlspec::AbstractStep::IoOp { vaddr, op, pte }
                    let mem_idx = word_index_spec(vaddr);
                    assert(s2.system.pt_mem === s1.system.pt_mem);
                    assert(s2.system.tlb === s1.system.tlb);
                    match pte {
                        Some((base, pte)) => {
                            // system
                            assert(s1.system.tlb.contains_pair(base, pte));
                            assert(between(vaddr, base, base + pte.frame.size));
                            assert(paddr === (pte.frame.base + (vaddr - base)) as nat);

                            // abs
                            assert(abs_s1.mappings.contains_pair(base, pte));
                            match op {
                                IoOp::Store { new_value, result } => {
                                    if !pte.flags.is_supervisor && pte.flags.is_writable {
                                        assert(result.is_Ok());
                                        assert(s2.system.mem === s1.system.mem.update(mem_idx, new_value));
                                        assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(s2.system.mem === s1.system.mem);
                                        assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                                IoOp::Load { is_exec, result } => {
                                    assert(s2.system.mem === s1.system.mem);
                                    if !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                                        assert(result.is_Value());
                                        assert(result.get_Value_0() == s1.system.mem.index(mem_idx));
                                        assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    } else {
                                        assert(result.is_Pagefault());
                                        assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, Some((base, pte))));
                                    }
                                },
                            }
                        },
                        None => {
                            assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, pte));
                        },
                    }
                    assert(hlspec::step_IoOp(abs_s1, abs_s2, vaddr, op, pte));
                    assert(hlspec::next_step(abs_s1, abs_s2, abs_step));
                },
                system::SystemStep::PTMemOp => assert(false),
                system::SystemStep::TLBFill { base, pte } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
                system::SystemStep::TLBEvict { base } => {
                    // hlspec::AbstractStep::Stutter
                    assert(abs_s2 === abs_s1);
                },
            },
        OSStep::Map { base, pte, result } => {
            // hlspec::AbstractStep::Map { base, pte }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Map { base, pte, result });
            assert(step_Map(s1, s2, base, pte, result));
            assert(pt::step_Map(pt_s1, pt_s2, base, pte, result));
            assert(hlspec::step_Map_preconditions(base, pte));
            if candidate_mapping_overlaps_existing_mapping(pt_s1.map, base, pte) {
                assert(candidate_mapping_overlaps_existing_mapping(abs_s1.mappings, base, pte));
                assert(hlspec::step_Map(abs_s1, abs_s2, base, pte, result));
            } else {
                assert(!candidate_mapping_overlaps_existing_mapping(abs_s1.mappings, base, pte));
                // hlspec::lemma_mem_domain_from_mappings();
                assert(forall|base, pte| s1.interp_mappings().contains_pair(base, pte) ==> s2.interp_mappings().contains_pair(base, pte));
                assert(forall|base, pte| s1.interp().mappings.contains_pair(base, pte) ==> s2.interp().mappings.contains_pair(base, pte));
                assert(s1.interp().mappings === s1.interp_mappings());
                assert(s2.interp().mappings === s2.interp_mappings());
                s1.lemma_interp(s2);
                assert(result.is_Ok());
                assert(abs_s2.mappings === abs_s1.mappings.insert(base, pte));
                assert forall|word_idx|
                    #[trigger] abs_s1.mem.dom().contains(word_idx)
                    implies abs_s2.mem[word_idx] === abs_s1.mem[word_idx] by
                {
                    assert(abs_s2.mem.dom().contains(word_idx));
                    assert(abs_s2.mem[word_idx] == abs_s1.mem[word_idx]);
                };
                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(abs_s2.mappings));
                assert(hlspec::step_Map(abs_s1, abs_s2, base, pte, result));
            }
            assert(hlspec::next_step(abs_s1, abs_s2, abs_step));

        },
        OSStep::Unmap { base, result } => {
            // hlspec::AbstractStep::Unmap { base }
            let pt_s1 = s1.pt_variables();
            let pt_s2 = s2.pt_variables();
            assert(abs_step === hlspec::AbstractStep::Unmap { base, result });
            assert(step_Unmap(s1, s2, base, result));
            assert(pt::step_Unmap(pt_s1, pt_s2, base, result));
            assert(hlspec::step_Unmap_preconditions(base));
            if pt_s1.map.dom().contains(base) {
                assert(abs_s1.mappings.dom().contains(base));
                assert(result.is_Ok());
                assert(pt_s2.map === pt_s1.map.remove(base));
                assert(abs_s2.mappings === abs_s1.mappings.remove(base));

                assert(abs_s2.mem.dom() === hlspec::mem_domain_from_mappings(abs_s2.mappings));
                s2.lemma_interp(s1);
                assert forall|word_idx|
                    #[trigger] abs_s2.mem.dom().contains(word_idx)
                    implies abs_s1.mem[word_idx] === abs_s2.mem[word_idx] by
                {
                    assert(abs_s1.mem.dom().contains(word_idx));
                    assert(abs_s1.mem[word_idx] == abs_s2.mem[word_idx]);
                };

                assert(hlspec::step_Unmap(abs_s1, abs_s2, base, result));
            } else {
                assert(!abs_s1.mappings.dom().contains(base));
                assert(hlspec::step_Unmap(abs_s1, abs_s2, base, result));
            }
            assert(hlspec::step_Unmap(abs_s1, abs_s2, base, result));
            assert(hlspec::next_step(abs_s1, abs_s2, abs_step));
        },
    }
}

// // TODO: Can we add this to pervasive? Push is awkward to use in recursive functions.
// impl<A> Seq<A> {
//     pub open spec fn cons(self, a: A) -> Self;
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_cons_len<A>(s: Seq<A>, a: A)
//     ensures
//         #[trigger] s.cons(a).len() == s.len() + 1,
// {
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_cons_index_same<A>(s: Seq<A>, a: A)
//     ensures
//         #[trigger] s.cons(a).index(0) === a,
// {
// }

// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
//     requires
//         0 < i <= s.len(),
//     ensures
//         s.cons(a)[i] === s[i - 1],
// {
// }

// // exclusive on upper bound
// pub open spec fn enum_from_to(from: nat, to: nat) -> Seq<nat>
//     decreases to + 1 - from
// {
//     if from >= to {
//         seq![]
//     } else {
//         enum_from_to(from + 1, to).cons(from)
//     }
// }

// pub proof fn lemma_enum_from_to(from: nat, to: nat)
//     ensures
//         from <= to ==> enum_from_to(from, to).len() == to - from,
//         from > to ==> enum_from_to(from, to).len() == 0,
//         forall|i: nat|
//             i < enum_from_to(from, to).len() ==> enum_from_to(from, to)[i] == from + i
//     decreases to + 1 - from
// {
//     if from <= to {
//         lemma_enum_from_to(from + 1, to);
//     }
// }

// // TODO: better way of writing this? Maybe directly axiomatize like for Map?
// pub open spec fn new_seq_map_index<T, F: Fn(nat) -> T>(len: nat, f: F) -> Seq<T> {
//     enum_from_to(0, len).map(|idx,i| f(i))
// }

}
