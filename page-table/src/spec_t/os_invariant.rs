use vstd::prelude::*;

//use crate::impl_u::spec_pt;
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{
    candidate_mapping_overlaps_existing_vmem, overlap, MemRegion, PTE, Core, X86_NUM_ENTRIES, new_seq
};
#[cfg(verus_keep_ghost)]
use crate::definitions_u::{ lemma_new_seq };
use crate::spec_t::{hlspec, os};
use crate::spec_t::mmu::rl3::refinement::to_rl1;
use crate::spec_t::mmu;
use crate::theorem::RLbl;
use crate::impl_u::wrapped_token;
use crate::impl_u::l2_impl::{ PTDir, PT };
use crate::spec_t::mmu::rl1;

verus! {

pub proof fn lemma_init_implies_empty_map(s: os::State, c: os::Constants)
    requires os::init(c, s),
    ensures s.interp_pt_mem() === map![]
{
    reveal(crate::spec_t::mmu::pt_mem::PTMem::view);
    assert forall|vaddr| #[trigger] s.mmu@.pt_mem.pt_walk(vaddr).result() is Invalid by {
        crate::impl_u::l2_impl::lemma_bitvector_facts_simple();
        crate::spec_t::mmu::translation::lemma_bit_indices_less_512(vaddr);
    };
    assert(s.interp_pt_mem() =~= map![]);
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Proof of Invariant
///////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_inv(c: os::Constants, s: os::State)
    requires os::init(c, s),
    ensures s.inv(c),
{
    to_rl1::init_implies_inv(s.mmu, c.mmu);
    to_rl1::init_refines(s.mmu, c.mmu);
    assert(s.inv_impl()) by {
        assert forall|wtok: wrapped_token::WrappedTokenView| ({
            &&& wtok.pt_mem == s.mmu@.pt_mem
            &&& wtok.regions.dom() == s.os_ext.allocated
            &&& #[trigger] wtok.regions_derived_from_view()
        })
            implies exists|pt| PT::inv_and_nonempty(wtok, pt)
        by {
            let pml4 = s.mmu@.pt_mem.pml4;
            let region = MemRegion { base: pml4 as nat, size: 4096 };
            let pt =
                PTDir {
                    region,
                    entries: new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None),
                    used_regions: set![region],
                };
            lemma_new_seq::<Option<PTDir>>(X86_NUM_ENTRIES as nat, None);
            assert forall|i: usize| 0 <= i < 512 implies wtok.regions[region][i as int] == 0 by {
                assert(s.mmu@.pt_mem.read(add(pml4, mul(i, 8))) == 0);
            };
            PT::lemma_zeroed_page_implies_empty_at(wtok, pt, 0, pml4);
            assert(PT::inv_and_nonempty(wtok, pt));
        };
    };

    lemma_init_implies_empty_map(s, c);
    assert(s.inv_basic(c));
    init_implies_tlb_inv(c, s);
}

pub proof fn next_preserves_inv(c: os::Constants, s1: os::State, s2: os::State, lbl: RLbl)
    requires
        s1.inv(c),
        os::next(c, s1, s2, lbl),
    ensures
        s2.inv(c),
{
    let step = choose|step| os::next_step(c, s1, s2, step, lbl);
    next_step_preserves_inv(c, s1, s2, step, lbl);
}

pub proof fn next_step_preserves_inv(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    /*
     assert(s2.inv_successful_maps(c)) by {
        assert forall|core| c.valid_core(core) implies {
            match s2.core_states[core] {
                os::CoreState::UnmapExecuting { vaddr, result: Some(_),.. }
                | os::CoreState::UnmapOpDone { vaddr, .. }
                | os::CoreState::UnmapShootdownWaiting { vaddr, .. }
                    => !s2.interp_pt_mem().dom().contains(vaddr),
                _ => true,
            }
        } by { let _ = s1.core_states[core].is_in_crit_sect(); }
    };
    */
    assert(s2.inv_inflight_pte_above_zero_pte_result_consistent(c)) by {
        assert forall|core: Core| c.valid_core(core) implies
            match s2.core_states[core] {
                os::CoreState::MapWaiting { vaddr, pte, .. }
                | os::CoreState::MapExecuting { vaddr, pte, .. }
                | os::CoreState::MapDone { vaddr, pte, .. }
                    => pte.frame.size > 0,
                os::CoreState::UnmapWaiting { vaddr, .. }
                | os::CoreState::UnmapExecuting { vaddr, result: None, .. }
                    => s2.interp_pt_mem().contains_key(vaddr)
                        ==> s2.interp_pt_mem()[vaddr].frame.size > 0,
                os::CoreState::UnmapExecuting { result: Some(result), .. }
                | os::CoreState::UnmapOpDone { result, .. }
                | os::CoreState::UnmapShootdownWaiting { result, .. }
                    => result is Ok ==> result.get_Ok_0().frame.size > 0,
                os::CoreState::Idle => true,
        } by {
            match s2.core_states[core] {
                os::CoreState::MapWaiting { vaddr, pte, .. }
                | os::CoreState::MapExecuting { vaddr, pte, .. }
                | os::CoreState::MapDone { vaddr, pte, .. } => {
                    assert(pte.frame.size > 0);
                },
                os::CoreState::UnmapWaiting { vaddr, .. }
                | os::CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                    if s2.interp_pt_mem().contains_key(vaddr) {
                        assert(s2.interp_pt_mem()[vaddr].frame.size > 0);
                    }
                },
                os::CoreState::UnmapExecuting { result: Some(result), .. }
                | os::CoreState::UnmapOpDone { result, .. }
                | os::CoreState::UnmapShootdownWaiting { result, .. } => {
                    assert(result is Ok ==> result.get_Ok_0().frame.size > 0);
                },
                os::CoreState::Idle => {},
            }
        };
    };

    assert(s2.inv_basic(c));
    next_step_preserves_inv_osext(c, s1, s2, step, lbl);
    //next_step_preserves_tlb_inv(c, s1, s2, step);
    next_step_preserves_overlap_vmem_inv(c, s1, s2, step, lbl);
    next_step_preserves_inv_impl(c, s1, s2, step, lbl);
    next_step_preserves_inv_writes(c, s1, s2, step, lbl);
    next_step_preserves_inv_shootdown(c, s1, s2, step, lbl);
    next_step_preserves_inv_pending_maps(c, s1, s2, step, lbl);
}

pub proof fn next_step_preserves_inv_pending_maps(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_pending_maps(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        // Map steps
        os::Step::MMU => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::MemOp { core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::ReadPTMem { core, paddr, value } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::Barrier { core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::Invlpg { core, vaddr } => {
            assert(s2.inv_pending_maps(c));
        }

        os::Step::MapStart { core } => {
            assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                exists |core| os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps)
            by {
                assert(s1.mmu@.pending_maps.dom().contains(base));
                let core = choose |core| os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps);
                assert(os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps));
                assert(os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps));
            }
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapOpStart { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::Allocate { core, res } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapOpStutter { core, paddr, value }
        | os::Step::UnmapOpChange { core, paddr, value }
        | os::Step::UnmapOpStutter { core, paddr, value } => {
            let mlbl = mmu::Lbl::Write(core, paddr, value);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, step, mlbl);
            assert(rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, mmu_step, mlbl));
            match mmu_step {
                rl1::Step::WriteNonneg => {
                    assert forall |vbase| s2.mmu@.pt_mem@.contains_key(vbase) implies s1.mmu@.pt_mem@.contains_key(vbase)
                    by {
                        assert(s2.interp_pt_mem().dom().contains(vbase as nat));
                        assert(s1.interp_pt_mem().dom().contains(vbase as nat));
                    }
                    assert(s1.mmu@.pending_maps =~= s2.mmu@.pending_maps);
                    assert(s2.inv_pending_maps(c));
                }
                rl1::Step::WriteNonpos => {
                    assert(s2.inv_pending_maps(c));
                }
                _ => {
                    assert(false);
                }
            }
        },
        os::Step::MapOpChange { core, paddr, value } => {
            let mlbl = mmu::Lbl::Write(core, paddr, value);
            let mmu_step = choose|step| rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, step, mlbl);
            assert(rl1::next_step(s1.mmu@, s2.mmu@, c.mmu, mmu_step, mlbl));
            match mmu_step {
                rl1::Step::WriteNonneg => {
                    let vaddr = s1.core_states[core]->MapExecuting_vaddr;
                    let pte = s1.core_states[core]->MapExecuting_pte;
                    assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                        exists |core1| os::State::is_pending_for_core(c, base, core1,
                            s2.core_states, s2.mmu@.pending_maps)
                    by {
                        if base == vaddr {
                            assert(s2.interp_pt_mem().dom().contains(base as nat));
                            assert(s2.interp_pt_mem()[base as nat] == pte);
                            assert(s2.mmu@.pending_maps.dom().contains(base));
                            assert(s2.mmu@.pending_maps[base] == pte);
                            assert(os::State::is_pending_for_core(c, base, core,
                                s2.core_states, s2.mmu@.pending_maps));
                        } else {
                            assert(s2.interp_pt_mem().dom().contains(base as nat));
                            assert(s1.interp_pt_mem().dom().contains(base as nat));
                            assert(s1.mmu@.pending_maps.dom().contains(base));

                            let core1 = choose |core1| os::State::is_pending_for_core(c, base, core1,
                                s1.core_states, s1.mmu@.pending_maps);
                            assert(os::State::is_pending_for_core(c, base, core1,
                                s1.core_states, s1.mmu@.pending_maps));
                            assert(os::State::is_pending_for_core(c, base, core1,
                                s2.core_states, s2.mmu@.pending_maps));
                        }
                    }
                    assert(s2.inv_pending_maps(c));
                }
                rl1::Step::WriteNonpos => {
                    assert(s2.inv_pending_maps(c));
                }
                _ => {
                    assert(false);
                }
            }
        },
        os::Step::MapNoOp { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::MapEnd { core } => {
            assert(s2.inv_pending_maps(c));
        },

        //Unmap steps
        os::Step::UnmapStart { core } => {
            assert forall |base| #[trigger] s2.mmu@.pending_maps.dom().contains(base) implies
                exists |core| os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps)
            by {
                assert(s1.mmu@.pending_maps.dom().contains(base));
                let core = choose |core| os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps);
                assert(os::State::is_pending_for_core(c, base, core,
                    s1.core_states, s1.mmu@.pending_maps));
                assert(os::State::is_pending_for_core(c, base, core,
                    s2.core_states, s2.mmu@.pending_maps));
            }
            assert(s2.inv_pending_maps(c));
        },
        os::Step::UnmapOpStart { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::Deallocate { core: Core, reg: MemRegion } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::UnmapOpFail { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::UnmapInitiateShootdown { core } => {
            assert(s2.inv_pending_maps(c));
        },
        os::Step::AckShootdownIPI { core: Core } => {
            assert(s2.inv_pending_maps(c));
        }
        os::Step::UnmapEnd { core: Core } => {
            assert(s2.inv_pending_maps(c));
        }
    }
}

pub proof fn next_step_preserves_inv_osext(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_osext(),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
}

pub proof fn next_step_preserves_inv_impl(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv_mmu(c),
        s1.inv_lock(c),
        s1.inv_impl(),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_impl(),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
}

pub proof fn next_step_preserves_inv_shootdown(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_shootdown(c),
{
    reveal(crate::spec_t::os_ext::Constants::valid_core);
    reveal(mmu::Constants::valid_core);
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        os::Step::AckShootdownIPI { core } => {
            // TODO: What to do about this one? Need to be careful about adding more enabling
            // conditions on the acks because we don't implement that transition.
            assert(s1.os_ext.shootdown_vec.open_requests.contains(core));
            admit();

        },
        _ => {},
    }
}

pub proof fn next_step_preserves_inv_writes(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_writes(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    match step {
        os::Step::Invlpg { core, vaddr } => {
            assert((s2.os_ext.lock matches Some(core) && s2.core_states[core].is_mapping())
                ==> s2.mmu@.writes.nonpos === set![]);
            assert(s2.os_ext.lock is None ==> {
                &&& s2.mmu@.writes.tso === set![]
                &&& s2.mmu@.writes.nonpos === set![]
            });
            assert(s2.inv_writes(c));
        },
        os::Step::UnmapOpChange { core, paddr, value } => {
            // If I remove this match arm, Verus times out, wtf
        },
        _ => {},
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of TLB Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn init_implies_tlb_inv(c: os::Constants, s: os::State)
    requires os::init(c, s),
    ensures s.tlb_inv(c),
{
    to_rl1::init_refines(s.mmu, c.mmu);
    assert(s.os_ext.shootdown_vec.open_requests.is_empty());
    Set::lemma_len0_is_empty(s.os_ext.shootdown_vec.open_requests);
    assert(s.os_ext.shootdown_vec.open_requests === Set::empty());
    assert(s.shootdown_cores_valid(c));
    assert(s.successful_IPI(c));
    assert(s.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c));
}

pub proof fn next_step_preserves_tlb_inv(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    step: os::Step,
    lbl: RLbl,
)
    requires
        s1.tlb_inv(c),
        s1.inv_basic(c),
        s2.inv_basic(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.tlb_inv(c),
{
    admit();
    
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof of overlapping virtual memory Invariants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn next_step_preserves_overlap_vmem_inv(
    c: os::Constants,
    s1: os::State,
    s2: os::State,
    step: os::Step,
    lbl: RLbl,
)
    requires
        s1.inv(c),
        s2.inv_basic(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.overlapping_vmem_inv(c),
{
    broadcast use
        to_rl1::next_preserves_inv,
        to_rl1::next_refines;
    let _ = s2.interp_pt_mem(); let _ = s1.interp_pt_mem();

    if s2.sound {
        match step {
            // Map steps
            os::Step::MapStart { core } => {
                let thread_id = lbl->MapStart_thread_id;
                let vaddr = lbl->MapStart_vaddr;
                let pte = lbl->MapStart_pte;
                let corestate = os::CoreState::MapWaiting { ult_id: thread_id, vaddr, pte };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::MapOpStart { core } => {
                let vaddr = s1.core_states[core]->MapWaiting_vaddr;
                let pte = s1.core_states[core]->MapWaiting_pte;
                let ult_id = s1.core_states[core]->MapWaiting_ult_id;
                let corestate = os::CoreState::MapExecuting { ult_id, vaddr, pte };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::MapNoOp { core }
            | os::Step::MapOpChange { core, .. } => {
                let vaddr = s1.core_states[core]->MapExecuting_vaddr;
                let ult_id = s1.core_states[core]->MapExecuting_ult_id;
                let pte = s1.core_states[core]->MapExecuting_pte;
                let result = if (step is MapOpChange) { Ok(()) } else { Err(()) };
                let corestate = os::CoreState::MapDone { ult_id, vaddr, pte, result};
                assert(unique_CoreStates(s2.core_states));
                assert forall|state1: os::CoreState, state2: os::CoreState|
                    s2.core_states.values().contains(state1) && s2.core_states.values().contains(state2)
                    && !state1.is_idle() && !state2.is_idle() && overlap(
                        MemRegion {
                            base: state1.vaddr(),
                            size: state1.vmem_pte_size(s2.interp_pt_mem()),
                        },
                        MemRegion {
                            base: state2.vaddr(),
                            size: state2.vmem_pte_size(s2.interp_pt_mem()),
                        },
                    ) implies state1 == state2 by {
                        if state1.vaddr() == vaddr || state2.vaddr() == vaddr {
                            let other = if state1 != corestate { state1 } else { state2 };
                            if other != corestate {
                                assert(overlap(
                                    MemRegion { base: other.vaddr(), size: other.vmem_pte_size(s1.interp_pt_mem()) },
                                    MemRegion {
                                        base: s1.core_states[core].vaddr(),
                                        size: s1.core_states[core].vmem_pte_size(s1.interp_pt_mem()),
                                    },
                                ));
                                let other_core = choose|b|
                                    #![auto]
                                    s1.core_states.insert(core, corestate).dom().contains(b) && s1.core_states[b] == other
                                        && b != core;
                                assert(s1.core_states.remove(core).dom().contains(other_core));
                                assert(false);
                            }
                        } else {
                            if s1.interp_pt_mem().dom().contains(state1.vaddr()) {
                                assert(overlap(
                                    MemRegion {
                                        base: state1.vaddr(),
                                        size: state1.vmem_pte_size(s1.interp_pt_mem()),
                                    },
                                    MemRegion {
                                        base: state2.vaddr(),
                                        size: state2.vmem_pte_size(s1.interp_pt_mem()),
                                    },
                                ));
                            } else {
                                assert(!s2.interp_pt_mem().dom().contains(state1.vaddr()));
                            }
                        }
                    }
                assert(no_overlap_vmem_values(s2.core_states, s2.interp_pt_mem()));

                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.inflight_map_no_overlap_inflight_vmem(c));


                assert forall|x, y| #![auto] (s2.interp_pt_mem().contains_key(x) && s2.interp_pt_mem().remove(x).dom().contains(y))
                implies ( !overlap(
                    MemRegion { base: x, size: s2.interp_pt_mem()[x].frame.size },
                    MemRegion { base: y, size:  s2.interp_pt_mem().remove(x)[y].frame.size })) by
                {   if ( x != vaddr &&  y != vaddr ) {
                    assert(x != y);
                    assert(s1.interp_pt_mem().dom().contains(x));
                    assert(s1.interp_pt_mem().dom().contains(y));
                    assert(!s1.interp_pt_mem().remove(x).dom().contains(y) || !overlap(
                        MemRegion { base: x, size: s1.interp_pt_mem()[x].frame.size },
                        MemRegion { base: y, size:  s1.interp_pt_mem().remove(x)[y].frame.size }));
                } 
                }
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            //Unmap steps
            os::Step::UnmapStart { core } => {
                let ult_id = lbl->UnmapStart_thread_id;
                let vaddr = lbl->UnmapStart_vaddr;
                let corestate = os::CoreState::UnmapWaiting { ult_id, vaddr };
                lemma_insert_no_overlap_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapOpStart { core } => {
                let vaddr = s1.core_states[core]->UnmapWaiting_vaddr;
                let ult_id = s1.core_states[core]->UnmapWaiting_ult_id;
                let corestate = os::CoreState::UnmapExecuting { ult_id, vaddr, result: None };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapOpChange { core, .. } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
                
                let pt = s1.interp_pt_mem();
                //proofgoal (1/2):  assert(s2.inflight_map_no_overlap_inflight_vmem(c));
                assert( s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));
                assert( s1.core_states[core].vmem_pte_size(s1.interp_pt_mem()) >= s2.core_states[core].vmem_pte_size(s2.interp_pt_mem()));
                lemma_insert_preserves_no_overlap(c, s1.core_states, s1.interp_pt_mem(), core, s2.core_states[core]);
                assert forall|state1, state2| 
                    s2.core_states.values().contains(state1) && s2.core_states.values().contains(state2)
                    && !state1.is_idle() && !state2.is_idle() && overlap(
                        MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
                        MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
                    ) implies state1 == state2 
                by {
                    if (state1 === s2.core_states[core] || state2 == s2.core_states[core]) {
                        let other_state = if state1 === s2.core_states[core] {state2} else {state1};
                    }
                }
                lemma_submap_preserves_no_overlap(c, s2.core_states, s1.interp_pt_mem(), s2.interp_pt_mem());
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.interp_pt_mem().submap_of(s1.interp_pt_mem()));
                assert forall|base| #[trigger] s2.interp_pt_mem().dom().contains(base) implies
                    !candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base])
                by {
                    assert(s2.interp_pt_mem().dom().contains(base));
                    if candidate_mapping_overlaps_existing_vmem(
                        s2.interp_pt_mem().remove(base),
                        base,
                        s2.interp_pt_mem()[base],
                    ) {
                        let overlap_vaddr = choose|b: nat| #![auto] {
                            &&& s2.interp_pt_mem().remove(base).dom().contains(b)
                            &&& overlap(
                                MemRegion {
                                    base: base,
                                    size: s2.interp_pt_mem()[base].frame.size,
                                },
                                MemRegion { base: b, size: s2.interp_pt_mem()[b].frame.size },
                            )
                        };
                        assert(s1.interp_pt_mem().remove(base).dom().contains(overlap_vaddr));
                        // assert(s1.existing_map_no_overlap_existing_vmem(c));
                        assert(false);
                    }
                }
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapOpFail { core } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
                let corestate = os::CoreState::UnmapOpDone { ult_id, vaddr, result: Err(()) };
                lemma_insert_preserves_no_overlap(
                    c,
                    s1.core_states,
                    s1.interp_pt_mem(),
                    core,
                    corestate,
                );
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            os::Step::UnmapInitiateShootdown { core } => {
                let vaddr = s1.core_states[core]->UnmapExecuting_vaddr;
                let ult_id = s1.core_states[core]->UnmapExecuting_ult_id;
                let result = s1.core_states[core]->UnmapExecuting_result;
                let corestate = os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result: result->Some_0 };
                lemma_insert_preserves_no_overlap(c, s1.core_states, s1.interp_pt_mem(), core, corestate);
                lemma_unique_and_overlap_values_implies_overlap_vmem(c, s2);
                assert(s2.existing_map_no_overlap_existing_vmem(c));
            },
            _ => {},
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Alternative Definition for inflight_map_no_overlap_inflight_vmem and Equivalence proof
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub open spec fn unique_CoreStates(map: Map<Core, os::CoreState>) -> bool {
    forall|core| #![auto] map.contains_key(core) && !map[core].is_idle()
        ==> !map.remove(core).values().contains(map[core])
}

pub open spec fn no_overlap_vmem_values(
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
) -> bool {
    forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) ==> state1 == state2
}

//pub proof fn lemma_overlapping_inv_implies_unique_and_overlap_values(
//    c: os::Constants,
//    s: os::State,
//)
//    requires
//        s.inv_basic(c),
//        s.inflight_map_no_overlap_inflight_vmem(c),
//    ensures
//        unique_CoreStates(s.core_states),
//        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
//{
//}

pub proof fn lemma_unique_and_overlap_values_implies_overlap_vmem(
    c: os::Constants,
    s: os::State,
)
    requires
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
        s.inv_basic(c),
    ensures
        s.inflight_map_no_overlap_inflight_vmem(c),
{
    assert(forall|core| #[trigger] c.valid_core(core) ==> s.core_states.contains_key(core));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Lemmata to help proof inflight_map_no_overlap_inflight_vmem
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//pub proof fn lemma_insert_idle_corestate_preserves_no_overlap(
//    c: os::Constants,
//    core_states: Map<Core, os::CoreState>,
//    pt: Map<nat, PTE>,
//    core: Core,
//)
//    requires
//        core_states.dom().contains(core),
//        unique_CoreStates(core_states),
//        no_overlap_vmem_values(core_states, pt),
//    ensures
//        unique_CoreStates(core_states.insert(core, os::CoreState::Idle)),
//        no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt),
//{
//    assert forall|a|
//        #![auto]
//        core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() implies !core_states.insert(core, os::CoreState::Idle).remove(
//        a,
//    ).values().contains(core_states.insert(core, os::CoreState::Idle).index(a)) by {
//        if core_states.insert(core, os::CoreState::Idle).dom().contains(a) && !core_states.insert(
//            core,
//            os::CoreState::Idle,
//        ).index(a).is_idle() && a != core {
//            assert(core_states.dom().contains(a));
//            assert(core_states.index(a) == core_states.insert(core, os::CoreState::Idle).index(a));
//            assert(!core_states.index(a).is_idle());
//            assert(!core_states.remove(a).values().contains(core_states.index(a)));
//
//            assert(core_states.insert(core, os::CoreState::Idle).remove(a) =~= core_states.remove(
//                a,
//            ).insert(core, os::CoreState::Idle));
//
//            lemma_map_insert_values_equality(core_states.remove(a), core, os::CoreState::Idle);
//        }
//    };
//    assert(no_overlap_vmem_values(core_states.insert(core, os::CoreState::Idle), pt));
//}

pub proof fn lemma_insert_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    new_cs: os::CoreState,
)
    requires
        new_cs.is_in_crit_sect(),
        forall|cr| #![auto] core_states.dom().contains(cr) && core_states[cr].is_in_crit_sect() ==> cr == core,
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        !core_states[core].is_idle(),
        !new_cs.is_idle(),
        core_states[core].vaddr() == new_cs.vaddr(),
        core_states[core].vmem_pte_size(pt) >= new_cs.vmem_pte_size(pt),
        core_states[core] != new_cs,
    ensures
        unique_CoreStates(core_states.insert(core, new_cs)),
        no_overlap_vmem_values(core_states.insert(core, new_cs), pt),
{
    assert forall|a| #![auto]
        core_states.insert(core, new_cs).dom().contains(a) && !core_states.insert(core, new_cs)[a].is_idle()
        implies !core_states.insert(core, new_cs).remove(a).values().contains(core_states.insert(core, new_cs).index(a))
    by {
        if a != core {
            assert(!core_states[a].is_in_crit_sect());
            if core_states.insert(core, new_cs).remove(a).values().contains(core_states.insert(core, new_cs)[a]) {
                let same_core = choose|cr| #![auto]
                    core_states.insert(core, new_cs).dom().contains(cr) && core_states.insert(
                        core,
                        new_cs,
                    )[cr] == core_states.insert(core, new_cs)[a] && cr != a;
                assert(core_states.remove(a).dom().contains(same_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, new_cs).values().contains(state1) && core_states.insert(
            core,
            new_cs,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) implies state1 == state2 by {
        if state1 == new_cs || state2 == new_cs {
            let other = if state1 != new_cs { state1 } else { state2 };
            if other != new_cs {
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.vmem_pte_size(pt) },
                    MemRegion {
                        base: core_states[core].vaddr(),
                        size: core_states[core].vmem_pte_size(pt),
                    },
                ));
                let other_core = choose|b|
                    #![auto]
                    core_states.insert(core, new_cs).dom().contains(b) && core_states[b] == other
                        && b != core;
                assert(core_states.remove(core).dom().contains(other_core));
                assert(false);
            }
        }
    }
}

pub proof fn lemma_insert_no_overlap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    corestate: os::CoreState,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        core_states[core].is_idle(),
        !corestate.is_idle(),
        !os::candidate_mapping_overlaps_inflight_vmem(
            pt,
            core_states.values(),
            corestate.vaddr(),
            corestate.vmem_pte_size(pt),
        ),
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(core_states.insert(core, corestate), pt),
{
    assert forall|a| #![auto]
        core_states.insert(core, corestate).dom().contains(a)
        && !core_states.insert(core, corestate)[a].is_idle()
        implies !core_states.insert(core, corestate).remove(a).values()
                            .contains(core_states.insert(core, corestate)[a])
    by {
        if core_states.insert(core, corestate).remove(a).values().contains(
            core_states.insert(core, corestate)[a],
        ) {
            let some_core = choose|cr|
                #![auto]
                cr != a && core_states.insert(core, corestate).dom().contains(cr)
                    && core_states.insert(core, corestate)[cr] == core_states.insert(
                    core,
                    corestate,
                )[a];
            if a == core || some_core == core {
                let other = if some_core != core { some_core } else { a };
                assert(core_states.values().contains(core_states[other]));
                assert(overlap(
                    MemRegion {
                        base: core_states[other].vaddr(),
                        size: core_states[other].vmem_pte_size(pt),
                    },
                    MemRegion { base: corestate.vaddr(), size: corestate.vmem_pte_size(pt) },
                ));
            } else {
                assert(core_states.remove(a).dom().contains(some_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, corestate).values().contains(state1) && core_states.insert(
            core,
            corestate,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ) implies state1 == state2 by {
        if state1 == corestate || state2 == corestate {
            let other = if state1 != corestate {
                state1
            } else {
                state2
            };
            if other != corestate {
                assert(core_states.values().contains(other));
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.vmem_pte_size(pt) },
                    MemRegion { base: corestate.vaddr(), size: corestate.vmem_pte_size(pt) },
                ));
                assert(false);
            }
        }
    }
}

pub proof fn lemma_submap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    sub_pt: Map<nat, PTE>,
)
    requires
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        sub_pt.submap_of(pt),
    ensures
        no_overlap_vmem_values(core_states, sub_pt),
{
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(sub_pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(sub_pt) },
        ) implies state1 == state2 by {
        assert(overlap(
            MemRegion { base: state1.vaddr(), size: state1.vmem_pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.vmem_pte_size(pt) },
        ));
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// soundness lemmata
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_os_implies_hl(
    c: os::Constants,
    s: os::State,
    base: nat,
    candidate_size: nat,
)
    requires
        s.inv_basic(c),
    ensures
        os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    )) by {
        if os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ) {
            let corestate = choose|b: os::CoreState| #![auto]
                {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. }
                        | os::CoreState::MapDone { vaddr, pte, .. } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapWaiting { vaddr, .. }
                        | os::CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                            let size = if s.interp_pt_mem().dom().contains(vaddr) {
                                s.interp_pt_mem().index(vaddr).frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        os::CoreState::UnmapExecuting { vaddr, result: Some(result), .. }
                        | os::CoreState::UnmapOpDone { vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { vaddr, result, .. } => {
                            let size = if result is Ok {
                                result.get_Ok_0().frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        _ => { false },
                    }
                };
            let core = choose|core| #[trigger] c.valid_core(core) && s.core_states[core] == corestate;
            match corestate {
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapDone { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                },
                os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    //assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.contains_key(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    //if result is Ok {}
                },
                _ => {},
            };
        } 
    };
}

pub proof fn lemma_candidate_mapping_inflight_vmem_overlap_hl_implies_os(
    c: os::Constants,
    s: os::State,
    base: nat,
    candidate_size: nat,
)
    requires
        s.inv_basic(c),
    ensures
        hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ) ==> os::candidate_mapping_overlaps_inflight_vmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            base,
            candidate_size,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_vmem(
        s.interp(c).thread_state.values(),
        base,
        candidate_size,
    ) ==> os::candidate_mapping_overlaps_inflight_vmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        base,
        candidate_size,
    )) by {
        if hlspec::candidate_mapping_overlaps_inflight_vmem(
            s.interp(c).thread_state.values(),
            base,
            candidate_size,
        ) {
            let thread_state = choose|b|
                {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(
                                MemRegion { base: vaddr, size: pte.frame.size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
                            let size = if pte.is_some() {
                                pte.unwrap().frame.size
                            } else {
                                0
                            };
                            overlap(
                                MemRegion { base: vaddr, size: size },
                                MemRegion { base: base, size: candidate_size },
                            )
                        },
                        _ => { false },
                    }
                };
            let ult_id = choose|id| #[trigger] c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(c.valid_core(core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id2 == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    ));
                },
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(ult_id2 == ult_id);
                    if s.interp_pt_mem().dom().contains(vaddr) {
                        let pte = s.interp_pt_mem()[vaddr];
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: Some(entry),
                            }
                            &&& vaddr === v_addr
                            &&& entry === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: pte.frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    }
                },
                os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    if result is Ok {
                        assert(ult_id2 == ult_id);
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: Some(pte),
                            }
                            &&& vaddr === v_addr
                            &&& result.get_Ok_0() === pte
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: result.get_Ok_0().frame.size },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    } else {
                        assert({
                            &&& thread_state matches hlspec::ThreadState::Unmap {
                                vaddr: v_addr,
                                pte: None,
                            }
                            &&& vaddr === v_addr
                        });
                        assert(overlap(
                            MemRegion { base: vaddr, size: 0 },
                            MemRegion { base: base, size: candidate_size },
                        ));
                    }
                },
                _ => {},
            };
        }
    };

}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_os_implies_hl(
    c: os::Constants,
    s: os::State,
    candidate: PTE,
)
    requires
        s.inv_basic(c),
        candidate.frame.size > 0,
    ensures
        os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ),
{
    assert(os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    ) ==> hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    )) by {
        if os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ) {
            let corestate = choose|b: os::CoreState| #![auto] {
                    &&& s.core_states.values().contains(b)
                    &&& match b {
                        os::CoreState::MapWaiting { vaddr, pte, .. }
                        | os::CoreState::MapExecuting { vaddr, pte, .. }
                        | os::CoreState::MapDone { vaddr, pte, .. } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        os::CoreState::UnmapWaiting { ult_id, vaddr }
                        | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                            &&& s.interp_pt_mem().dom().contains(vaddr)
                            &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                        },
                        os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                        | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                        | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                            &&& result is Ok
                            &&& overlap(candidate.frame, result.get_Ok_0().frame)
                        },
                        os::CoreState::Idle => false,
                    }
                };
            let core = choose|core| #[trigger] s.core_states.dom().contains(core) && s.core_states[core] == corestate;
            assert(c.valid_core(core));
            match corestate {
                os::CoreState::MapWaiting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id, vaddr, pte, .. }
                | os::CoreState::MapDone { ult_id, vaddr, pte, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state[ult_id] == thread_state);
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_address,
                            pte: p_te,
                        }
                        &&& v_address === vaddr
                        &&& p_te === pte
                        &&& overlap(candidate.frame, pte.frame)
                    });
                },
                os::CoreState::UnmapWaiting { ult_id, vaddr }
                | os::CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_address,
                            pte: Some(pte),
                        }
                        &&& v_address === vaddr
                        &&& s.interp_pt_mem()[vaddr] === pte
                        &&& overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame)
                    });
                },
                os::CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                    assert(c.valid_ult(ult_id));
                    let thread_state = s.interp_thread_state(c)[ult_id];
                    assert(s.interp(c).thread_state.dom().contains(ult_id));
                    assert(s.interp(c).thread_state.values().contains(thread_state));
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_address,
                            pte: pte,
                        }
                        &&& v_address === vaddr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                        &&& overlap(candidate.frame, pte->0.frame)
                    });
                },
                _ => {},
            };
        } 
    };
}

pub proof fn lemma_candidate_mapping_inflight_pmem_overlap_hl_implies_os(
    c: os::Constants,
    s: os::State,
    candidate: PTE,
)
    requires
        s.inv_basic(c),
        candidate.frame.size > 0,
    ensures
        hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ) ==> os::candidate_mapping_overlaps_inflight_pmem(
            s.interp_pt_mem(),
            s.core_states.values(),
            candidate,
        ),
{
    assert(hlspec::candidate_mapping_overlaps_inflight_pmem(
        s.interp(c).thread_state.values(),
        candidate,
    ) ==> os::candidate_mapping_overlaps_inflight_pmem(
        s.interp_pt_mem(),
        s.core_states.values(),
        candidate,
    )) by {
        if hlspec::candidate_mapping_overlaps_inflight_pmem(
            s.interp(c).thread_state.values(),
            candidate,
        ) {
            let thread_state = choose|b| {
                    &&& s.interp(c).thread_state.values().contains(b)
                    &&& match b {
                        hlspec::ThreadState::Map { vaddr, pte } => {
                            overlap(candidate.frame, pte.frame)
                        },
                        hlspec::ThreadState::Unmap { vaddr, pte } => {
                            &&& pte.is_some()
                            &&& overlap(candidate.frame, pte.unwrap().frame)
                        },
                        _ => { false },
                    }
                };
            let ult_id = choose|id| #[trigger]
                c.valid_ult(id) && s.interp(c).thread_state[id] == thread_state;
            assert(c.valid_ult(ult_id));
            let core = c.ult2core[ult_id];
            assert(c.valid_core(core));
            assert(s.core_states.dom().contains(core));
            let core_state = s.core_states[core];
            assert(s.core_states.values().contains(core_state));
            match core_state {
                os::CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte, .. }
                | os::CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Map {
                            vaddr: v_addr,
                            pte: entry,
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, pte.frame));
                },
                os::CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                | os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None, .. } => {
                    assert(s.interp_pt_mem().dom().contains(vaddr));
                    assert(ult_id == ult_id);
                    let pte = s.interp_pt_mem()[vaddr];
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_addr,
                            pte: Some(entry),
                        }
                        &&& vaddr === v_addr
                        &&& entry === pte
                    });
                    assert(overlap(candidate.frame, s.interp_pt_mem().index(vaddr).frame));
                },
                os::CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result), .. }
                | os::CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result, .. }
                | os::CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result, .. } => {
                    assert(ult_id == ult_id);
                    assert({
                        &&& thread_state matches hlspec::ThreadState::Unmap {
                            vaddr: v_addr,
                            pte,
                        }
                        &&& vaddr === v_addr
                        &&& match result {
                            Ok(pte_) => pte is Some && pte_ == pte->0,
                            Err(_) => pte is None,
                        }
                    });
                    assert(overlap(candidate.frame, result.get_Ok_0().frame));
                },
                _ => {},
            };
        }
    };
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// usefull lemmata about maps
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub proof fn lemma_map_insert_values_equality<A, B>(map: Map<A, B>, key: A, value: B)
    requires
        map.dom().contains(key),
    ensures
        map.values().insert(value) === map.insert(key, value).values().insert(map.index(key)),
{
    assert forall|values| #![auto] map.values().insert(value).contains(values)
        implies map.insert(key, value).values().insert(map.index(key)).contains(values)
    by {
        if values == value {
            lemma_map_insert_value(map, key, value);
        } else {
            let k = choose|some_key| #[trigger]
                map.dom().contains(some_key) && (map[some_key] == values);
            assert(map.insert(key, value).dom().contains(k));
            if k == key {
                assert(map.index(key) == values);
            } else {
                assert(map[k] === map.insert(key, value)[k]);
            }
        }
    }
    assert(map.values().insert(value) =~= map.insert(key, value).values().insert(map.index(key)));
}

pub proof fn lemma_map_insert_value<A, B>(map: Map<A, B>, key: A, value: B)
    requires
    ensures
        map.insert(key, value).values().contains(value),
{
    assert(map.insert(key, value).dom().contains(key));
    assert(map.insert(key, value)[key] == value);
}

} // verus!
