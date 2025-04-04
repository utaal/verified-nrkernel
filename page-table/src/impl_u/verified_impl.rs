use vstd::prelude::*;

use crate::spec_t::mmu::defs::{ PageTableEntryExec, MemRegionExec, x86_arch_spec_upper_bound };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ candidate_mapping_overlaps_existing_vmem, MAX_BASE, x86_arch_spec };
use crate::spec_t::os_code_vc::{ Prophecy, Token, CodeVC };
use crate::impl_u::wrapped_token::{ self, WrappedMapToken, WrappedUnmapToken, WrappedTokenView, DoShootdown };
use crate::impl_u::l2_impl::PT::{ self, map_frame, unmap };

verus! {

pub struct PTImpl {}

impl CodeVC for PTImpl {
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
        Tracked(proph_res): Tracked<Prophecy<Result<(),()>>>
    ) -> (Result<(),()>, Tracked<Token>)
    {
        let tracked mut tok = tok;
        let tracked mut proph_res = proph_res;

        wrapped_token::start_map_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat), Ghost(pte@));
        let tracked wtok = WrappedMapToken::new(tok); //, tok.steps()[0]->MapEnd_result);
        proof {
            wtok.lemma_regions_derived_from_view();
        }
        let mut pt = Ghost(choose|pt| PT::inv_and_nonempty(wtok@, pt));
        assert(PT::inv_and_nonempty(wtok@, pt@));

        proof {
            x86_arch_spec_upper_bound();
            assert(vaddr < MAX_BASE);
            assert(x86_arch_spec.contains_entry_size_at_index_atleast(pte.frame.size as nat, 1)) by {
                assert(x86_arch_spec.entry_size(1) == crate::spec_t::mmu::defs::L1_ENTRY_SIZE);
                assert(x86_arch_spec.entry_size(2) == crate::spec_t::mmu::defs::L2_ENTRY_SIZE);
                assert(x86_arch_spec.entry_size(3) == crate::spec_t::mmu::defs::L3_ENTRY_SIZE);
            };
        }

        let ghost wtok_before = wtok@;
        let ghost pt_before = pt@;

        let res = map_frame(Tracked(&mut wtok), &mut pt, pml4, vaddr, pte);
        assert(PT::inv_and_nonempty(wtok@, pt@));
        assert forall|wtokp: WrappedTokenView| ({
            &&& wtokp.pt_mem == wtok@.pt_mem
            &&& wtokp.regions.dom() == wtok@.regions.dom()
            &&& #[trigger] wtokp.regions_derived_from_view()
        }) implies exists|pt| PT::inv_and_nonempty(wtokp, pt) by {
            wtok.lemma_regions_derived_from_view();
            PT::lemma_inv_at_changed_tok(wtok@, wtokp, pt@, 0, pt@.region.base as usize);
            PT::lemma_no_empty_directories_with_changed_tok(wtok@, pt@, wtokp, pt@, 0, pt@.region.base as usize, 0);
            assert(PT::inv_and_nonempty(wtokp, pt@));
        };

        if let Err(_) = res {
            proof {
                assert(candidate_mapping_overlaps_existing_vmem(
                    PT::interp_to_l0(wtok@, pt@),
                    wtok@.args->Map_base as nat,
                    wtok@.args->Map_pte
                ));
                WrappedMapToken::register_failed_map(&mut wtok, pt@);
            }
        }
        assert(wtok@.change_made);

        assert(wtok@.steps === tok.steps());
        proof { proph_res.resolve(res); }

        assert(wtok@.result == proph_res.value()) by {
            if let Ok(_) = res {
                assert(wtok@.result === Ok(()));
                assert(res is Ok);
                assert(res.get_Ok_0() == ());
                assert(res == Ok::<(), ()>(()));
                assert(proph_res.value() is Ok);
                assert(proph_res.value() == Ok::<(), ()>(()));
            }

            if let Err(_) = res {
                assert(wtok@.result === Err(()));
                assert(res is Err);
                assert(res.get_Err_0() == ());
                assert(res == Err::<(), ()>(()));
                assert(proph_res.value() is Err);
                assert(proph_res.value() == Err::<(), ()>(()));
            }
        };
        assert(wtok@.steps[0]->MapEnd_result == proph_res.value());
        let tok = WrappedMapToken::finish_map_and_release_lock(Tracked(wtok));

        (res, tok)
    }

    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        Tracked(proph_res): Tracked<Prophecy<Result<(),()>>>
    ) -> (res: (Result<MemRegionExec,()>, Tracked<Token>))
    {
        let tracked mut tok = tok;
        let tracked mut proph_res = proph_res;

        wrapped_token::start_unmap_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat));
        let tracked wtok = WrappedUnmapToken::new(tok); //, tok.steps()[0]->MapEnd_result);
        proof {
            wtok.lemma_regions_derived_from_view();
        }
        let mut pt = Ghost(choose|pt| PT::inv_and_nonempty(wtok@, pt));
        assert(PT::inv_and_nonempty(wtok@, pt@));

        proof {
            x86_arch_spec_upper_bound();
            assert(vaddr < MAX_BASE);
            assert(x86_arch_spec.entry_size(1) == crate::spec_t::mmu::defs::L1_ENTRY_SIZE);
            assert(x86_arch_spec.entry_size(2) == crate::spec_t::mmu::defs::L2_ENTRY_SIZE);
            assert(x86_arch_spec.entry_size(3) == crate::spec_t::mmu::defs::L3_ENTRY_SIZE);
        }

        let ghost wtok_before = wtok@;
        let ghost pt_before = pt@;

        let res = unmap(Tracked(&mut wtok), &mut pt, pml4, vaddr);
        assert(PT::inv_and_nonempty(wtok@, pt@));
        assert forall|wtokp: WrappedTokenView| ({
            &&& wtokp.pt_mem == wtok@.pt_mem
            &&& wtokp.regions.dom() == wtok@.regions.dom()
            &&& #[trigger] wtokp.regions_derived_from_view()
        }) implies exists|pt| PT::inv_and_nonempty(wtokp, pt) by {
            wtok.lemma_regions_derived_from_view();
            PT::lemma_inv_at_changed_tok(wtok@, wtokp, pt@, 0, pt@.region.base as usize);
            PT::lemma_no_empty_directories_with_changed_tok(wtok@, pt@, wtokp, pt@, 0, pt@.region.base as usize, 0);
            assert(PT::inv_and_nonempty(wtokp, pt@));
        };

        let shootdown = if let Ok(pte) = res {
            assume(wtok@.result is Ok);
            assume(wtok@.steps[0]->UnmapEnd_result is Ok);
            assume(wtok@.args->Unmap_base == vaddr);
            DoShootdown::Yes { vaddr, size: pte.size }
        } else {
            assume(wtok@.result is Err);
            assume(wtok@.steps[0]->UnmapEnd_result is Err);
            assume(!PT::interp_to_l0(wtok@, pt@).contains_key(vaddr as nat));
            DoShootdown::No
        };

        assume(wtok@.steps[0]->UnmapEnd_result == wtok@.result);
        let tok = WrappedUnmapToken::finish_unmap_and_release_lock(Tracked(wtok), shootdown, pt);

        assume(res is Ok <==> proph_res.value() is Ok);

        (res, tok)
    }
}


} // verus!
