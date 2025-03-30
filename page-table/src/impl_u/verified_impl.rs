use vstd::prelude::*;

use crate::spec_t::mmu::defs::{ PageTableEntryExec, MemRegionExec, x86_arch_spec_upper_bound };
#[cfg(verus_keep_ghost)]
use crate::spec_t::mmu::defs::{ candidate_mapping_overlaps_existing_vmem, MAX_BASE };
use crate::spec_t::os_code_vc::{ Prophecy, Token, CodeVC };
use crate::impl_u::wrapped_token::{ WrappedMapToken, WrappedUnmapToken };
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

        crate::impl_u::wrapped_token::start_map_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat), Ghost(pte@));
        // TODO: Needs an OS invariant
        //assume(tok.st().mmu@.pending_maps === map![]);
        let tracked wtok = WrappedMapToken::new(tok); //, proph_res.value());
        let mut pt = Ghost(arbitrary());
        assume(PT::inv_and_nonempty(wtok@, pt@));
        assume(PT::interp(wtok@, pt@).inv());


        proof {
            x86_arch_spec_upper_bound();
            assert(vaddr < MAX_BASE);
        }

        let ghost wtok_before = wtok@;
        let ghost pt_before = pt@;

        let res = map_frame(Tracked(&mut wtok), &mut pt, pml4, vaddr, pte);

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
        assert(wtok@.done);

        proof { proph_res.resolve(res); }

        let tok = WrappedMapToken::finish_map_and_release_lock(Tracked(wtok));

        (res, tok)
    }

    #[verifier(external_body)]
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        Tracked(proph_res): Tracked<Prophecy<Result<(),()>>>
    ) -> (res: (Result<MemRegionExec,()>, Tracked<Token>))
    {
        let tracked wtok = WrappedUnmapToken::new(tok);
        let mut pt = Ghost(arbitrary());
        let res = unmap(Tracked(&mut wtok), &mut pt, pml4, vaddr);

        let tracked tok = wtok.destruct();

        (res, Tracked(tok))
    }
}


} // verus!
