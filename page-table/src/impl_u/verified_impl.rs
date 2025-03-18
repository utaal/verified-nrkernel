use vstd::prelude::*;

use crate::spec_t::mmu::defs::{ PageTableEntryExec, Core, MAX_BASE, MemRegionExec };
use crate::spec_t::os_code_vc::{ Prophecy, Token, CodeVC };
use crate::impl_u::wrapped_token::{ WrappedMapToken, WrappedUnmapToken };
use crate::impl_u::l2_impl::PT::{ map_frame, unmap };

verus! {

struct PT {}

impl CodeVC for PT {
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (Result<(),()>, Tracked<Token>)
    {
        let tracked mut tok = tok;
        let tracked mut proph_res = proph_res;

        crate::impl_u::wrapped_token::register_step_and_acquire_lock(Tracked(&mut tok), Ghost(vaddr as nat), Ghost(pte@));
        // TODO: Needs an invariant
        assume(tok.st().mmu@.pending_maps === map![]);
        let tracked wtok = WrappedMapToken::new(tok);
        let mut pt = Ghost(arbitrary());
        assume(crate::impl_u::l2_impl::PT::inv(wtok@, pt@));
        assume(crate::impl_u::l2_impl::PT::interp(wtok@, pt@).inv(true));


        assume(vaddr < MAX_BASE); // TODO: We probably need to somehow get this out of the first transition?

        let res = map_frame(Tracked(&mut wtok), &mut pt, pml4, vaddr, pte);

        proof { proph_res.resolve(res); }

        let tracked tok = wtok.destruct();

        (res, Tracked(tok))
    }

    #[verifier(external_body)]
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<Token>,
        pml4: usize,
        core: Core,
        vaddr: usize,
        tracked proph_res: Prophecy<Result<(),()>>
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
