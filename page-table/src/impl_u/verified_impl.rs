use vstd::prelude::*;

use crate::spec_t::mmu::defs::{ PageTableEntryExec, Core, MAX_BASE };
use crate::spec_t::os_code_vc::{ Prophecy, Token, CodeVC };
use crate::impl_u::wrapped_token::{ WrappedMapToken };
use crate::impl_u::l2_impl::PT::{ map_frame };

verus! {

struct PT {}

impl CodeVC for PT {
    exec fn sys_do_map(
        Tracked(tok): Tracked<Token>,
        vaddr: usize,
        pte: PageTableEntryExec,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (Result<(),()>, Tracked<Token>)
    {
        let tracked mut tok = tok;
        let tracked mut proph_res = proph_res;
        //requires
        //    os::step_Map_enabled(vaddr as nat, pte@),
        //    tok.st().inv(tok.consts()),
        //    tok.consts().valid_ult(tok.thread()),
        //    tok.st().core_states[tok.core()] is Idle,
        //    tok.steps() === seq![
        //        RLbl::MapStart { thread_id: tok.thread(), vaddr: vaddr as nat, pte: pte@ },
        //        RLbl::MapEnd { thread_id: tok.thread(), vaddr: vaddr as nat, result: proph_res.value() }
        //    ],
        //    tok.progress() is Unready,
        //    proph_res.may_resolve(),
        //ensures
        //    res.0 == proph_res.value(),
        //    res.1.steps() === seq![],
        //    res.1.progress() is Ready,


        proof {
            crate::impl_u::wrapped_token::do_step_mapstart(&mut tok, vaddr, pte);
        }
        crate::impl_u::wrapped_token::do_step_mapopstart(Tracked(&mut tok));
        // TODO: Needs an invariant
        assume(tok.st().mmu@.pending_maps === map![]);
        let tracked wtok = WrappedMapToken::new(tok);
        let mut pt = Ghost(arbitrary());
        assume(crate::impl_u::l2_impl::PT::inv(wtok@, pt@));
        assume(crate::impl_u::l2_impl::PT::interp(wtok@, pt@).inv());

        // TODO: don't magic pml4 into existence
        let pml4: usize = 0;
        assume(pml4 == wtok@.pml4);

        assume(vaddr < MAX_BASE); // TODO: We probably need to somehow get this out of the first transition?

        let res = map_frame(Tracked(&mut wtok), &mut pt, pml4, vaddr, pte);

        proof { proph_res.resolve(res); }

        let tracked tok = wtok.destruct();

        (res, Tracked(tok))
    }

    #[verifier(external_body)]
    exec fn sys_do_unmap(
        Tracked(tok): Tracked<&mut Token>,
        core: Core,
        vaddr: usize,
        tracked proph_res: Prophecy<Result<(),()>>
    ) -> (res: Result<(),()>)
    { unimplemented!() }
}


} // verus!
