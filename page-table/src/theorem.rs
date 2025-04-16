#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::prelude::*;
use crate::spec_t::hlspec;
use crate::spec_t::os;
use crate::spec_t::mmu::defs::{ MemOp, PTE, Core };
use crate::spec_t::os_code_vc::{ CodeVC, HandlerVC };
use crate::impl_u::verified_impl::PTImpl;

verus!{

// Lemma 1: The OS+HW state machine refines the userspace specification.

// $line_count$Trusted${$
proof fn lemma1_init(c: os::Constants, pre: os::State)
    requires
        os::init(c, pre),
    ensures
        hlspec::init(c.interp(), pre.interp(c)),
        pre.inv(c),
// $line_count$}$
{
    crate::impl_u::os_refinement::os_init_refines_hl_init(c, pre);
    crate::spec_t::os_invariant::init_implies_inv(c, pre);
}

// $line_count$Trusted${$
proof fn lemma1_next(c: os::Constants, pre: os::State, post: os::State, lbl: RLbl)
    requires
        os::next(c, pre, post, lbl),
        pre.inv(c),
    ensures
        hlspec::next(c.interp(), pre.interp(c), post.interp(c), lbl.interp()),
        post.inv(c),
// $line_count$}$
{
    crate::impl_u::os_refinement::os_next_refines_hl_next(c, pre, post, lbl);
    crate::spec_t::os_invariant::next_preserves_inv(c, pre, post, lbl);
}

// Lemma 2: The implemented functions realize their specification in the OS+HW state machine.

spec fn ensure_codevc<X: CodeVC>(x: X) -> bool { true }

spec fn ensure_handlervc<X: HandlerVC>(x: X) -> bool { true }

// $line_count$Trusted${$
proof fn lemma2(p: PTImpl) {
    ensure_codevc(p);
    ensure_handlervc(p);
}
// $line_count$}$







pub enum TokState {
    Init,
    ProphecyMade,
    Validated,
    Spent,
}

pub enum RLbl {
    Tau,
    MemOp      { thread_id: nat, vaddr: nat, op: MemOp },
    MapStart   { thread_id: nat, vaddr: nat, pte: PTE },
    MapEnd     { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    UnmapStart { thread_id: nat, vaddr: nat },
    UnmapEnd   { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    AckShootdownIPI { core: Core },
}

impl RLbl {
    /// When we prescribe steps to be taken that contain outputs, the outputs on the actual
    /// transition may differ, since we don't know them ahead of time.
    pub open spec fn compatible_with(self, other: RLbl) -> bool {
        match (self, other) {
            (RLbl::MapEnd { thread_id, vaddr, .. }, RLbl::MapEnd { thread_id: t2, vaddr: v2, .. })
                => thread_id == t2 && vaddr == v2,
            (RLbl::UnmapEnd { thread_id, vaddr, .. }, RLbl::UnmapEnd { thread_id: t2, vaddr: v2, .. })
                => thread_id == t2 && vaddr == v2,
            _ => other == self,
        }
    }

    /// To specify the VC for the shootdown handler, we need a label for the AckShootdownIPI
    /// transition. However, the transition is still internal and not visible in the high-level
    /// spec, so during refinement it gets refined to `RLbl::Tau`.
    pub open spec fn is_internal(self) -> bool {
        self is Tau || self is AckShootdownIPI
    }

    pub open spec fn interp(self) -> RLbl {
        if self.is_internal() { RLbl::Tau } else { self }
    }
}


}
