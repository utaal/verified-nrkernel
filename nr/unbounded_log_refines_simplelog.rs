// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use super::pervasive::map::*;
use super::pervasive::seq::*;
//use super::pervasive::set::*;
use super::pervasive::*;

use state_machines_macros::*;

use super::simple_log::{ReadReq as SReadReq, SimpleLog, UpdateResp as SUpdateResp};
use super::types::*;
use super::unbounded_log::{CombinerState, ReadonlyState, UnboundedLog, UpdateState};
use super::utils::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Refinement Proof: UnboundedLog refines SimpleLog
// ================================================
//
// ...
//
////////////////////////////////////////////////////////////////////////////////////////////////////

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interpretation Function
////////////////////////////////////////////////////////////////////////////////////////////////////


spec fn interp_log(global_tail: nat, log: Map<nat, LogEntry>) -> Seq<UpdateOp> {
    Seq::new(global_tail, |i| log.index(i as nat).op)
}

spec fn interp_readonly_reqs(local_reads: Map<nat, ReadonlyState>) -> Map<ReqId, SReadReq> {
    Map::new(
        |rid| local_reads.dom().contains(rid),
        |rid| match local_reads.index(rid) {
            ReadonlyState::Init { op } => SReadReq::Init { op },
            ReadonlyState::VersionUpperBound { version_upper_bound: idx, op } => SReadReq::Req { op, version: idx },
            ReadonlyState::ReadyToRead { version_upper_bound: idx, op, .. } => SReadReq::Req { op, version: idx },
            ReadonlyState::Done { version_upper_bound: idx, op, .. } => SReadReq::Req { op, version: idx },
        },
    )
}

spec fn interp_update_reqs(local_updates: Map<LogIdx, UpdateState>) -> Map<LogIdx, UpdateOp> {
    Map::new(
        |rid| local_updates.dom().contains(rid) && local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => op,
            _ => arbitrary(),
        }
    )
}

spec fn interp_update_resps(local_updates: Map<nat, UpdateState>) -> Map<ReqId, SUpdateResp> {
    Map::new(
        |rid| local_updates.dom().contains(rid) && !local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => arbitrary(),
            UpdateState::Placed{op, idx} => SUpdateResp(idx),
            UpdateState::Applied{ret, idx} => SUpdateResp(idx),
            UpdateState::Done{ret, idx} => SUpdateResp(idx),
        },
    )
}

spec fn interp(s: UnboundedLog::State) -> SimpleLog::State {
    SimpleLog::State {
        log: interp_log(s.global_tail, s.log),
        version: s.version_upper_bound,
        readonly_reqs: interp_readonly_reqs(s.local_reads),
        update_reqs: interp_update_reqs(s.local_updates),
        update_resps: interp_update_resps(s.local_updates),
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////


#[proof]
fn refinement(pre: UnboundedLog::State, post: UnboundedLog::State)
    requires
        pre.invariant(),
        post.invariant(),
        interp(pre).invariant(),
        UnboundedLog::State::next_strong(pre, post),
    ensures
        SimpleLog::State::next(interp(pre), interp(post)),
{
    case_on_next_strong!{pre, post, UnboundedLog => {
        readonly_start(op) => {
            // let rid = get_new_nat(pre.local_reads.dom());
            // assert_maps_equal!(
            //     pre.local_reads.insert(rid, ReadonlyState::Init {op}),
            //     post.local_reads
            // );
            // assert_maps_equal!(
            //     interp(pre).readonly_reqs.insert(rid, SReadReq::Init{op}),
            //     interp(post).readonly_reqs
            // );

            // SimpleLog::show::readonly_start(interp(pre), interp(post), rid, op);
            // assert(SimpleLog::State::next(interp(pre), interp(post)));
            assume(false);
        }
        readonly_read_ctail(rid) => {
            // assert(interp(pre).readonly_reqs.dom().contains(rid));
            // if let SReadReq::Init { op } = interp(pre).readonly_reqs.index(rid) {
            //     assert(interp(pre).readonly_reqs.index(rid) === SReadReq::Init{ op });
            // } else {
            //     assert(false);
            // }
            // SimpleLog::show::readonly_read_version(interp(pre), interp(post), rid);
            // assert(SimpleLog::State::next(interp(pre), interp(post)));
            assume(false);
        }

        readonly_ready_to_read(rid, node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        readonly_apply(rid) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        readonly_finish(rid, op, version_upper_bound, node_id, ret) => {
            assume(false);
            //SimpleLog::show::finish_readonly(interp(pre), interp(post), rid, );
        }

        update_start(op) => {
            assume(false);
            // let rid = choose|rid: nat| post.local_updates === pre.local_updates.insert(rid, UpdateState::Init { op });
            // // get the request id here..
            // SimpleLog::show::update_start(interp(pre), interp(post), rid, op);
        }

        update_place_ops_in_log_one(node_id, rid) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        update_done(rid) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        update_finish(rid) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_trivial_start(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_load_local_version(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_load_local_version(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_load_global_head(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_dispatch_local(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_dispatch_remote(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_update_version_upper_bound(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_finish(node_id) => {
            assume(false);
            // SimpleLog::show::no_op(interp(pre), interp(post));
        }
    }
}
}

} // end verus!
