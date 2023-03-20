// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::arbitrary;
use super::pervasive::map::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::seq::Seq;
use super::pervasive::seq_lib::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::set::*;

use state_machines_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::simple_log::{
    compute_nrstate_at_version as s_nrstate_at_version, ReadReq as SReadReq, SimpleLog,
    UpdateResp as SUpdateResp,
};
#[allow(unused_imports)] // XXX: should not be needed!
use super::types::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::unbounded_log::{
    combiner_request_id_fresh, compute_nrstate_at_version as i_nrstate_at_version, get_fresh_nat,
    CombinerState, ReadonlyState, UnboundedLog, UpdateState,
};
#[allow(unused_imports)] // XXX: should not be needed!
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
        log: interp_log(s.tail, s.log),
        version: s.version_upper_bound,
        readonly_reqs: interp_readonly_reqs(s.local_reads),
        update_reqs: interp_update_reqs(s.local_updates),
        update_resps: interp_update_resps(s.local_updates),
    }
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////

proof fn refinement_inv(vars: UnboundedLog::State)
    requires vars.invariant()
    ensures interp(vars).invariant()
{
}

proof fn refinement_init(post: UnboundedLog::State)
    requires
        post.invariant(),
        UnboundedLog::State::init(post)
    ensures
        SimpleLog::State::init(interp(post)),
{
    case_on_init!{ post, UnboundedLog => {
        initialize(number_of_nodes) => {
            assert_maps_equal!(interp(post).readonly_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_reqs, Map::empty());
            assert_maps_equal!(interp(post).update_resps, Map::empty());
            assert_seqs_equal!(interp(post).log, Seq::empty());
            SimpleLog::show::initialize(interp(post));
        }
    }}
}


proof fn refinement_next(pre: UnboundedLog::State, post: UnboundedLog::State)
    requires
        pre.invariant(),
        post.invariant(),
        UnboundedLog::State::next_strong(pre, post),
    ensures
        SimpleLog::State::next(interp(pre), interp(post)),
{
    case_on_next_strong! {
      pre, post, UnboundedLog => {
        readonly_start(op) => {

            let rid = get_fresh_nat(pre.local_reads.dom(), pre.combiner);
            assert_maps_equal!(
                pre.local_reads.insert(rid, ReadonlyState::Init {op}),
                post.local_reads
            );
            assert_maps_equal!(
                interp(pre).readonly_reqs.insert(rid, SReadReq::Init{op}),
                interp(post).readonly_reqs
            );

            SimpleLog::show::readonly_start(interp(pre), interp(post), rid, op);
        }

        readonly_read_ctail(rid) => {
            let op = pre.local_reads.index(rid).get_Init_op();

            assert_maps_equal!(
                interp(pre).readonly_reqs.insert(rid, SReadReq::Req { op, version: pre.version_upper_bound }),
                interp(post).readonly_reqs
            );

            SimpleLog::show::readonly_read_version(interp(pre), interp(post), rid);
        }

        readonly_ready_to_read(rid, node_id) => {
            assert_maps_equal!(interp(pre).readonly_reqs, interp(post).readonly_reqs);
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        readonly_apply(rid) => {
            assert_maps_equal!(interp(pre).readonly_reqs, interp(post).readonly_reqs);
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        readonly_finish(rid, op, ret) => {
            // corresponds toConsumeStub_Refines_End
            // let version = 0;

            assert(op == pre.local_reads.index(rid).get_Done_op());
            assert(op == interp(pre).readonly_reqs.index(rid).get_Req_op());

            assert(pre.local_reads.index(rid).is_Done());
            assert(ret == pre.local_reads.index(rid).get_Done_ret());

            let version_upper_bound = pre.local_reads.index(rid).get_Done_version_upper_bound();

            // assert(node_id == pre.local_reads.index(rid).get_Done_node_id());

            assert(version_upper_bound <= pre.version_upper_bound);
            assert(rangeincl(version_upper_bound, version_upper_bound, pre.version_upper_bound));
            assert(exists |v| rangeincl(version_upper_bound, v, pre.version_upper_bound));

            assert(pre.version_upper_bound  <= interp(pre).log.len());


            assert(forall |version| 0 <= version <= pre.version_upper_bound ==> #[trigger] version_in_log(pre.log, version));
            assert(forall |version| version_upper_bound <= version <= pre.version_upper_bound ==> #[trigger] version_in_log(pre.log, version));
            assert(forall |v| version_upper_bound <= v <= pre.version_upper_bound <==> #[trigger] dummy(version_upper_bound, v, pre.version_upper_bound));

            assert(forall |version|#[trigger]rangeincl(version_upper_bound, version, pre.version_upper_bound) ==> version_in_log(pre.log, version));

            // assert(exists |version : nat | version_upper_bound <= version <= pre.version_upper_bound
            // ==> VersionInLog(pre.log, version) && result_match(s.log, output, version,  s.localReads[rid].op)) by {

            assert(exists |version: nat| #[trigger]rangeincl(version_upper_bound, version, pre.version_upper_bound) && result_match(pre.log, ret, version, op)) ;

            let version : nat = choose(|version| {
                version_upper_bound <= version <= pre.version_upper_bound
                && #[trigger] result_match(pre.log, ret, version, op)
            });

            assert(version_in_log(pre.log, version));
            assert(version <= pre.version_upper_bound);
            assert(version <= interp(pre).version);
            assert(0 <= version <=  interp(pre).log.len());
            assert(interp(pre).readonly_reqs.index(rid).get_Req_version() <= version <= interp(pre).log.len());

            assert(ret == interp(pre).nrstate_at_version(version).read(op)) by {
                state_at_version_refines(interp(pre).log, pre.log, pre.tail, version);
            }

            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).readonly_reqs.remove(rid), interp(post).readonly_reqs);

            SimpleLog::show::readonly_finish(interp(pre), interp(post), rid, version, ret);
        }

        update_start(op) => {
            let rid = get_fresh_nat(pre.local_updates.dom(), pre.combiner);

            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(
                interp(pre).update_reqs.insert(rid, op),
                interp(post).update_reqs
            );

            SimpleLog::show::update_start(interp(pre), interp(post), rid, op);
        }

        update_place_ops_in_log_one(node_id, rid) => {
            let op = pre.local_updates.index(rid).get_Init_op();

            assert_seqs_equal!(interp(pre).log.push(op), interp(post).log);
            assert_maps_equal!(interp(pre).update_reqs.remove(rid), interp(post).update_reqs);
            assert_maps_equal!(
                interp(pre).update_resps.insert(rid, SUpdateResp(pre.tail)),
                interp(post).update_resps
            );

            SimpleLog::show::update_add_ops_to_log_one(interp(pre), interp(post), rid);
        }

        update_done(rid) => {
            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);

            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        update_finish(rid) => {
            let ret = pre.local_updates.index(rid).get_Done_ret();
            let idx = pre.local_updates.index(rid).get_Done_idx();

            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).update_resps.remove(rid), interp(post).update_resps);

            SimpleLog::show::update_finish(interp(pre), interp(post), rid);
        }

        exec_trivial_start(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_load_local_version(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_load_local_version(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_load_global_head(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_dispatch_local(node_id) => {
            assert_maps_equal!(interp(pre).update_reqs, interp(post).update_reqs);
            assert_maps_equal!(interp(pre).update_resps, interp(post).update_resps);
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_dispatch_remote(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_update_version_upper_bound(node_id) => {
            let global_tail = pre.combiner.index(node_id).get_Loop_tail();
            let version = if pre.version_upper_bound >= global_tail{
                pre.version_upper_bound
            } else {
                global_tail
            };
            SimpleLog::show::update_incr_version(interp(pre), interp(post), version);
        }

        exec_finish(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }

        exec_finish_no_change(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
      }
    }
}

pub open spec fn dummy(lower:nat, mid: nat, upper: nat) -> bool
    recommends lower <= upper
{
    lower <= mid <= upper
}

pub open spec fn dummy2(lower:nat, mid: nat, upper: nat) -> bool
    recommends lower < upper
{
    lower <= mid < upper
}


pub open spec fn version_in_log(log: Map<LogIdx, LogEntry>, version: LogIdx) -> bool
{
    forall |i| 0 <= i < version ==> log.contains_key(i)
}

pub open spec fn result_match(log: Map<LogIdx, LogEntry>,  output: ReturnType, version: LogIdx, op: ReadonlyOp) -> bool
    recommends version_in_log(log, version)
{

    output == i_nrstate_at_version(log, version).read(op)
}


proof fn state_at_version_refines(s_log: Seq<UpdateOp>, i_log: Map<LogIdx, LogEntry>, gtail: nat, idx:nat)
    requires
      forall |i| 0 <= i < gtail ==> i_log.dom().contains(i),
      0 <= idx <= s_log.len(),
      idx <= gtail,
      s_log == interp_log(gtail, i_log),
    ensures
      s_nrstate_at_version(s_log, idx) == i_nrstate_at_version(i_log, idx)
    decreases idx
{
    if idx > 0 {
        state_at_version_refines(s_log, i_log, gtail, (idx - 1) as nat);
    }
}

} // end verus!
