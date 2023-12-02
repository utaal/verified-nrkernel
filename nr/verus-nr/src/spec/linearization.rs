// The Linearization Proof


#[allow(unused_imports)]
use builtin::*;
// use vstd::*;
use vstd::seq::*;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::spec::simple_log::{UpdateResp, ReadReq, SimpleLog, compute_nrstate_at_version};
use crate::{LogIdx, ReqId};
use crate::Dispatch;
#[cfg(verus_keep_ghost)]
use crate::{SimpleLogRefinesAsynchronousSingleton, AsyncLabel, AsynchronousSingletonBehavior, AsynchronousSingleton, SimpleLogBehavior,
behavior_equiv, InputOperation, OutputOperation};

verus! {
#[cfg(verus_keep_ghost)]
type SState<DT> = SimpleLog::State<DT>;
#[cfg(verus_keep_ghost)]
type AState<DT> = AsynchronousSingleton::State<DT>;

////////////////////////////////////////////////////////////////////////////////////////////////////
//                                  LINEARIZATION PROOF                                           //
////////////////////////////////////////////////////////////////////////////////////////////////////


// =================================================================================================
// Refinement Theorem
// =================================================================================================

#[cfg(verus_keep_ghost)]
pub struct RefinementProof;
#[cfg(verus_keep_ghost)]
impl<DT: Dispatch> SimpleLogRefinesAsynchronousSingleton<DT> for RefinementProof {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<DT>)
        // requires a.wf(),
        // ensures b.wf() && behavior_equiv(a, b)
    {
        return exists_equiv_behavior_rec(a, Map::empty())
    }
}

/// The *actual* refinement proof using recursion over the behaviors
proof fn exists_equiv_behavior_rec<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>)
    -> (b: AsynchronousSingletonBehavior<DT>)
    requires a.wf() && future_points_ok(a.get_last(), r_points)
    ensures  b.wf() && behavior_equiv(a, b) && state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases a, 0nat, 0nat
{
    match a {
        SimpleLogBehavior::Stepped(post, aop, tail) => {
            // reveal the next transition
            reveal(SimpleLog::State::next);
            reveal(SimpleLog::State::next_by);
            reveal(AsynchronousSingleton::State::next);
            reveal(AsynchronousSingleton::State::next_by);

            let prev = tail.get_last();
            let step = choose |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(prev, post, step);
            match step {
                SimpleLog::Step::readonly_start(rid, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.remove(rid));
                    let a0 = readonly_start_refines(prev, post, b0.get_last(), r_points, rid, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::readonly_read_version(rid) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = readonly_read_version_refines(prev, post, b0.get_last(), r_points, rid);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::readonly_finish(rid, logidx, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.insert(rid, logidx));
                    let a0 = readonly_finish_refines(prev, post, b0.get_last(), r_points, rid, logidx, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_start(rid, uop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_start_refines(prev, post, b0.get_last(), r_points, rid, uop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_add_op_to_log(rid) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_add_update_to_log_refines(prev, post, b0.get_last(), r_points, rid);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::update_incr_version(logidx) => {
                    update_incr_version_refines(a, r_points, logidx)
                }
                SimpleLog::Step::update_finish(rid, resp) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_finish_refines(prev, post, b0.get_last(), r_points, rid, resp);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                SimpleLog::Step::no_op() => {
                    exists_equiv_behavior_rec(*tail, r_points)
                }
                SimpleLog::Step::dummy_to_use_type_params(state) => {
                    assert(false);  // nothing to be done here, this is not a real transition but
                    arbitrary()     // is being generated to make Rust happy w.r.t. type parameters
                }
            }
        }
        SimpleLogBehavior::Inited(sl_state) => {
            let st = AsynchronousSingleton::State {
                state: DT::init_spec(),
                reqs: Map::empty(),
                resps: Map::empty(),
            };
            let res =  AsynchronousSingletonBehavior::Inited(st);

            reveal(SimpleLog::State::init);
            reveal(SimpleLog::State::init_by);
            reveal(AsynchronousSingleton::State::init);
            reveal(AsynchronousSingleton::State::init_by);

            assert(AsynchronousSingleton::State::init_by(st, AsynchronousSingleton::Config::initialize()));
            res
        }
    }
}


// =================================================================================================
// Validity of Requests
// =================================================================================================


/// checks whether the version of the request with the given ID is OK           (Dafny: FutureRidOk)
spec fn future_rid_ok<DT: Dispatch>(s: SState<DT>, rid: ReqId, version: LogIdx) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Init() ==> s.version <= version
    &&& s.readonly_reqs[rid].is_Req()  ==> s.readonly_reqs[rid].get_Req_version() <= version
}

/// checks whether the versions of the requests are ok                       (Dafny: FuturePointsOk)
spec fn future_points_ok<DT: Dispatch>(s:SState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    &&& r_points.dom().finite()
    &&& (forall |rid| #[trigger]r_points.contains_key(rid) ==> future_rid_ok(s, rid, r_points[rid]))
}

/// checks whether the readonly requests are valid                                    (Dafny: rel_r)
/// in the simple log, we do not distinguish between requests and responses, but the AsyncSingleton
/// does, so we need to do a case distinction here.
spec fn readonly_requests_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    &&& (forall |rid| (#[trigger]s.readonly_reqs.contains_key(rid) && #[trigger]t.reqs.contains_key(rid))
            ==> readonly_request_is_valid(s, t, r_points, rid))
    &&& (forall |rid| (#[trigger]s.readonly_reqs.contains_key(rid) && #[trigger]t.resps.contains_key(rid))
            ==> readonly_response_is_valid(s, t, r_points, rid))
}

/// checks whether the readonly request is valid                            (Dafny: readonly_is_req)
spec fn readonly_request_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& (s.readonly_reqs[rid].is_Req() ==> s.readonly_reqs[rid].get_Req_version() <= s.version)

    &&& t.reqs.contains_key(rid)
    &&& t.reqs[rid] == InputOperation::<DT>::Read(s.readonly_reqs[rid].op())

    &&& (r_points.contains_key(rid) ==> {
        &&& s.version <= r_points[rid]
        &&& (s.readonly_reqs[rid].is_Req() ==> s.version < r_points[rid])
    })
}

/// checks whether the readonly response is valid                          (Dafny: readonly_is_resp)
spec fn readonly_response_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Req()
    &&& s.readonly_reqs[rid].get_Req_version() <= s.version

    &&& t.resps.contains_key(rid)

    &&& (r_points.contains_key(rid) ==> {
        &&& s.readonly_reqs[rid].get_Req_version() <= r_points[rid] && r_points[rid] <= s.version
        &&& 0 <= r_points[rid] && r_points[rid] <= s.log.len()
        &&& t.resps[rid] == OutputOperation::<DT>::Read(DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), s.readonly_reqs[rid].op()))
    })
}

/// checks whether the update response is valid                              (Dafny: update_is_done)
spec fn update_response_is_valid<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> bool {
    &&& s.update_resps.contains_key(rid)
    &&& s.update_resps[rid].0 < s.log.len()

    &&& t.resps.contains_key(rid)
    &&& t.resps[rid] == OutputOperation::<DT>::Write(
        DT::dispatch_mut_spec(s.nrstate_at_version(s.update_resps[rid].0), s.log[s.update_resps[rid].0 as int]).1
    )
}

/// checks whether the upate responses have versions that matche the log         (Dafny: HasVersion)
spec fn update_response_with_version(update_resps: Map<ReqId, UpdateResp>, version: LogIdx) -> bool
{
    exists |rid| #[trigger] update_resps.contains_key(rid) && update_resps[rid].0 == version
}


// =================================================================================================
// State Refinement Relation
// =================================================================================================


/// Basic State Refinement Relation                                               (Dafny: rel_basic)
/// sets the AsynchronousSingleton::State in realtion with the SimpleLog::State
spec fn state_refinement_relation_basic<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool {
    // the version must be valid w.r.t. to the log size
    &&& (0 <= s.version && s.version <= s.log.len())
    // the state corresponds to the state computed at the given version
    &&& t.state == s.nrstate_at_version(s.version)

    // the request ids of the readonly/update requests and responses must be unique
    &&& s.readonly_reqs.dom().disjoint( s.update_reqs.dom())
    &&& s.readonly_reqs.dom().disjoint( s.update_resps.dom())
    &&& s.update_reqs.dom().disjoint( s.update_resps.dom())
    &&& t.reqs.dom().disjoint(t.resps.dom())

    // requests are complete: if a request in present in the AState then it must be present in the SState
    &&& (forall |rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) || #[trigger] s.update_reqs.contains_key(rid) || #[trigger] s.update_resps.contains_key(rid))
        <==>
        (#[trigger] t.reqs.contains_key(rid) || #[trigger] t.resps.contains_key(rid))
    )

    // requests/responses in the rightmaps
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Read()
            ==> s.readonly_reqs.contains_key(rid))
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Write()
            ==> s.update_reqs.contains_key(rid) || s.update_resps.contains_key(rid))
    &&& (forall |rid| #[trigger] t.resps.contains_key(rid)
            ==> s.readonly_reqs.contains_key(rid) || s.update_resps.contains_key(rid))

    // for all log entries > version, there must be a response with the given version
    &&& (forall |v: LogIdx|  s.version <= v && v < s.log.len() ==> update_response_with_version(s.update_resps, v))

    // for any two update responses, if the request id differs, the version in the log must also differ
    &&& (forall |rid1, rid2| #[trigger] s.update_resps.contains_key(rid1) && #[trigger] s.update_resps.contains_key(rid2) && rid1 != rid2
            ==> s.update_resps[rid1] != s.update_resps[rid2])

    // for all update responses, the version must be within the log
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid)
            ==> s.update_resps[rid].0 < s.log.len())

    // for all update requests, they must be part of the requests and the operation must match
    &&& (forall |rid| #[trigger] s.update_reqs.contains_key(rid)
            ==> t.reqs.contains_key(rid) && t.reqs[rid] == InputOperation::<DT>::Write(s.update_reqs[rid]))

    // forall update responses larger than the current version, they must be in the requests,
    // the update operation must match
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 >= s.version ==> {
        &&& t.reqs.contains_key(rid)
        &&& t.reqs[rid] == InputOperation::<DT>::Write(s.log[s.update_resps[rid].0 as int])
    })

    // for all update responses smaller than th eversion, they must be valid
    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 < s.version ==>
        update_response_is_valid(s, t, r_points, rid)
    )
}

/// State Refinement Relation                                                           (Dafny: rel)
/// This relates the state of the SimpleLog and the AsyncSingleton to each other
spec fn state_refinement_relation<DT: Dispatch>(s:SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>) -> bool
{
    &&& state_refinement_relation_basic(s, t, r_points)
    &&& readonly_requests_valid(s, t, r_points)
}


// =================================================================================================
// State Transition Refinements: Read-Only Requests
// =================================================================================================


/// Refinement Proof of the ReadOnly_Start transition of the SimpleLog
///
/// This corresponds to the "Start" transition that introduces a new request into the system
proof fn readonly_start_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, rop: DT::ReadOperation) -> (t2: AState<DT>)
    requires
        SimpleLog::State::readonly_start(s, s2, rid, rop),
        state_refinement_relation(s, t, r_points.remove(rid)), future_points_ok(s2, r_points)
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) // one.Next(Is, Is', AI.Start(rid, nrifc.ROp(rop)))
{
    // Is' := Is.(reqs := Is.reqs[rid := nrifc.ROp(rop)]);
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs.insert(rid, InputOperation::Read(rop)),
        resps: t.resps,
    };

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::start(rid, InputOperation::Read(rop))));

    res
}

/// Refinement Proof of the Readonly_ReadVersion transition of the SimpleLog
///
/// This corresponds to an "InternalOp" transition
proof fn readonly_read_version_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::readonly_read_version(s, s2, rid),
        state_refinement_relation(s, t, r_points), future_points_ok(s2, r_points)
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) // one.Next(Is, Is', AI.InternalOp)
{
    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    if r_points.contains_key(rid) && r_points[rid] == s.version {
        let op =  s.readonly_reqs[rid].get_Init_op();

        // remind verus that the request id is known!
        assert(t.reqs.contains_key(rid) || t.resps.contains_key(rid));

        let retval = DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), op);

        // Is' := Is.(reqs := Is.reqs - {rid})
        //         .(resps := Is.resps[rid := retval]);
        let res = AsynchronousSingleton::State {
            state: t.state,
            reqs: t.reqs.remove(rid),
            resps: t.resps.insert(rid, OutputOperation::Read(retval)),
        };

        assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::internal_next(rid, InputOperation::Read(op), OutputOperation::Read(retval))));
        res
    } else {
        // if the request id is not part of the supplied r_points then this corresponds to a no-op
        assert(AsynchronousSingleton::State::next_by(t, t, AsynchronousSingleton::Step::no_op()));
        t
    }
}

/// Refinement Proof of the Readonly_Finish transition of the SimpleLog
///
/// This corresponds to a "End" transition where a response leaves the system
proof fn readonly_finish_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, version: LogIdx, ret: DT::Response) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::readonly_finish(s, s2, rid, version, ret),
        state_refinement_relation(s, t, r_points.insert(rid, version)),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) // one.Next(Is, Is', AI.End(rid, return_value))
{
    // Is' := Is.(resps := Is.resps - {rid});
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs,
        resps: t.resps.remove(rid),
    };

    if t.reqs.contains_key(rid) {
        assert(false); // proof by contradiction
    } else {
        assert(t.resps.contains_key(rid));
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::end(rid,  OutputOperation::Read(ret))));
    res
}


// =================================================================================================
// State Transition Refinements: Update Requests
// =================================================================================================


/// Refinement Proof of the Update_Start transition of the SimpleLog
///
/// This corresponds to the "Start" transition that introduces a new request into the system
proof fn update_start_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, uop: DT::WriteOperation) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_start(s, s2, rid, uop),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) //  one.Next(Is, Is', AI.Start(rid, nrifc.UOp(uop)))
{
    //  Is' := Is.(reqs := Is.reqs[rid := nrifc.UOp(uop)]);
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs.insert(rid, InputOperation::Write(uop)),
        resps: t.resps,
    };

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::start(rid,  InputOperation::Write(uop))));
    res
}


/// Refinement Proof of the Update_AddUpdateToLog transition of the SimpleLog
///
/// This corresponds to an "InternalOp transition"
proof fn update_add_update_to_log_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_add_op_to_log(s, s2, rid),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) //  one.Next(Is, Is', AI.InternalOp)
{
    state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.version);

    assert forall |r| #[trigger] s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r)
        ==> readonly_response_is_valid(s2, t, r_points, r) by {
        if s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r) {
            if r_points.contains_key(r) {
                state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], r_points[r]);
            }
        }
    }

    assert forall |r| (#[trigger] s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version)
        ==> update_response_is_valid(s2, t, r_points, r) by {
        if s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version {
            state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.update_resps[r].0);
        }
    }

    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> update_response_with_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            if v < s2.log.len() - 1 {
                assert(update_response_with_version(s.update_resps, v));
                let qid = choose|qid| #[trigger]s.update_resps.contains_key(qid) && s.update_resps[qid].0 == v;
                assert(s2.update_resps.contains_key(qid) && s2.update_resps[qid].0 == v);
            } else {
                assert(s2.update_resps.contains_key(rid) && s2.update_resps[rid].0 == v);
            }
        }
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, t, AsynchronousSingleton::Step::no_op()));
    t
}


/// Refinement Proof ot the Update_Finish transition of the SimpleLog
///
/// This corresponds to the "End" transition that removes a response from the system
proof fn update_finish_refines<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t: AState<DT>, r_points: Map<ReqId, LogIdx>, rid: ReqId, resp: DT::Response) -> ( t2: AState<DT>)
    requires
        SimpleLog::State::update_finish(s, s2, rid, resp),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) //  one.Next(Is, Is', AI.End(rid, return_value))
{
    // Is' := Is.(resps := Is.resps - {rid});
    let res = AsynchronousSingleton::State {
        state: t.state,
        reqs: t.reqs,
        resps: t.resps.remove(rid),
    };

    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> update_response_with_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            assert(update_response_with_version(s.update_resps, v));
            let qid = choose|qid| #[trigger]s.update_resps.contains_key(qid) && s.update_resps[qid].0 == v;
            assert(s2.update_resps.contains_key(qid) && s2.update_resps[qid].0 == v);

        }
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::end(rid, OutputOperation::Write(resp))));
    res
}


/// Refinement Proof of the Update_IncrVersion transition of the SimpleLog
///
/// This corresponds to an internal, or next transition
proof fn update_incr_version_refines<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>, new_version: LogIdx) -> (b: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(), future_points_ok(a.get_last(), r_points), a.is_Stepped(), a.get_Stepped_1().is_Internal(),
        SimpleLog::State::update_incr_version(a.get_Stepped_2().get_last(), a.get_last(), new_version),
    ensures
        b.wf(), behavior_equiv(a, b), state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases
        *a.get_Stepped_2(), 1nat, new_version
{
    if new_version == a.get_Stepped_2().get_last().version {
        exists_equiv_behavior_rec(*a.get_Stepped_2(), r_points)
    } else {
        /* var amid := a.(s := a.s.(ctail := a.s.ctail - 1)); */
        let mut new_st = a.get_Stepped_0();
        new_st.version = (new_st.version - 1) as nat;
        let amid = SimpleLogBehavior::Stepped(
            new_st,
            a.get_Stepped_1(),
            a.get_Stepped_2(),
        );

        reveal(SimpleLog::State::next);
        reveal(SimpleLog::State::next_by);
        assert(SimpleLog::State::next_by(amid.get_Stepped_2().get_last(), amid.get_last(), SimpleLog::Step::update_incr_version((new_version - 1) as nat)));

        let bmid = update_incr_version_refines(amid, r_points, (new_version - 1) as LogIdx);
        update_incr_version_1_refines(bmid, amid, a, r_points)
    }
}


proof fn update_incr_version_1_refines<DT: Dispatch>(b: AsynchronousSingletonBehavior<DT>, a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>) -> (b2: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(), future_points_ok(a2.get_last(), r_points),
        a.is_Stepped() && a2.is_Stepped(),
        a.get_Stepped_2() == a2.get_Stepped_2(), // a.tail == a'.tail
        a.get_Stepped_1().is_Internal() && a2.get_Stepped_1().is_Internal(),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
        a.get_last().version + 1 <= a.get_last().log.len(),
        b.wf(),
        behavior_equiv(a, b),
        state_refinement_relation(a.get_last(), b.get_last(), r_points)
    ensures
        b2.wf(), behavior_equiv(a2, b2), state_refinement_relation(a2.get_last(), b2.get_last(), r_points)
{
    let s = a.get_last();
    let s2 = a2.get_last();

    assert(s.version < s.log.len());
    assert(update_response_with_version(s.update_resps, s.version));

    let urid  = choose |urid| #[trigger] s.update_resps.contains_key(urid) && s.update_resps[urid].0 == s.version;

    let x = DT::dispatch_mut_spec(s.nrstate_at_version(s.update_resps[urid].0), s.log[s.update_resps[urid].0 as int]);
    let uret = x.1;

    let input = InputOperation::Write(s.log[s.update_resps[urid].0 as int]);
    let output = OutputOperation::Write(uret);

    let st = AsynchronousSingleton::State {
        state: x.0,
        reqs: b.get_last().reqs.remove(urid),
        resps: b.get_last().resps.insert(urid, output),
    };
    let b2 = AsynchronousSingletonBehavior::Stepped(st, AsyncLabel::Internal, Box::new(b));

    assert(b2.wf()) by {
        reveal(AsynchronousSingleton::State::next);
        reveal(AsynchronousSingleton::State::next_by);
        assert(AsynchronousSingleton::State::next_by(b2.get_Stepped_2().get_last(), b2.get_last(), AsynchronousSingleton::Step::internal_next(urid, input, output)));
    }


    assert(behavior_equiv(a2, b2)) by { trick_equiv(a, a2, b2); }

    let the_reads = all_reads_for::<DT>(s.readonly_reqs, r_points, s.version + 1);
    update_incr_version_1_read_reqs(b2, a, a2, r_points, the_reads)
}

spec fn simple_log_state_equiv_inc_version<DT: Dispatch>(a: SState<DT>, a2: SState<DT>) -> bool {
    // a'.s == a.s.(ctail := a.s.ctail + 1)
    &&& a2.log == a.log
    &&& a2.version == a.version + 1
    &&& a2.readonly_reqs == a.readonly_reqs
    &&& a2.update_reqs == a.update_reqs
    &&& a2.update_resps == a.update_resps
}

spec fn recursion_invariant<DT: Dispatch>(s: SState<DT>, s2: SState<DT>, t2: AState<DT>, r_points: Map<ReqId, LogIdx>, the_reads: Set<ReqId>) -> bool {
    &&& the_reads.finite()
    &&& s.version + 1 <= s.log.len()
    &&&  state_refinement_relation_basic(s2, t2, r_points)
    &&& (forall |rid| #[trigger]the_reads.contains(rid) ==> {
        &&& r_points.contains_key(rid)
        &&& r_points[rid] == s.version + 1
        &&& s.readonly_reqs.contains_key(rid)
        &&& s.readonly_reqs[rid].is_Req()
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
        !the_reads.contains(rid) ==> readonly_request_is_valid(s2, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
        !the_reads.contains(rid) ==> readonly_response_is_valid(s2, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.reqs.contains_key(rid) ==> {
        the_reads.contains(rid) ==> readonly_request_is_valid(s, t2, r_points, rid)
    })
    &&& (forall |rid| #[trigger]s.readonly_reqs.contains_key(rid) && t2.resps.contains_key(rid) ==> {
        the_reads.contains(rid) ==> readonly_response_is_valid(s, t2, r_points, rid)
    })
}

proof fn update_incr_version_1_read_reqs<DT: Dispatch>(b2: AsynchronousSingletonBehavior<DT>, a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, r_points: Map<ReqId, LogIdx>, the_reads: Set<ReqId>) -> (res: AsynchronousSingletonBehavior<DT>)
    requires
        b2.wf(), behavior_equiv(a2, b2),
        recursion_invariant(a.get_last(), a2.get_last(), b2.get_last(), r_points, the_reads),
        simple_log_state_equiv_inc_version(a.get_last(), a2.get_last()),
    ensures
        res.wf(), behavior_equiv(a2, res),
        recursion_invariant(a.get_last(), a2.get_last(), res.get_last(), r_points, Set::<ReqId>::empty()),
    decreases
        the_reads.len()
{
    if the_reads.is_empty() {
        assert(the_reads =~= Set::empty());
        b2
    } else {
        let s = a.get_last();
        let s2 = a2.get_last();

        let (the_reads2, rid) = pop_rid(the_reads);

        let ret = DT::dispatch_spec(s.nrstate_at_version(r_points[rid]), s.readonly_reqs[rid].op());
        let input = InputOperation::<DT>::Read(s.readonly_reqs[rid].op());
        let output = OutputOperation::Read(ret);

        let st = AsynchronousSingleton::State {
            state: b2.get_last().state,
            reqs: b2.get_last().reqs.remove(rid),
            resps: b2.get_last().resps.insert(rid, output),
        };
        let b2_new = AsynchronousSingletonBehavior::Stepped(st, AsyncLabel::Internal, Box::new(b2));

        assert(b2_new.wf()) by {
            reveal(AsynchronousSingleton::State::next);
            reveal(AsynchronousSingleton::State::next_by);
            assert(AsynchronousSingleton::State::internal_next(b2.get_last(), b2_new.get_last(), rid, input, output));
            assert(AsynchronousSingleton::State::next_by(b2.get_last(), b2_new.get_last(),
                AsynchronousSingleton::Step::internal_next(rid, input, output)
            ));
        }

        update_incr_version_1_read_reqs(b2_new, a, a2, r_points, the_reads2)
    }
}


// =================================================================================================
// Utility Functions
// =================================================================================================

/// Shows that adding an entry to the log doesn't change the state
proof fn state_at_version_preserves<DT: Dispatch>(a: Seq<DT::WriteOperation>, b: Seq<DT::WriteOperation>, x: DT::WriteOperation, i: LogIdx)
    requires b == a.push(x), i <= a.len(), i <= b.len()
    ensures compute_nrstate_at_version::<DT>(a, i) == compute_nrstate_at_version::<DT>(b, i)
    decreases i
{
    if i > 0 {
        state_at_version_preserves::<DT>(a, b, x, (i-1) as LogIdx);
    }
}

/// Removes an element from the set, returning it, maintaining finitenes property
/// XXX: something like this shoudl go intot he stdlib...
proof fn pop_rid(t: Set<ReqId>) -> (res: (Set<ReqId>, ReqId))
    requires !t.is_empty(), t.finite()
    ensures res.0.len() < t.len(), t.contains(res.1), res.0 =~= t.remove(res.1), res.0.finite()
{
    let r = t.choose();
    (t.remove(r), r)
}

/// Shows the behavior equivalency under specific condition
proof fn trick_equiv<DT: Dispatch>(a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, b: AsynchronousSingletonBehavior<DT>)
    requires
        behavior_equiv(a, b), a.is_Stepped(), a2.is_Stepped(), a.get_Stepped_2() == a2.get_Stepped_2(),
        a.get_Stepped_1().is_Internal(), a2.get_Stepped_1().is_Internal()
    ensures
        behavior_equiv(a2, b)
    decreases b
{
    if !b.is_Inited() &&  behavior_equiv(a, *b.get_Stepped_2()) {
        trick_equiv(a, a2, *b.get_Stepped_2());
    }
}


/// Constructs a set of Requests IDs that corresponds to ReadOnly requests and that are currently
/// in the r_points set and have a version that matches the input
spec fn all_reads_for<DT: Dispatch>(readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>, r_points: Map<ReqId, LogIdx>, version: LogIdx) -> Set<ReqId>
    recommends r_points.dom().finite()
{
    r_points.dom().filter(|rid| r_points[rid] == version && readonly_reqs.contains_key(rid) && readonly_reqs[rid].is_Req())
}


} // end verus!