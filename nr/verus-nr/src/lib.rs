// trustedness: ignore this file

// TODO fix?
// #![feature(register_tool)]
// #![register_tool(verifier)]

#[allow(unused_imports)]
use builtin::*;
use vstd::*;
use vstd::seq::*;
use vstd::prelude::*;
use state_machines_macros::state_machine;

mod spec;
mod exec;
pub mod constants;

pub use crate::exec::context::ThreadToken;
pub use crate::exec::NodeReplicated;
pub use crate::exec::replica::ReplicaId;

#[cfg(feature = "counter_dispatch_example")]
mod counter_dispatch_example;

verus! {

global size_of usize == 8;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nr State and its operations
////////////////////////////////////////////////////////////////////////////////////////////////////

// the following types are currently arbitrary, the depend on the the actual data structure that
// each replica wraps. The NR crate has this basically as a trait that the data structure must
// implement.

/// type of the node / replica id
pub type NodeId = nat;

/// the log index
pub type LogIdx = nat;

/// the request id
pub type ReqId = nat;

/// the id of a thread on a replica node
pub type ThreadId = nat;


pub trait Dispatch: Sized {
    /// A read-only operation. When executed against the data structure, an
    /// operation of this type must not mutate the data structure in any way.
    /// Otherwise, the assumptions made by NR no longer hold.
    type ReadOperation: Sized;

    /// A write operation. When executed against the data structure, an
    /// operation of this type is allowed to mutate state. The library ensures
    /// that this is done so in a thread-safe manner.
    type WriteOperation: Sized + Send;

    /// The type on the value returned by the data structure when a
    /// `ReadOperation` or a `WriteOperation` successfully executes against it.
    type Response: Sized;

    // Self is the concrete type

    ///
    type View;

    spec fn view(&self) -> Self::View;

    fn init() -> (res: Self)
        ensures res@ == Self::init_spec();

    // partial eq also add an exec operation
    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation)
        ensures op == res;

    fn clone_response(op: &Self::Response) -> (res: Self::Response)
        ensures op == res;

    /// Method on the data structure that allows a read-only operation to be
    /// executed against it.
    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response)
        ensures Self::dispatch_spec(self@, op) == result
        ;

    /// Method on the data structure that allows a write operation to be
    /// executed against it.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response)
        ensures Self::dispatch_mut_spec(old(self)@, op) == (self@, result);

    spec fn init_spec() -> Self::View;

    spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response;

    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (Self::View, Self::Response);
}


// use crate::exec::context::ThreadToken;
use crate::spec::unbounded_log::UnboundedLog;

pub open spec fn is_readonly_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_reads<DT>,
    op: DT::ReadOperation,
    log: UnboundedLog::Instance<DT>) -> bool
{
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value.is_Init() && ticket@.value.get_Init_op() == op
    // requires ticket.loc == TicketStubSingletonLoc.loc()
    &&& ticket@.instance == log
}

pub open spec fn is_readonly_stub<DT: Dispatch>(
    stub: UnboundedLog::local_reads<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists ctail, op, nodeid :: stub == ReadOp(rid, ReadonlyDone(op, output, nodeid, ctail)))
    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}


pub open spec fn is_update_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_updates<DT>,
    op: DT::WriteOperation,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value.is_Init() && ticket@.value.get_Init_op() == op
    // requires ticket.loc == TicketStubSingletonLoc.loc()
    &&& ticket@.instance == log
}

pub open spec fn is_update_stub<DT: Dispatch>(
    stub: UnboundedLog::local_updates<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists log_idx :: stub == UpdateOp(rid, UpdateDone(output, log_idx)))
    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}

pub trait ThreadTokenT<DT: Dispatch, Replica> {
    spec fn wf(&self, replica: &Replica) -> bool;

    spec fn replica_id_spec(&self) -> nat;
}

pub trait NR<DT: Dispatch + Sync>: Sized {
    type Replica;
    type ReplicaId;
    type TT: ThreadTokenT<DT, Self::Replica>;

    spec fn wf(&self) -> bool;

    spec fn replicas(&self) -> Vec<Box<Self::Replica>>;

    spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT>;

    // TODO this does not properly ensures initialization I think
    // I think it needs to return the correct initialization token
    fn new(num_replicas: usize) -> (res: Self)
        requires
            0 < num_replicas && num_replicas <= crate::constants::MAX_REPLICAS
        ensures
            res.wf(),
            res.replicas().len() == num_replicas;

    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<Self::TT>)
        requires old(self).wf(),
        ensures
            self.wf(),
            result.is_Some() ==> result.get_Some_0().wf(&self.replicas()[replica_id as int]);

    fn execute_mut(&self, op: DT::WriteOperation, tkn: Self::TT, ticket: Tracked<UnboundedLog::local_updates<DT>>)
        -> (result: Result<(DT::Response, Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
                           (Self::TT, Tracked<UnboundedLog::local_updates<DT>>) > )
        requires
            self.wf(), // wf global node
            tkn.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            is_update_ticket(ticket@, op, self.unbounded_log_instance())
        ensures
            result.is_Ok() ==> is_update_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.unbounded_log_instance()) && result.get_Ok_0().1.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn;

    fn execute(&self, op: DT::ReadOperation, tkn: Self::TT,  ticket: Tracked<UnboundedLog::local_reads<DT>>)
            -> (result: Result<(DT::Response, Self::TT, Tracked<UnboundedLog::local_reads<DT>>), (Self::TT, Tracked<UnboundedLog::local_reads<DT>>)>)
        requires
            self.wf(), // wf global node
            tkn.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            is_readonly_ticket(ticket@, op, self.unbounded_log_instance())
        ensures
            result.is_Ok() ==> is_readonly_stub(result.get_Ok_0().2@, ticket@@.key, result.get_Ok_0().0, self.unbounded_log_instance()) && result.get_Ok_0().1.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn;
}


spec fn implements_NodeReplicated<DT: Dispatch + Sync, N: NR<DT>>() -> bool { true }

proof fn theorem_1<DT: Dispatch + Sync>()
    ensures implements_NodeReplicated::<DT, NodeReplicated<DT>>(),
{ }


use crate::spec::simple_log::SimpleLog;

pub open spec fn add_ticket<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    input: InputOperation<DT>,
    rid: RequestId) -> bool
{
    !pre.local_reads.dom().contains(rid)
    && !pre.local_updates.dom().contains(rid)
    && (match input {
        InputOperation::Read(read_op) => {
            && post == UnboundedLog::State::<DT> {
                local_reads: pre.local_reads.insert(rid, crate::spec::unbounded_log::ReadonlyState::Init { op: read_op }),
                .. pre
            }
        }
        InputOperation::Write(write_op) => {
            && post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(rid, crate::spec::unbounded_log::UpdateState::Init { op: write_op }),
                .. pre
            }
        }
    })
}

pub open spec fn consume_stub<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    output: OutputOperation<DT>,
    rid: RequestId) -> bool
{
    match output {
        OutputOperation::Read(response) => {
            pre.local_reads.dom().contains(rid)
            && pre.local_reads[rid].is_Done()
            && pre.local_reads[rid].get_Done_ret() == response
            && post == UnboundedLog::State::<DT> {
              local_reads: pre.local_reads.remove(rid),
              .. pre
            }
        }
        OutputOperation::Write(response) => {
            pre.local_updates.dom().contains(rid)
            && pre.local_updates[rid].is_Done()
            && pre.local_updates[rid].get_Done_ret() == response
            && post == UnboundedLog::State::<DT> {
              local_updates: pre.local_updates.remove(rid),
              .. pre
            }
        }
    }
}

trait UnboundedLogRefinesSimpleLog<DT: Dispatch> {
    spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT>;

    // Prove that it is always possible to add a new ticket
    spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> RequestId;

    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>)
        requires pre.invariant(),
        ensures
            !pre.local_reads.dom().contains(Self::get_fresh_rid(pre)),
            !pre.local_updates.dom().contains(Self::get_fresh_rid(pre));

    proof fn refinement_inv(vars: UnboundedLog::State<DT>)
        requires vars.invariant(),
        ensures Self::interp(vars).invariant();

    proof fn refinement_init(post: UnboundedLog::State<DT>)
        requires
            post.invariant(),
            UnboundedLog::State::init(post)
        ensures
            SimpleLog::State::init(Self::interp(post));

    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
            post.invariant(),
            UnboundedLog::State::next_strong(pre, post),
        ensures
            SimpleLog::State::next(Self::interp(pre), Self::interp(post));

    proof fn refinement_add_ticket(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: InputOperation<DT>,
    )
        requires
            pre.invariant(),
            add_ticket(pre, post, input, Self::get_fresh_rid(pre)),
        ensures
            post.invariant(),
            SimpleLog::State::next(Self::interp(pre), Self::interp(post));

    proof fn refinement_consume_stub(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: RequestId
    )
        requires
            pre.invariant(),
            consume_stub(pre, post, output, rid),
        ensures
            post.invariant(),
            SimpleLog::State::next(Self::interp(pre), Self::interp(post));
}

spec fn implements_UnboundedLogRefinesSimpleLog<DT: Dispatch, RP: UnboundedLogRefinesSimpleLog<DT>>() -> bool { true }

proof fn theorem_2<DT: Dispatch + Sync>()
    ensures implements_UnboundedLogRefinesSimpleLog::<DT, crate::spec::unbounded_log_refines_simplelog::RefinementProof<DT>>(),
{ }

#[is_variant]
pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation),
    Write(DT::WriteOperation),
}

#[is_variant]
pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}

#[is_variant]
pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(RequestId, InputOperation<DT>),
    End(RequestId, OutputOperation<DT>),
}

type RequestId = nat;

state_machine!{ AsynchronousSingleton<DT: Dispatch> {
    fields {
        pub state: DT::View,
        pub reqs: Map<RequestId, InputOperation<DT>>,
        pub resps: Map<RequestId, OutputOperation<DT>>,
    }

    //pub type Label<DT> = AsyncLabel<DT>;

    init!{
        initialize() {
            init state = DT::init_spec();
            init reqs = Map::empty();
            init resps = Map::empty();
        }
    }

    transition!{
        internal_next(rid: RequestId, input: InputOperation<DT>, output: OutputOperation<DT>) {
            require pre.reqs.dom().contains(rid);
            require pre.reqs[rid] == input;
            update reqs = pre.reqs.remove(rid);
            update resps = pre.resps.insert(rid, output);

            match input {
                InputOperation::Read(read_op) => {
                    require output === OutputOperation::Read(DT::dispatch_spec(pre.state, read_op));
                }
                InputOperation::Write(write_op) => {
                    let (next_state, out) = DT::dispatch_mut_spec(pre.state, write_op);
                    require output === OutputOperation::Write(out);
                    update state = next_state;
                }
            }
        }
    }

    transition!{
        no_op() {
            /* stutter step */
        }
    }

    transition!{
        start(rid: RequestId, input: InputOperation<DT>) {
            require !pre.reqs.dom().contains(rid);
            update reqs = pre.reqs.insert(rid, input);
        }
    }

    transition!{
        end(rid: RequestId, output: OutputOperation<DT>) {
            require pre.resps.dom().contains(rid);
            require pre.resps[rid] == output;
            update resps = pre.resps.remove(rid);
        }
    }
}}

#[is_variant]
pub enum SimpleLogBehavior<DT: Dispatch> {
    Stepped(SimpleLog::State<DT>, AsyncLabel<DT>, Box<SimpleLogBehavior<DT>>),
    Inited(SimpleLog::State<DT>),
}

pub open spec fn async_op_matches<DT: Dispatch>(pre: SimpleLog::State<DT>, post:SimpleLog::State<DT>, op: AsyncLabel<DT>) -> bool
    recommends exists |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(pre, post, step)
{
    let step = choose |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(pre, post, step);
    match step {
         SimpleLog::Step::readonly_start(rid, rd_op)=> op == AsyncLabel::Start(rid, InputOperation::<DT>::Read(rd_op)),
         SimpleLog::Step::readonly_read_version(_rid) => op.is_Internal(),
         SimpleLog::Step::readonly_finish(rid, _logidx, resp) => op == AsyncLabel::End(rid, OutputOperation::<DT>::Read(resp)),
         SimpleLog::Step::update_start(rid, wr_op)=> op == AsyncLabel::Start(rid, InputOperation::<DT>::Write(wr_op)),
        //  SimpleLog::Step::update_add_ops_to_log(_rids) => op.is_Internal(),
         SimpleLog::Step::update_add_op_to_log(_rid) => op.is_Internal(),
         SimpleLog::Step::update_incr_version(_logidx) => op.is_Internal(),
         SimpleLog::Step::update_finish(rid, resp) => op == AsyncLabel::End(rid, OutputOperation::<DT>::Read(resp)),
         SimpleLog::Step::no_op() => op.is_Internal(),
         SimpleLog::Step::dummy_to_use_type_params(_st) => op.is_Internal(),
    }
}

impl<DT: Dispatch> SimpleLogBehavior<DT> {
    pub open spec fn get_last(self) -> SimpleLog::State<DT> {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => post,
            SimpleLogBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            SimpleLogBehavior::Stepped(post, op, tail) => {
                tail.wf() && SimpleLog::State::next(/* op, */ tail.get_last(), post)
                && async_op_matches(tail.get_last(), post, op)
            }
            SimpleLogBehavior::Inited(post) => {
                SimpleLog::State::init(post)
            }
        }
    }
}

#[is_variant]
pub enum AsynchronousSingletonBehavior<DT: Dispatch> {
    Stepped(AsynchronousSingleton::State<DT>, AsyncLabel<DT>, Box<AsynchronousSingletonBehavior<DT>>),
    Inited(AsynchronousSingleton::State<DT>),
}

impl<DT: Dispatch> AsynchronousSingletonBehavior<DT> {
    pub open spec fn get_last(self) -> AsynchronousSingleton::State<DT> {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => post,
            AsynchronousSingletonBehavior::Inited(post) => post,
        }
    }

    pub open spec fn wf(self) -> bool
        decreases self,
    {
        match self {
            AsynchronousSingletonBehavior::Stepped(post, op, tail) => {
                tail.wf() && AsynchronousSingleton::State::next(/* op, */ tail.get_last(), post)
            }
            AsynchronousSingletonBehavior::Inited(post) => {
                AsynchronousSingleton::State::init(post)
            }
        }
    }
}

pub open spec fn behavior_equiv<DT: Dispatch>(a: SimpleLogBehavior<DT>, b: AsynchronousSingletonBehavior<DT>) -> bool
    decreases a, b
{
    // (a.Inited? && b.Inited?)
    ||| (a.is_Inited() && b.is_Inited())
    // || (a.Stepped? && a.op.InternalOp? && equiv(a.tail, b))
    ||| (a.is_Stepped() && a.get_Stepped_1().is_Internal() && behavior_equiv(*a.get_Stepped_2(), b))
    // || (b.Stepped? && b.op.InternalOp? && equiv(a, b.tail))
    ||| (b.is_Stepped() && b.get_Stepped_1().is_Internal() && behavior_equiv(a, *b.get_Stepped_2()))
    // || (a.Stepped? && b.Stepped? && a.op == b.op && equiv(a.tail, b.tail))
    ||| (a.is_Stepped() && b.is_Stepped() &&  a.get_Stepped_1() == b.get_Stepped_1() && behavior_equiv(*a.get_Stepped_2(), *b.get_Stepped_2()))


    // // We can either take an 'internal' step on a and do nothing on b
    // || (match a {
    //     SimpleLogBehavior::Stepped(state, op, tail) => op.is_Internal() && behavior_equiv(*tail, b),
    //     _ => false
    // })
    // // Or an 'internal' step on b and nothing on a
    // || (match b {
    //     AsynchronousSingletonBehavior::Stepped(state, op, tail) => op.is_Internal() && behavior_equiv(a, *tail),
    //     _ => false,
    // })
    // // Or take the same step on both
    // || (match a {
    //     SimpleLogBehavior::Stepped(_state1, op1, tail1) => {
    //         match b {
    //             AsynchronousSingletonBehavior::Stepped(_state2, op2, tail2) => op1 == op2 && behavior_equiv(*tail1, *tail2),
    //             _ => false,
    //         }
    //     }
    //     _ => false
    // })
}

trait SimpleLogRefinesAsynchronousSingleton<DT: Dispatch> {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<DT>)
        requires a.wf(),
        ensures b.wf() && behavior_equiv(a, b);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Linearization Proof
////////////////////////////////////////////////////////////////////////////////////////////////////

use crate::spec::simple_log::UpdateResp;

/// checks whether the version of a single request id is ok (FutureRidOk)
spec fn future_rid_ok<DT: Dispatch>(s:SimpleLog::State<DT>, rid: RequestId, version: LogIdx) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Init() ==> s.version <= version
    &&& s.readonly_reqs[rid].is_Req() ==> s.readonly_reqs[rid].get_Req_version() <= version
}

/// checks whether the version of the request ids are ok (FuturePointsOk)
spec fn future_points_ok<DT: Dispatch>(s:SimpleLog::State<DT>, r_points: Map<RequestId, LogIdx>) -> bool {
    forall |rid| #[trigger] r_points.contains_key(rid) ==> future_rid_ok(s, rid, r_points[rid])
}

/// checks whether the readonly requests are valid  (rel_r)
spec fn readonly_requests_valid<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>) -> bool {
    &&& (forall |rid| (#[trigger] s.readonly_reqs.contains_key(rid) && #[trigger] t.reqs.contains_key(rid) )==> readonly_request_is_valid(s, t, r_points, rid))
    &&& (forall |rid| (#[trigger] s.readonly_reqs.contains_key(rid) && #[trigger] t.resps.contains_key(rid)) ==> readonly_response_is_valid(s, t, r_points, rid))
}

/// checks whether the readonly request is valid  (readonly_is_req)
spec fn readonly_request_is_valid<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& (s.readonly_reqs[rid].is_Req() ==> s.readonly_reqs[rid].get_Req_version() <= s.version)

    &&& t.reqs.contains_key(rid)
    &&& t.reqs[rid] == InputOperation::<DT>::Read(s.readonly_reqs[rid].op())

    &&& (r_points.contains_key(rid) ==> {
        &&& s.version <= r_points[rid]
        &&& (s.readonly_reqs[rid].is_Req() ==> s.version < r_points[rid])
    })
}

/// checks whether the readonly response is valid (readonly_is_resp)
spec fn readonly_response_is_valid<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId) -> bool {
    &&& s.readonly_reqs.contains_key(rid)
    &&& s.readonly_reqs[rid].is_Req()
    &&& s.readonly_reqs[rid].get_Req_version() <= s.version

    &&& t.resps.contains_key(rid)

    &&& (r_points.contains_key(rid) ==> {
        &&& s.readonly_reqs[rid].get_Req_version() <= r_points[rid] && r_points[rid] <= s.version
        &&& 0 <= r_points[rid] && r_points[rid] <= s.log.len()
        &&& t.resps[rid] == OutputOperation::<DT>::Read(DT::dispatch_spec(s.nrstate_at_version(r_points[rid]),  s.readonly_reqs[rid].op()))
    })
}

/// checks whether the update response is valid  (update_is_done)
spec fn update_response_is_valid<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId) -> bool {
    &&& s.update_resps.contains_key(rid)
    &&& s.update_resps[rid].0 < s.log.len()

    &&& t.resps.contains_key(rid)
    &&& t.resps[rid] == OutputOperation::<DT>::Write(
        DT::dispatch_mut_spec(s.nrstate_at_version(s.update_resps[rid].0), s.log[s.update_resps[rid].0 as int]).1
    )
}

/// checks whether the upate responses have versions that matche the log  (HasVersion)
spec fn log_has_version(update_resps: Map<RequestId, UpdateResp>, version: LogIdx) -> bool
{
    exists |rid| #[trigger] update_resps.contains_key(rid) && update_resps[rid].0 == version
}

/// basic state relation  (rel_basic)
spec fn state_refinement_relation_basic<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>) -> bool {
    &&& (0 <= s.version && s.version <= s.log.len())
    &&& t.state == s.nrstate_at_version(s.version)

    &&& s.readonly_reqs.dom().disjoint( s.update_reqs.dom())
    &&& s.readonly_reqs.dom().disjoint( s.update_resps.dom())
    &&& s.update_reqs.dom().disjoint( s.update_resps.dom())
    &&& t.reqs.dom().disjoint(t.resps.dom())

    // the requests must be present in both, and in the right map
    &&& (forall |rid|
        (#[trigger] s.readonly_reqs.contains_key(rid) || #[trigger] s.update_reqs.contains_key(rid) || #[trigger] s.update_resps.contains_key(rid))
        <==>
        (#[trigger] t.reqs.contains_key(rid) || #[trigger] t.resps.contains_key(rid))
    )
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Read() ==> s.readonly_reqs.contains_key(rid))
    &&& (forall |rid| #[trigger] t.reqs.contains_key(rid) && #[trigger] t.reqs[rid].is_Write() ==> s.update_reqs.contains_key(rid) || s.update_resps.contains_key(rid))
    &&& (forall |rid| #[trigger] t.resps.contains_key(rid) ==> s.readonly_reqs.contains_key(rid) || s.update_resps.contains_key(rid))

    // check if there is a update
    &&& (forall |v: LogIdx|  s.version <= v && v < s.log.len() ==> log_has_version(s.update_resps, v))

    &&& (forall |rid1, rid2| #[trigger] s.update_resps.contains_key(rid1) && #[trigger] s.update_resps.contains_key(rid2) && rid1 != rid2
            ==> s.update_resps[rid1] != s.update_resps[rid2])

    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) ==> s.update_resps[rid].0 < s.log.len())

    &&& (forall |rid| #[trigger] s.update_reqs.contains_key(rid) ==> t.reqs.contains_key(rid) && t.reqs[rid] == InputOperation::<DT>::Write(s.update_reqs[rid]))

    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 >= s.version ==> {
        &&& t.reqs.contains_key(rid)
        &&& 0 <= s.update_resps[rid].0 &&  s.update_resps[rid].0 < s.log.len()
        &&& t.reqs[rid] == InputOperation::<DT>::Write(s.log[s.update_resps[rid].0 as int])
    })

    &&& (forall |rid| #[trigger] s.update_resps.contains_key(rid) && s.update_resps[rid].0 < s.version ==>
        update_response_is_valid(s, t, r_points, rid)
    )
}

/// relates the state between the two points state machines  (rel)
spec fn state_refinement_relation<DT: Dispatch>(s:SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>) -> bool
{
    &&& state_refinement_relation_basic(s, t, r_points)
    &&& readonly_requests_valid(s, t, r_points)
}


//--------------------------------------------------------------------------------------------------
// Readonly Transition Refinements
//--------------------------------------------------------------------------------------------------

// simple.Variables -> SimpleLog::State<DT>
// one.Variables -> AsynchronousSingleton::State<DT>

proof fn readonly_start_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId, rop: DT::ReadOperation) -> ( t2: AsynchronousSingleton::State<DT>)
    requires
        SimpleLog::State::readonly_start(s, s2, rid, rop),
        state_refinement_relation(s, t, r_points.remove(rid)),
        future_points_ok(s2, r_points)
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
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::start(rid,  InputOperation::Read(rop))));
    res
}

proof fn readonly_read_version_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId) -> ( t2: AsynchronousSingleton::State<DT>)
    requires
        SimpleLog::State::readonly_read_version(s, s2, rid),
        state_refinement_relation(s, t, r_points),
        future_points_ok(s2, r_points)
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) // one.Next(Is, Is', AI.InternalOp)
{
    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    if r_points.contains_key(rid) && r_points[rid] == s.version {
        // assert(s.readonly_reqs[rid].is_Init());

        let op =  s.readonly_reqs[rid].get_Init_op();

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
        assert(AsynchronousSingleton::State::next_by(t, t, AsynchronousSingleton::Step::no_op())); // one.Next(Is, Is', AI.InternalOp);
        t
    }
}


proof fn readonly_finish_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId, version: LogIdx, ret: DT::Response) -> ( t2: AsynchronousSingleton::State<DT>)
    requires
        SimpleLog::State::readonly_finish(s, s2, rid, version, ret),
        state_refinement_relation(s, t, r_points.insert(rid, version)),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) // one.Next(Is, Is', AI.End(rid, return_value))
{
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
    assert(AsynchronousSingleton::State::end(t, res, rid, OutputOperation::Read(ret))); // fails
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::end(rid,  OutputOperation::Read(ret))));
    res
}

//--------------------------------------------------------------------------------------------------
// Update Transition Refinements
//--------------------------------------------------------------------------------------------------

proof fn update_start_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId, uop: DT::WriteOperation) -> ( t2: AsynchronousSingleton::State<DT>)
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

use crate::spec::simple_log::compute_nrstate_at_version;
proof fn state_at_version_preserves<DT: Dispatch>(a: Seq<DT::WriteOperation>, b: Seq<DT::WriteOperation>, x: DT::WriteOperation, i: LogIdx)
    requires b == a.push(x), i <= a.len(), i <= b.len()
    ensures compute_nrstate_at_version::<DT>(a, i) == compute_nrstate_at_version::<DT>(b, i)
    decreases i
{
    if i > 0 {
        state_at_version_preserves::<DT>(a, b, x, (i-1) as LogIdx);
    } else {
        assert(compute_nrstate_at_version::<DT>(a, i) == DT::init_spec());
        assert(compute_nrstate_at_version::<DT>(b, i) == DT::init_spec());
    }
}


proof fn update_add_update_to_log_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId) -> ( t2: AsynchronousSingleton::State<DT>)
    requires
        SimpleLog::State::update_add_op_to_log(s, s2, rid),
        state_refinement_relation(s, t, r_points),
    ensures
        state_refinement_relation(s2, t2, r_points),
        AsynchronousSingleton::State::next(t, t2) //  one.Next(Is, Is', AI.InternalOp)
{
    assert(s2.log == s.log.push(s.update_reqs[rid]));
    state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.version);

    assert forall |r| #[trigger] s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r)
        ==> readonly_response_is_valid(s2, t, r_points, r) by {
        if s2.readonly_reqs.contains_key(r) && #[trigger] t.resps.contains_key(r) {
            if r_points.contains_key(r) {
                assert(r_points[r] <= s.version);
                state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], r_points[r]);
            }
        }
    }

    assert forall |r| (#[trigger] s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version)
        ==> update_response_is_valid(s2, t, r_points, r) by {
        if s2.update_resps.contains_key(r) && s2.update_resps[r].0 < s2.version {
            state_at_version_preserves::<DT>(s.log, s2.log, s.update_reqs[rid], s.update_resps[r].0);
            assert(update_response_is_valid(s2, t, r_points, r));
        }
    }

    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> log_has_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            if v < s2.log.len() - 1 {
                assert(log_has_version(s.update_resps, v));
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
    assert(AsynchronousSingleton::State::next(t, t));
    t
}

proof fn update_finish_refines<DT: Dispatch>(s: SimpleLog::State<DT>, s2: SimpleLog::State<DT>, t: AsynchronousSingleton::State<DT>, r_points: Map<RequestId, LogIdx>, rid: RequestId, resp: DT::Response) -> ( t2: AsynchronousSingleton::State<DT>)
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
    assert forall |v: LogIdx| (s2.version <= v && v < s2.log.len()) ==> log_has_version(s2.update_resps, v) by {
        if s2.version <= v && v < s2.log.len() {
            assert(log_has_version(s.update_resps, v));
            let qid = choose|qid| #[trigger]s.update_resps.contains_key(qid) && s.update_resps[qid].0 == v;
            assert(s2.update_resps.contains_key(qid) && s2.update_resps[qid].0 == v);

        }
    }

    reveal(AsynchronousSingleton::State::next_by);
    reveal(AsynchronousSingleton::State::next);
    assert(AsynchronousSingleton::State::next_by(t, res, AsynchronousSingleton::Step::end(rid, OutputOperation::Write(resp))));
    assert(AsynchronousSingleton::State::next(t, res));
    res
}


proof fn update_incr_version_1_refines<DT: Dispatch>(b: AsynchronousSingletonBehavior<DT>, a: SimpleLogBehavior<DT>, a2: SimpleLogBehavior<DT>, r_points: Map<RequestId, LogIdx>) -> (b2: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(),
        future_points_ok(a2.get_last(), r_points),
        a.is_Stepped() && a2.is_Stepped(),
        a.get_Stepped_2() == a2.get_Stepped_2(),
        a.get_Stepped_1().is_Internal() && a2.get_Stepped_1().is_Internal(),
        a.get_last().version + 1 == a2.get_last().version,
        a.get_last().version + 1 <= a.get_last().log.len()
    ensures
        b2.wf(), behavior_equiv(a2, b2), state_refinement_relation(a2.get_last(), b2.get_last(), r_points)
{
    assume(false);
    arbitrary()
}

proof fn update_incr_version_refines<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<RequestId, LogIdx>, new_version: LogIdx) -> (b: AsynchronousSingletonBehavior<DT>)
    requires
        a.wf(), future_points_ok(a.get_last(), r_points), a.is_Stepped(), a.get_Stepped_1().is_Internal(),
        SimpleLog::State::update_incr_version(a.get_Stepped_2().get_last(), a.get_last(), new_version),
    ensures
        b.wf(), behavior_equiv(a, b), state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases
        *a.get_Stepped_2(), new_version
{
    assert(new_version >= a.get_Stepped_2().get_last().version);
    assert(new_version >= a.get_last().version);
    if new_version == a.get_Stepped_2().get_last().version {
        assert(a.get_last() == a.get_Stepped_2().get_last());
        // TODO: how to fix the recursion here?
        // exists_equiv_behavior_rec(*a.get_Stepped_2(), r_points)
        assume(false);
        arbitrary()
    } else {
        /* var amid := a.(s := a.s.(ctail := a.s.ctail - 1)); */
        let mut new_st = a.get_Stepped_0();
        new_st.version = (new_st.version - 1) as nat;
        /* do this */
        let amid = SimpleLogBehavior::Stepped(
            new_st,
            a.get_Stepped_1(),
            a.get_Stepped_2(),
        );

        reveal(SimpleLog::State::next);
        reveal(SimpleLog::State::next_by);
        // assert simple.NextStep(amid.tail.s, amid.s, AI.InternalOp, simple.IncreaseCtail_Step(new_ctail - 1));
        assert(SimpleLog::State::next_by(amid.get_Stepped_2().get_last(), amid.get_last(), SimpleLog::Step::update_incr_version((new_version - 1) as nat)));

        // var bmid := CtailRec(amid, r_points, new_ctail - 1);
        let bmid = update_incr_version_refines(amid, r_points, (new_version - 1) as LogIdx);

        update_incr_version_1_refines(bmid, amid, a, r_points)
    }
}

//--------------------------------------------------------------------------------------------------
// Refinement Theorem
//--------------------------------------------------------------------------------------------------

proof fn exists_equiv_behavior_rec<DT: Dispatch>(a: SimpleLogBehavior<DT>, r_points: Map<RequestId, LogIdx>)
    -> (b: AsynchronousSingletonBehavior<DT>)
    requires a.wf() && future_points_ok(a.get_last(), r_points)
    ensures  b.wf() && behavior_equiv(a, b) && state_refinement_relation(a.get_last(), b.get_last(), r_points)
    decreases a
{
    match a {
        SimpleLogBehavior::Stepped(post, aop, tail) => {
            // reveal the next transition
            reveal(SimpleLog::State::next);
            reveal(SimpleLog::State::next_by);
            reveal(AsynchronousSingleton::State::next);
            reveal(AsynchronousSingleton::State::next_by);

            let prev = tail.get_last();
            assert(exists |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(prev, post, step));
            let step = choose |step: SimpleLog::Step<DT>| SimpleLog::State::next_by(prev, post, step);
            match step {
                //                              ReqId, DT::ReadOperation
                SimpleLog::Step::readonly_start(rid, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.remove(rid));
                    let a0 = readonly_start_refines(prev, post, b0.get_last(), r_points, rid, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                //                              ReqId,
                SimpleLog::Step::readonly_read_version(rid) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = readonly_read_version_refines(prev, post, b0.get_last(), r_points, rid);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                //                              ReqId, LogIdx, DT::ReadOperation
                SimpleLog::Step::readonly_finish(rid, logidx, rop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points.insert(rid, logidx));
                    let a0 = readonly_finish_refines(prev, post, b0.get_last(), r_points, rid, logidx, rop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                //                            ReqId, DT::WriteOperation
                SimpleLog::Step::update_start(rid, uop) => {
                    let b0 = exists_equiv_behavior_rec(*tail, r_points);
                    let a0 = update_start_refines(prev, post, b0.get_last(), r_points, rid, uop);
                    AsynchronousSingletonBehavior::Stepped(a0, aop, Box::new(b0))
                }
                //                              ReqId,
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
                //                                        SimpleLog::State<DT>
                SimpleLog::Step::dummy_to_use_type_params(state) => {
                    // nothing to be done here.
                    assert(false);
                    arbitrary()
                }
            }
        }
        // Inited(SimpleLog::State<DT>),
        SimpleLogBehavior::Inited(sl_state) => {
            let st = AsynchronousSingleton::State {
                state: DT::init_spec(),
                reqs: Map::empty(),
                resps: Map::empty(),
            };
            let res =  AsynchronousSingletonBehavior::Inited(st);
            // yeah we need a bunch of reveals here... :(
            reveal(SimpleLog::State::init);
            reveal(SimpleLog::State::init_by);
            reveal(AsynchronousSingleton::State::init);
            reveal(AsynchronousSingleton::State::init_by);

            assert(AsynchronousSingleton::State::init_by(st, AsynchronousSingleton::Config::initialize()));
            res
        }
    }
}


struct Foo;
impl<DT: Dispatch> SimpleLogRefinesAsynchronousSingleton<DT> for Foo {
    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<DT>)
        // requires a.wf(),
        // ensures b.wf() && behavior_equiv(a, b)
        decreases a
    {
        return exists_equiv_behavior_rec(a, Map::empty())
    }
}


} // verus!
