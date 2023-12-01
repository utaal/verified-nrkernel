// trustedness: ignore this file

// TODO fix?
// #![feature(register_tool)]
// #![register_tool(verifier)]

#[allow(unused_imports)]
use builtin::*;
use vstd::*;
// use vstd::seq::*;
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
    rid: ReqId) -> bool
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
    rid: ReqId) -> bool
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
    spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId;

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
        rid: ReqId
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
    Start(ReqId, InputOperation<DT>),
    End(ReqId, OutputOperation<DT>),
}

state_machine!{ AsynchronousSingleton<DT: Dispatch> {
    fields {
        pub state: DT::View,
        pub reqs: Map<ReqId, InputOperation<DT>>,
        pub resps: Map<ReqId, OutputOperation<DT>>,
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
        internal_next(rid: ReqId, input: InputOperation<DT>, output: OutputOperation<DT>) {
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
        start(rid: ReqId, input: InputOperation<DT>) {
            require !pre.reqs.dom().contains(rid);
            update reqs = pre.reqs.insert(rid, input);
        }
    }

    transition!{
        end(rid: ReqId, output: OutputOperation<DT>) {
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
    ||| (a.is_Stepped() && b.is_Stepped() && a.get_Stepped_1() == b.get_Stepped_1() && behavior_equiv(*a.get_Stepped_2(), *b.get_Stepped_2()))


    // (a.is_Inited() && b.is_Inited())
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

spec fn implements_SimpleLogRefinesAsynchronousSingleton<DT: Dispatch, RP: SimpleLogRefinesAsynchronousSingleton<DT>>() -> bool { true }

proof fn theorem_3<DT: Dispatch + Sync>()
    ensures implements_SimpleLogRefinesAsynchronousSingleton::<DT, crate::spec::linearization::RefinementProof>(),
{ }


} // verus!
