// trustedness: ignore this file

// TODO fix?
// #![feature(register_tool)]
// #![register_tool(verifier)]

#[allow(unused_imports)]
use builtin::*;
use vstd::*;
use vstd::prelude::*;
use state_machines_macros::state_machine;

mod spec;
mod exec;
mod constants;

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

use crate::exec::replica::ReplicaId;
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

trait ThreadToken<DT: Dispatch, Replica> {
    spec fn wf(&self, replica: &Replica) -> bool;

    spec fn replica_id_spec(&self) -> nat;
}

trait NodeReplicated<DT: Dispatch + Sync>: Sized {
    type Replica; 
    type ReplicaId; 
    type TT: ThreadToken<DT, Self::Replica>;

    spec fn wf(&self) -> bool;

    spec fn replicas(&self) -> Vec<Box<Self::Replica>>;

    spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT>;

    // TODO this does not properly ensures initialization I think
    // I think it needs to return the correct initialization token
    fn new(num_replicas: usize) -> (res: Self)
        requires num_replicas == crate::constants::NUM_REPLICAS,
        ensures res.wf();

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

pub use crate::exec::NodeReplicated as NR;

spec fn implements_NodeReplicated<DT: Dispatch + Sync, N: NodeReplicated<DT>>() -> bool { true }

proof fn theorem_1<DT: Dispatch + Sync>()
    ensures implements_NodeReplicated::<DT, NR<DT>>(),
{ }

#[cfg(verus_keep_ghost)] use crate::spec::simple_log::SimpleLog;

pub open spec fn add_ticket<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    input: InputOperation<DT>,
    rid: RequestId) -> bool
{
    match input {
        InputOperation::Read(read_op) => {
            !pre.local_reads.dom().contains(rid)
            && post == UnboundedLog::State::<DT> {
                local_reads: pre.local_reads.insert(rid, crate::spec::unbounded_log::ReadonlyState::Init { op: read_op }),
                .. pre
            }
        }
        InputOperation::Write(write_op) => {
            !pre.local_updates.dom().contains(rid)
            && post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(rid, crate::spec::unbounded_log::UpdateState::Init { op: write_op }),
                .. pre
            }
        }
    }
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
            !pre.local_updates.dom().contains(rid)
            && pre.local_reads[rid].is_Done()
            && pre.local_reads[rid].get_Done_ret() == response
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
    proof fn finite_domains(post: UnboundedLog::State<DT>)
        requires post.invariant(),
        ensures post.local_reads.dom().finite(),
            post.local_updates.dom().finite();

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
}

spec fn implements_UnboundedLogRefinesSimpleLog<DT: Dispatch, RP: UnboundedLogRefinesSimpleLog<DT>>() -> bool { true }

proof fn theorem_2<DT: Dispatch + Sync>()
    ensures implements_UnboundedLogRefinesSimpleLog::<DT, crate::spec::unbounded_log_refines_simplelog::RefinementProof<DT>>(),
{ }

pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation),
    Write(DT::WriteOperation),
}

pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}

pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(RequestId, InputOperation<DT>),
    End(RequestId, InputOperation<DT>),
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

} // verus!
