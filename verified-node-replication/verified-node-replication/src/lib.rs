// Verified Node Replication Library
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # Verified Node Replication Library
//!
//! This library is a verified version of the [node-replicatin library](https://github.com/vmware/node-replication/)
//! that allows for the construction of replicated, concurrent data structures.
//!
//! This top-level module contains the trusted traits and the top-level lemmas.
#[allow(unused_imports)]
use builtin::*;
//use state_machines_macros::state_machine;
use vstd::prelude::*;

pub mod constants;
mod exec;
mod spec;
mod extra;

mod counter;

use crate::spec::simple_log::SimpleLog;
use crate::spec::unbounded_log::UnboundedLog;

pub use crate::exec::context::ThreadToken;
pub use crate::exec::NodeReplicated;

use crate::constants::MAX_REPLICAS;

verus! {

// tell the verifier that the size of usize is 8.
global size_of usize == 8;

////////////////////////////////////////////////////////////////////////////////////////////////////
// GLobal Types
////////////////////////////////////////////////////////////////////////////////////////////////////
/// the type of a replica identifier
pub type ReplicaId = usize;

// $line_count$Trusted$
/// the identifier of a node / replica
pub type NodeId = nat;

// $line_count$Trusted$
/// the index into the log
pub type LogIdx = nat;

// $line_count$Trusted$
/// the identifier of a update or read request
pub type ReqId = nat;

// $line_count$Trusted$
/// the identifier of a thread on a given replica
pub type ThreadId = nat;

// $line_count$Trusted$
////////////////////////////////////////////////////////////////////////////////////////////////////
// Top-level Theorem
////////////////////////////////////////////////////////////////////////////////////////////////////
// the following theorems establish the correctness of the execution adhering to the specification.
// See the corresponding refinement proofs etc.
// We leverage traits that establish the required pre- and post-conditions (trusted), then we use
// the trait constraints to show that the actual types implement the trait correctly.
///// Theorem 1: The SimpleLog atomic state machine refines the trusted specification of the data
/////            structure expressed as an asynchronous singleton.
/////
///// This theorem shows the linearizability of the SimpleLog atomic state machine.
//#[verus::trusted]
//proof fn theorem_1<DT: Dispatch + Sync>()
//    ensures
//        implements_SimpleLogRefinesAsynchronousSingleton::<
//            DT,
//            crate::spec::linearization::RefinementProof,
//        >(),
//{
//}

/// Theorem 2: The UnboundedLog Global State Machine refines the SimpleLog atomic state machine.
///
/// This shows that the replicas are evolving correctly with respect to the SimpleLog atomic state machine.
#[verus::trusted]
proof fn theorem_2<DT: Dispatch + Sync>()
    ensures
        implements_UnboundedLogRefinesSimpleLog::<
            DT,
            crate::spec::unbounded_log_refines_simplelog::RefinementProof<DT>,
        >(),
{
}

/// Theorem 3: The Node Replication implementation refines the Unbounded Log and establishes
///            local/global transition system relationship.
#[verus::trusted]
proof fn theorem_3<DT: Dispatch + Sync>()
    ensures
        implements_NodeReplicated::<DT, NodeReplicated<DT>>(),
{
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Thread Token
////////////////////////////////////////////////////////////////////////////////////////////////////
/// Trusted interface of a thread token used in the proofs.
///
/// TODO: change this to pub(trait)
#[verus::trusted]
pub trait ThreadTokenT<DT: Dispatch, Replica> {
    /// returns true if the thread token is well-formed
    spec fn wf(&self, replica: &Replica) -> bool;

    /// obtains the replica identifier this thread is registered with
    spec fn replica_id_spec(&self) -> nat;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Dispatch Trait
////////////////////////////////////////////////////////////////////////////////////////////////////
/// The dispatch trait defines the update/readonly operations applied to the replicate data structure
/// and the return types. For a data structure to be used with the node-replication library, it must
/// implement this trait.
///
/// Read-only Operations: These operations do not modify the state of the data structure.
/// The node-replication library will execute [`Dispatch::dispatch`] method on the data structure
/// with the provided `ReadOperation` argument and return a `Response` value.
///
/// Write Operations: These operations modify the state of the data structure. The node-replication
/// library will execute [`Dispatch::dispatch_mut`] method on the data structure with the provided
/// `WriteOperation` argument and return a `Response` value.
///
/// The dispatch trait interface is trusted by the verifier as it is the high-level interface that
/// the data structure is verified against.
///
#[verus::trusted]
pub trait Dispatch: Sized {
    /// Type of a read-only operation. Operations of this type do not mutate the data structure.
    type ReadOperation: Sized;

    /// Type of a write operation. Operations of this type may mutate the data structure.
    /// Write operations are sent between replicas.
    type WriteOperation: Sized + Send;

    /// Type of the response of either a read or write operation.
    type Response: Sized;

    /// Type of the view of the data structure for specs and proofs.
    type View;

    /// Constructs the view of the data structure.
    ///
    /// This lifts the concrete, executable representation of the data structure into a
    /// view that can be reasoned about in specs and proofs.
    /// This provides support for the `@` operator on the data structure
    spec fn view(&self) -> Self::View;

    /// Initializes the data structure.
    fn init() -> (res: Self)
        ensures
            res@ == Self::init_spec(),
            res.inv(),
    ;

    /// Clones a write operation to be copied to and read from the shared log.
    fn clone_write_op(op: &Self::WriteOperation) -> (res: Self::WriteOperation)
        ensures
            op == res,
    ;

    /// Clones a response value such that it can be returned to the waiting thread
    fn clone_response(op: &Self::Response) -> (res: Self::Response)
        ensures
            op == res,
    ;

    /// Executes a read-only operation against the data structure and returns the result.
    fn dispatch(&self, op: Self::ReadOperation) -> (result: Self::Response)
        requires
            self.inv(),
        ensures
            Self::dispatch_spec(self@, op) == result,
    ;

    /// Executes a write operation against the data structure and returns the result.
    fn dispatch_mut(&mut self, op: Self::WriteOperation) -> (result: Self::Response)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            Self::dispatch_mut_spec(old(self)@, op) == (self@, result),
    ;

    /// specification of the [`Dispatch::init`] function.
    spec fn init_spec() -> Self::View;

    /// specification of the [`Dispatch::dispatch`] function.
    spec fn dispatch_spec(ds: Self::View, op: Self::ReadOperation) -> Self::Response;

    /// specification of the [`Dispatch::dispatch_mut`] function.
    spec fn dispatch_mut_spec(ds: Self::View, op: Self::WriteOperation) -> (
        Self::View,
        Self::Response,
    );

    /// An invariant that is preserved by [`Dispatch::dispatch_mut`]
    spec fn inv(&self) -> bool;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Node Replicated Trait
////////////////////////////////////////////////////////////////////////////////////////////////////
/// Affinity Function
///
/// This structure is a wrapper around a function that changes the memory affinity
/// when allocating/initializing replicas during the initialization of the data structure.
///
#[verifier(external_body)]  /* vattr */
#[verus::trusted]
pub struct AffinityFn {
    f: Box<dyn Fn(ReplicaId)>,
}

#[verus::trusted]
impl AffinityFn {
    /// creates a new AffinityFn object that points to the given affinity function.
    #[verifier(external_body)]  /* vattr */
    pub fn new(f: impl Fn(ReplicaId) + 'static) -> Self {
        Self { f: Box::new(f) }
    }

    /// calls the affinity function with the given replica id.
    #[verifier(external_body)]  /* vattr */
    pub fn call(&self, rid: ReplicaId) {
        (self.f)(rid)
    }
}

/// Node Replicated Trait
///
/// This is the top-level interface that users will interact with.
///
#[verus::trusted]
pub trait NodeReplicatedT<DT: Dispatch + Sync>: Sized {
    /// The type of a replica
    type Replica;

    /// The type of the replica id
    type ReplicaId;

    /// the type of the thread token
    type TT: ThreadTokenT<DT, Self::Replica>;

    /// defines the well-formedness condition on the replicated data structure
    spec fn wf(&self) -> bool;

    /// obtains a vector of replicas
    spec fn replicas(&self) -> Vec<Box<Self::Replica>>;

    /// obtainst the instance to the unbounded log
    spec fn unbounded_log_instance(&self) -> UnboundedLog::Instance<DT>;

    /// creates a new instance of the replicated data structure with the given number of replicas.
    ///
    /// The number of replicas must be at least 1 and not exceed the pre-defined maximum.
    /// It ensures that the data structure is well-formed and has the correct number of replicas.
    fn new(num_replicas: usize, chg_mem_affinity: AffinityFn) -> (res: Self)
        requires
            0 < num_replicas && num_replicas <= MAX_REPLICAS,
        ensures
            res.wf() && res.replicas().len() == num_replicas,
    ;

    /// registers a thread with the given replica id.
    fn register(&mut self, replica_id: ReplicaId) -> (result: Option<Self::TT>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            result.is_Some() ==> result.get_Some_0().wf(&self.replicas()[replica_id as int]),
    ;

    /// executes an update operation against the data structure.
    fn execute_mut(
        &self,
        op: DT::WriteOperation,
        tkn: Self::TT,
        ticket: Tracked<UnboundedLog::local_updates<DT>>,
    ) -> (result: Result<
        (DT::Response, Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
        (Self::TT, Tracked<UnboundedLog::local_updates<DT>>),
    >)
        requires
            self.wf(),  // wf global node
            tkn.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            is_update_ticket(ticket@, op, self.unbounded_log_instance()),
        ensures
            result.is_Ok() ==> is_update_stub(
                result.get_Ok_0().2@,
                ticket@@.key,
                result.get_Ok_0().0,
                self.unbounded_log_instance(),
            ) && result.get_Ok_0().1.wf(&self.replicas().spec_index(tkn.replica_id_spec() as int)),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn,
    ;

    /// executes a read-only operation against the data structure.
    fn execute(
        &self,
        op: DT::ReadOperation,
        tkn: Self::TT,
        ticket: Tracked<UnboundedLog::local_reads<DT>>,
    ) -> (result: Result<
        (DT::Response, Self::TT, Tracked<UnboundedLog::local_reads<DT>>),
        (Self::TT, Tracked<UnboundedLog::local_reads<DT>>),
    >)
        requires
            self.wf(),  // wf global node
            tkn.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            is_readonly_ticket(ticket@, op, tkn.replica_id_spec(), self.unbounded_log_instance()),
        ensures
            result.is_Ok() ==> is_readonly_stub(
                result.get_Ok_0().2@,
                ticket@@.key,
                result.get_Ok_0().0,
                self.unbounded_log_instance(),
            ) && result.get_Ok_0().1.wf(&self.replicas()[tkn.replica_id_spec() as int]),
            result.is_Err() ==> result.get_Err_0().1 == ticket && result.get_Err_0().0 == tkn,
    ;
}

/// Spec function that checks whether the struct implements the trait properly.
#[verus::trusted]
spec fn implements_NodeReplicated<DT: Dispatch + Sync, N: NodeReplicatedT<DT>>() -> bool {
    true
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Proof Functions for Node Replicated -> Unbounded Log Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////
#[verus::trusted]
pub open spec fn is_readonly_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_reads<DT>,
    op: DT::ReadOperation,
    node_id: NodeId,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value is Init
    &&& ticket@.value.get_Init_op() == op
    &&& ticket@.value.get_Init_node_id() == node_id

    // requires ticket.loc == TicketStubSingletonLoc.loc()

    &&& ticket@.instance == log
}

#[verus::trusted]
pub open spec fn is_readonly_stub<DT: Dispatch>(
    stub: UnboundedLog::local_reads<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists ctail, op, nodeid :: stub == ReadOp(rid, ReadonlyDone(op, output, nodeid, ctail)))

    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}

#[verus::trusted]
pub open spec fn is_update_ticket<DT: Dispatch>(
    ticket: UnboundedLog::local_updates<DT>,
    op: DT::WriteOperation,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    // requires ticket.val == ssm.Ticket(rid, input)
    &&& ticket@.value.is_Init() && ticket@.value.get_Init_op()
        == op
    // requires ticket.loc == TicketStubSingletonLoc.loc()

    &&& ticket@.instance == log
}

#[verus::trusted]
pub open spec fn is_update_stub<DT: Dispatch>(
    stub: UnboundedLog::local_updates<DT>,
    rid: ReqId,
    result: DT::Response,
    log: UnboundedLog::Instance<DT>,
) -> bool {
    // ensures stub.loc == TicketStubSingletonLoc.loc()
    &&& stub@.instance
        == log
    // ensures ssm.IsStub(rid, output, stub.val)  -> (exists log_idx :: stub == UpdateOp(rid, UpdateDone(output, log_idx)))

    &&& stub@.key == rid
    &&& stub@.value.is_Done()
    &&& stub@.value.get_Done_ret() == result
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// UnboundedLog -> SimpleLog Refinement Proof
////////////////////////////////////////////////////////////////////////////////////////////////////
#[verus::trusted]
pub open spec fn add_ticket<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    input: InputOperation<DT>,
    rid: ReqId,
) -> bool {
    !pre.local_reads.dom().contains(rid) && !pre.local_updates.dom().contains(rid) && (match input {
        InputOperation::Read(read_op, node_id) => {
            &&post == UnboundedLog::State::<DT> {
                local_reads: pre.local_reads.insert(
                    rid,
                    crate::spec::unbounded_log::ReadonlyState::Init { op: read_op, node_id },
                ),
                ..pre
            }
        },
        InputOperation::Write(write_op) => {
            &&post == UnboundedLog::State::<DT> {
                local_updates: pre.local_updates.insert(
                    rid,
                    crate::spec::unbounded_log::UpdateState::Init { op: write_op },
                ),
                ..pre
            }
        },
    })
}

#[verus::trusted]
pub open spec fn consume_stub<DT: Dispatch>(
    pre: UnboundedLog::State<DT>,
    post: UnboundedLog::State<DT>,
    output: OutputOperation<DT>,
    rid: ReqId,
) -> bool {
    match output {
        OutputOperation::Read(response) => {
            pre.local_reads.dom().contains(rid) && pre.local_reads[rid].is_Done()
                && pre.local_reads[rid].get_Done_ret() == response && post == UnboundedLog::State::<
                DT,
            > { local_reads: pre.local_reads.remove(rid), ..pre }
        },
        OutputOperation::Write(response) => {
            pre.local_updates.dom().contains(rid) && pre.local_updates[rid].is_Done()
                && pre.local_updates[rid].get_Done_ret() == response && post
                == UnboundedLog::State::<DT> { local_updates: pre.local_updates.remove(rid), ..pre }
        },
    }
}

#[verus::trusted]
trait UnboundedLogRefinesSimpleLog<DT: Dispatch> {
    spec fn interp(s: UnboundedLog::State<DT>) -> SimpleLog::State<DT>;

    // Prove that it is always possible to add a new ticket
    spec fn get_fresh_rid(pre: UnboundedLog::State<DT>) -> ReqId;

    proof fn fresh_rid_is_ok(pre: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
        ensures
            !pre.local_reads.dom().contains(Self::get_fresh_rid(pre)),
            !pre.local_updates.dom().contains(Self::get_fresh_rid(pre)),
    ;

    proof fn refinement_inv(vars: UnboundedLog::State<DT>)
        requires
            vars.invariant(),
        ensures
            Self::interp(vars).invariant(),
    ;

    proof fn refinement_init(post: UnboundedLog::State<DT>)
        requires
            post.invariant(),
            UnboundedLog::State::init(post),
        ensures
            SimpleLog::State::init(Self::interp(post)),
    ;

    proof fn refinement_next(pre: UnboundedLog::State<DT>, post: UnboundedLog::State<DT>)
        requires
            pre.invariant(),
            post.invariant(),
            UnboundedLog::State::next_strong(pre, post),
        ensures
            SimpleLog::State::next(Self::interp(pre), Self::interp(post), AsyncLabel::Internal),
    ;

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
            SimpleLog::State::next(
                Self::interp(pre),
                Self::interp(post),
                AsyncLabel::Start(Self::get_fresh_rid(pre), input),
            ),
    ;

    proof fn refinement_consume_stub(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: OutputOperation<DT>,
        rid: ReqId,
    )
        requires
            pre.invariant(),
            consume_stub(pre, post, output, rid),
        ensures
            post.invariant(),
            SimpleLog::State::next(
                Self::interp(pre),
                Self::interp(post),
                AsyncLabel::End(rid, output),
            ),
    ;
}

#[verus::trusted]
spec fn implements_UnboundedLogRefinesSimpleLog<
    DT: Dispatch,
    RP: UnboundedLogRefinesSimpleLog<DT>,
>() -> bool {
    true
}

////////////////////////////////////////////////////////////////////////////////////////////////////
/// SimpleLog -> Linearization Refinement
////////////////////////////////////////////////////////////////////////////////////////////////////
#[is_variant]
#[verus::trusted]
pub enum InputOperation<DT: Dispatch> {
    Read(DT::ReadOperation, NodeId),
    Write(DT::WriteOperation),
}

#[is_variant]
#[verus::trusted]
pub enum OutputOperation<DT: Dispatch> {
    Read(DT::Response),
    Write(DT::Response),
}

#[is_variant]
#[verus::trusted]
pub enum AsyncLabel<DT: Dispatch> {
    Internal,
    Start(ReqId, InputOperation<DT>),
    End(ReqId, OutputOperation<DT>),
}

//state_machine!{ AsynchronousSingleton<DT: Dispatch> {           // $line_count$Trusted$
//    fields {                                                    // $line_count$Trusted$
//        pub state: DT::View,                                    // $line_count$Trusted$
//        pub reqs: Map<ReqId, InputOperation<DT>>,               // $line_count$Trusted$
//        pub resps: Map<ReqId, OutputOperation<DT>>,             // $line_count$Trusted$
//    }                                                           // $line_count$Trusted$
//
//    pub type Label<DT> = AsyncLabel<DT>;                        // $line_count$Trusted$
//
//    init!{                                                      // $line_count$Trusted$
//        initialize() {                                          // $line_count$Trusted$
//            init state = DT::init_spec();                       // $line_count$Trusted$
//            init reqs = Map::empty();                           // $line_count$Trusted$
//            init resps = Map::empty();                          // $line_count$Trusted$
//        }                                                       // $line_count$Trusted$
//    }                                                           // $line_count$Trusted$
//
//    transition!{                                                // $line_count$Trusted$
//        internal_next(label: Label<DT>, rid: ReqId, input: InputOperation<DT>, output: OutputOperation<DT>) {   // $line_count$Trusted$
//            require label.is_Internal();                     // $line_count$Trusted$
//            require pre.reqs.dom().contains(rid);            // $line_count$Trusted$
//            require pre.reqs[rid] == input;                  // $line_count$Trusted$
//            update reqs = pre.reqs.remove(rid);              // $line_count$Trusted$
//            update resps = pre.resps.insert(rid, output);    // $line_count$Trusted$
//
//            match input {                                    // $line_count$Trusted$
//                InputOperation::Read(read_op) => {           // $line_count$Trusted$
//                    require output === OutputOperation::Read(DT::dispatch_spec(pre.state, read_op));  // $line_count$Trusted$
//                }                                                                           // $line_count$Trusted$
//                InputOperation::Write(write_op) => {                                        // $line_count$Trusted$
//                    let (next_state, out) = DT::dispatch_mut_spec(pre.state, write_op);     // $line_count$Trusted$
//                    require output === OutputOperation::Write(out);                         // $line_count$Trusted$
//                    update state = next_state;                                              // $line_count$Trusted$
//                }                                                                           // $line_count$Trusted$
//            }                                                                               // $line_count$Trusted$
//        }                                                                                   // $line_count$Trusted$
//    }                                                                                       // $line_count$Trusted$
//
//    transition!{                                        // $line_count$Trusted$
//        no_op(label: Label<DT>) {                       // $line_count$Trusted$
//            require label.is_Internal();                // $line_count$Trusted$
//            /* stutter step */                          // $line_count$Trusted$
//        }                                               // $line_count$Trusted$
//    }                                                   // $line_count$Trusted$
//
//    transition!{                                                            // $line_count$Trusted$
//        start(label: Label<DT>, rid: ReqId, input: InputOperation<DT>) {    // $line_count$Trusted$
//            require label == AsyncLabel::<DT>::Start(rid, input);           // $line_count$Trusted$
//            require !pre.reqs.dom().contains(rid);                          // $line_count$Trusted$
//            update reqs = pre.reqs.insert(rid, input);                      // $line_count$Trusted$
//        }                                                                   // $line_count$Trusted$
//    }                                                                       // $line_count$Trusted$
//
//    transition!{                                                            // $line_count$Trusted$
//        end(label: Label<DT>, rid: ReqId, output: OutputOperation<DT>) {    // $line_count$Trusted$
//            require label == AsyncLabel::<DT>::End(rid, output);            // $line_count$Trusted$
//            require pre.resps.dom().contains(rid);                          // $line_count$Trusted$
//            require pre.resps[rid] == output;                               // $line_count$Trusted$
//            update resps = pre.resps.remove(rid);                           // $line_count$Trusted$
//        }                                                                   // $line_count$Trusted$
//    }                                                                       // $line_count$Trusted$
//}}  // $line_count$Trusted$
//
//
//#[is_variant]
//#[verus::trusted]
//pub enum SimpleLogBehavior<DT: Dispatch> {
//    Stepped(SimpleLog::State<DT>, AsyncLabel<DT>, Box<SimpleLogBehavior<DT>>),
//    Inited(SimpleLog::State<DT>),
//}
//
//#[verus::trusted]
//impl<DT: Dispatch> SimpleLogBehavior<DT> {
//    pub open spec fn get_last(self) -> SimpleLog::State<DT> {
//        match self {
//            SimpleLogBehavior::Stepped(post, op, tail) => post,
//            SimpleLogBehavior::Inited(post) => post,
//        }
//    }
//
//    pub open spec fn wf(self) -> bool
//        decreases self,
//    {
//        match self {
//            SimpleLogBehavior::Stepped(post, op, tail) => {
//                tail.wf() && SimpleLog::State::next(tail.get_last(), post, op)
//            },
//            SimpleLogBehavior::Inited(post) => { SimpleLog::State::init(post) },
//        }
//    }
//}
//
//#[is_variant]
//#[verus::trusted]
//pub enum AsynchronousSingletonBehavior<DT: Dispatch> {
//    Stepped(
//        AsynchronousSingleton::State<DT>,
//        AsyncLabel<DT>,
//        Box<AsynchronousSingletonBehavior<DT>>,
//    ),
//    Inited(AsynchronousSingleton::State<DT>),
//}
//
//#[verus::trusted]
//impl<DT: Dispatch> AsynchronousSingletonBehavior<DT> {
//    pub open spec fn get_last(self) -> AsynchronousSingleton::State<DT> {
//        match self {
//            AsynchronousSingletonBehavior::Stepped(post, op, tail) => post,
//            AsynchronousSingletonBehavior::Inited(post) => post,
//        }
//    }
//
//    pub open spec fn wf(self) -> bool
//        decreases self,
//    {
//        match self {
//            AsynchronousSingletonBehavior::Stepped(post, op, tail) => {
//                tail.wf() && AsynchronousSingleton::State::next(tail.get_last(), post, op)
//            },
//            AsynchronousSingletonBehavior::Inited(post) => {
//                AsynchronousSingleton::State::init(post)
//            },
//        }
//    }
//}
//
//#[verus::trusted]
//pub open spec fn behavior_equiv<DT: Dispatch>(
//    a: SimpleLogBehavior<DT>,
//    b: AsynchronousSingletonBehavior<DT>,
//) -> bool
//    decreases a, b,
//{
//    // (a.Inited? && b.Inited?)
//    ||| (a.is_Inited()
//        && b.is_Inited())
//    // || (a.Stepped? && a.op.InternalOp? && equiv(a.tail, b))
//
//    ||| (a.is_Stepped() && a.get_Stepped_1().is_Internal() && behavior_equiv(
//        *a.get_Stepped_2(),
//        b,
//    ))
//    // || (b.Stepped? && b.op.InternalOp? && equiv(a, b.tail))
//
//    ||| (b.is_Stepped() && b.get_Stepped_1().is_Internal() && behavior_equiv(
//        a,
//        *b.get_Stepped_2(),
//    ))
//    // || (a.Stepped? && b.Stepped? && a.op == b.op && equiv(a.tail, b.tail))
//
//    ||| (a.is_Stepped() && b.is_Stepped() && a.get_Stepped_1() == b.get_Stepped_1()
//        && behavior_equiv(*a.get_Stepped_2(), *b.get_Stepped_2()))
//}
//
//#[verus::trusted]
//trait SimpleLogRefinesAsynchronousSingleton<DT: Dispatch> {
//    proof fn exists_equiv_behavior(a: SimpleLogBehavior<DT>) -> (b: AsynchronousSingletonBehavior<
//        DT,
//    >)
//        requires
//            a.wf(),
//        ensures
//            b.wf() && behavior_equiv(a, b),
//    ;
//}
//
//#[verus::trusted]
//spec fn implements_SimpleLogRefinesAsynchronousSingleton<
//    DT: Dispatch,
//    RP: SimpleLogRefinesAsynchronousSingleton<DT>,
//>() -> bool {
//    true
//}

} // verus!
