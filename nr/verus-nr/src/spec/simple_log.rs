use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;

use vstd::prelude::*;

use crate::spec::types::*;
use crate::{AsyncLabel, Dispatch, InputOperation, OutputOperation};


////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Simple Log
// ==========
//
// The Simple Log is capturing requests to a data structure in an abstract and unbouned log
// represented as a mathematical sequence. In contrast to the node replication algorithm, the
// Simple Log does not store / wrap a data structure. Instead, it stores all update operations
// in the sequence. The state of the data structure is derived based on the version after N update
// operations have been applied. The version of the data structure is defined by the value of the
// completion tail (version) at the time the operation is dispatched.
//
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Simple Log State Machine
////////////////////////////////////////////////////////////////////////////////////////////////////

verus! {

/// Tracks the progress of a read-only query on the data structure.
///
/// Read requests enter the system and during the read the version of the data structure is
/// being read. That version defines the state the data structure is queried against.
///
/// Readonly operations are carried out in two steps:
///  1. When a 'ReadReq' request begins record the version of the log.
///  2. When it ends, we must return the answer at some version >= the recorded value.
///
pub ghost enum ReadReq<R> {
    /// a new read request that has entered the system
    Init { op: R },
    /// a request that has been dispatched at a specific version
    Req { version: LogIdx, op: R },
}

impl<R> ReadReq<R> {
    /// Extracts the operation from the ReadReq
    pub open spec fn op(self) -> R {
        match self {
            ReadReq::Init { op } => op,
            ReadReq::Req { op, ..} => op
        }
    }
}


/// Tracks the progress of an update query on the data structure.
///
/// Update requests are placed into the log. The
pub ghost struct UpdateResp(pub LogIdx);


state_machine! {
    SimpleLog<DT: Dispatch> {
    fields {
        /// a sequence of update operations,
        pub log: Seq<DT::WriteOperation>,
        /// the completion tail current index into the log
        pub version: LogIdx,
        /// in flight read requests
        pub readonly_reqs: Map<ReqId, ReadReq<DT::ReadOperation>>,
        /// inflight update requests
        pub update_reqs: Map<ReqId, DT::WriteOperation>,
        /// responses to update requests that haven't been returned
        pub update_resps: Map<ReqId, UpdateResp>,
    }

    /// Label for the requests
    pub type Label<DT> = AsyncLabel<DT>;

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// the version of the log must be less than the length of the log
    #[invariant]
    pub fn inv_version(&self) -> bool {
        0 <= self.version <= self.log.len()
    }

    /// all update responses must have version that are less than the length of the log
    #[invariant]
    pub fn inv_update_resp_version(&self) -> bool {
        forall |rid: ReqId| #[trigger] self.update_resps.contains_key(rid)
            ==> self.update_resps[rid].0 < self.log.len()
    }

    /// all readonly requests must have a version that is less or equal to the log version
    #[invariant]
    pub fn inv_readonly_req_version(&self) -> bool {
        forall |rid: ReqId| #[trigger] self.readonly_reqs.contains_key(rid) && self.readonly_reqs[rid] is Req
            ==> self.readonly_reqs[rid]->version <= self.version
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // State Machine Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////


    init!{
        initialize() {
            init log = Seq::empty();
            init version = 0;
            init readonly_reqs = Map::empty();
            init update_reqs = Map::empty();
            init update_resps = Map::empty();
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Constructing the DataStructureSpec
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// constructs the state of the data structure at a specific version given the log
    ///
    /// This function recursively applies the update operations to the initial state of the
    /// data structure and returns the state of the data structure at the given  version.
    pub open spec fn nrstate_at_version(&self, version: LogIdx) -> DT::View
        recommends 0 <= version <= self.log.len()
    {
        compute_nrstate_at_version::<DT>(self.log, version)
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Read Operation Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// Read Request: Enter the read request operation into the system
    ///
    /// The supplied request id must not yet be know to the system
    transition!{
        readonly_start(label: Label<DT>, rid: ReqId, op: DT::ReadOperation) {
            require label == AsyncLabel::<DT>::Start(rid, InputOperation::Read(op));

            require !pre.readonly_reqs.contains_key(rid);
            require !pre.update_reqs.contains_key(rid);
            require !pre.update_resps.contains_key(rid);

            update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Init{ op };
        }
    }

    /// Read Request: Read the current version of the log
    ///
    /// This records the current version of the log the read-only request was submitted
    transition!{
        readonly_read_version(label: Label<DT>, rid: ReqId) {
            require label.is_Internal();

            require pre.readonly_reqs.contains_key(rid);
            require let ReadReq::<DT::ReadOperation>::Init { op } = pre.readonly_reqs[rid];

            update readonly_reqs[rid] = ReadReq::<DT::ReadOperation>::Req { op, version: pre.version };
        }
    }

    /// Read Request: Remove the request from the system
    ///
    /// The actual version at which the read request was executed may be newer than when the
    /// read request entered the system. Thus, the supplied version must be larger or equal to
    /// the version that was read before, and less or equal to the current current length of the log.
    transition!{
        readonly_finish(label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) {
            require label == AsyncLabel::<DT>::End(rid, OutputOperation::Read(ret));

            require pre.readonly_reqs.contains_key(rid);
            require let ReadReq::<DT::ReadOperation>::Req { op, version: current } = pre.readonly_reqs[rid];

            require current <= version <= pre.log.len();
            require version <= pre.version;
            require ret == DT::dispatch_spec(pre.nrstate_at_version(version), op);

            update readonly_reqs = pre.readonly_reqs.remove(rid);
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Update Operation Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////////


    // Update operation happen in four steps:
    //  1. add the update to the local update requests
    //  2. collect the updates and store them in the log
    //  3. increase the version of the log
    //  4. return the version of the log at the update


    /// Update Request: place an update request in the system
    ///
    /// The request id here must not be in the system yet.
    transition!{
        update_start(label: Label<DT>, rid: ReqId, op: DT::WriteOperation) {
            require label == AsyncLabel::<DT>::Start(rid, InputOperation::Write(op));

            require !pre.readonly_reqs.contains_key(rid);
            require !pre.update_reqs.contains_key(rid);
            require !pre.update_resps.contains_key(rid);

            update update_reqs[rid] = op;
        }
    }

    /// Update Request: Add the update operations to the log
    ///
    /// Place the update with the given request id into the log and record its version.
    /// The update moves from the requests to the responses and the log grows by one element.
    transition!{
        update_add_op_to_log(label: Label<DT>, rid: ReqId) {
            require label.is_Internal();

            require pre.update_reqs.contains_key(rid);

            update log = pre.log.push(pre.update_reqs[rid]);
            update update_reqs = pre.update_reqs.remove(rid);
            update update_resps = pre.update_resps.insert(rid, UpdateResp(pre.log.len()));
        }
    }

    /// Update: Increasing the version of the log
    ///
    /// The version value is monotonically increasing and must not be larger than the
    /// length of the log.
    transition!{
        update_incr_version(label: Label<DT>, new_version: LogIdx) {
            require label.is_Internal();

            require pre.version <= new_version <= pre.log.len();

            update version = new_version;
        }
    }

    /// Update: Finish the update operation
    ///
    /// This removes the update response from the update responses. The supplied return value
    /// must match the value when we apply the update to the data structure at the give version.
    transition!{
        update_finish(label: Label<DT>, rid: nat, ret: DT::Response) {
            require label == AsyncLabel::<DT>::End(rid, OutputOperation::Write(ret));

            require pre.update_resps.contains_key(rid);
            let uidx = pre.update_resps[rid].0;

            require uidx < pre.version <= pre.log.len();
            require ret == DT::dispatch_mut_spec(pre.nrstate_at_version(uidx), pre.log[uidx as int]).1;

            update update_resps = pre.update_resps.remove(rid);
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Stutter Step
    ////////////////////////////////////////////////////////////////////////////////////////////////


    /// No-Op transition
    transition!{
        no_op(label: Label<DT>, ) {
            require label.is_Internal();
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Inductiveness Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////////


    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(readonly_start)]
    fn readonly_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::ReadOperation) { }

    #[inductive(readonly_read_version)]
    fn readonly_read_version_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

    #[inductive(readonly_finish)]
    fn readonly_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, version: LogIdx, ret: DT::Response) { }

    #[inductive(update_start)]
    fn update_start_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId, op: DT::WriteOperation) { }

    #[inductive(update_add_op_to_log)]
    fn update_add_op_to_log_inductive(pre: Self, post: Self, label: Label<DT>, rid: ReqId) { }

    #[inductive(update_incr_version)]
    fn update_incr_version_inductive(pre: Self, post: Self, label: Label<DT>, new_version: LogIdx) { }

    #[inductive(update_finish)]
    fn update_finish_inductive(pre: Self, post: Self, label: Label<DT>, rid: nat,  ret: DT::Response) { }

    #[inductive(no_op)]
    fn no_op_inductive(pre: Self, post: Self, label: Label<DT>) { }

}} // state_machine! SimpleLog


/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given version. The
/// version must be within the log's range.
pub open spec fn compute_nrstate_at_version<DT: Dispatch>(log: Seq<DT::WriteOperation>, version: LogIdx) -> DT::View
    recommends 0 <= version <= log.len()
    decreases version
{
    if version == 0 {
        DT::init_spec()
    } else {
        DT::dispatch_mut_spec(compute_nrstate_at_version::<DT>(log, (version - 1) as nat), log[version - 1]).0
    }
}

} // verus!
