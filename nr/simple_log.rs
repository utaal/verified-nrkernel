#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;

// use pervasive::*;
use super::pervasive::map::*;
use super::pervasive::seq::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::set::*;

use super::types::*;
#[allow(unused_imports)] // XXX: should not be needed!
use super::utils::*;

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Simple Log
// ==========
//
// The Simple Log is capturing requests to a data structure in an abstract and unbouned log
// represented as a mathematical sequence. In contrast to the node replication algorithm, the
// Simple Log does not store / wrap a data structure. Instead, it stores all update operations
// in the sequence. The state of the data structure is derived based on the version after N update
// operations have been applied. The version of the data structure is defined by the value of teh
// completion tail (ctail) at the time the operation is dispatched.
//
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Simple Log State Machine
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents the state of a read-request
#[is_variant]
pub enum ReadReq {
    /// a new read request that has entered the system
    Init { op: ReadonlyOp },
    /// a request that has been dispatched at a specific version
    Req { version: LogIdx, op: ReadonlyOp },
}

/// Represents the state of an update requeset, returning the index of the update in the log
pub struct UpdateResp(pub LogIdx);

state_machine! {
    SimpleLog {
        fields {
            /// a sequence of update operations,
            pub log: Seq<UpdateOp>,
            /// the completion tail current index into the log
            pub version: LogIdx,
            /// in flight read requests
            pub readonly_reqs: Map<ReqId, ReadReq>,
            /// inflight update requests
            pub update_reqs: Map<ReqId, UpdateOp>,
            /// responses to update requests that haven't been returned
            pub update_resps: Map<ReqId, UpdateResp>,
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        // Invariant
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// the version of the log must be less than the length of the log
        #[invariant]
        pub fn inv_version(&self) -> bool {
            self.version <= self.log.len()
        }

        /// all update responses must have version that are less than the length of the log
        #[invariant]
        pub fn inv_update_resp_version(&self) -> bool {
            forall(|rid: ReqId| {
                #[trigger] self.update_resps.dom().contains(rid)
                ==> self.update_resps[rid].0 < self.log.len()
            })
        }

        /// all readonly requests must have a version that is less or equal to the log version
        #[invariant]
        pub fn inv_readonly_req_version(&self) -> bool {
            forall(|rid: ReqId| {
                self.readonly_reqs.dom().contains(rid)
                ==> if let ReadReq::Req { version, .. } = self.readonly_reqs[rid] {
                        version <= self.version}
                    else { true }
            })
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
        // Constructing the NRState
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// constructs the state of the data structure at a specific version given the log
        ///
        /// This function recursively applies the update operations to the initial state of the
        /// data structure and returns the state of the data structure at the given  version.
        pub open spec fn nrstate_at_version(&self, version: LogIdx) -> NRState
            recommends 0 <= version < self.log.len()
            decreases version
        {
            // decreases_when(version >= 0);
            if version == 0 {
                NRState::init()
            } else {
                self.nrstate_at_version((version - 1) as nat).update(self.log[version - 1]).0
            }
        }

        ////////////////////////////////////////////////////////////////////////////////////////////
        //
        // Read Operation Transitions
        // --------------------------
        //
        // Readonly operations are carried out in three steps:
        //  0. Add the request to the system (readonly requests)
        //  1. When a 'readonly' request begins record the version of the log.
        //  2. When it ends, we must return the answer at some version >= the recorded value.
        //
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// Read Request: Enter the read request operation into the system
        transition!{
            readonly_start(rid: ReqId, op: ReadonlyOp) {
                require(!pre.readonly_reqs.dom().contains(rid));

                // XXX: do we actually care whether an update request has the same id as an readonly request?
                // require(!pre.update_reqs.dom().contains(rid));
                // require(!pre.update_resps.dom().contains(rid));

                update readonly_reqs[rid] = ReadReq::Init{ op };
            }
        }

        /// Read Request: Read the current version of the log
        transition!{
            readonly_read_version(rid: ReqId) {
                require(pre.readonly_reqs.dom().contains(rid));
                require let ReadReq::Init { op } = pre.readonly_reqs.index(rid);

                update readonly_reqs[rid] = ReadReq::Req { op, version: pre.version };
            }
        }

        /// Read Request: Remove the request from the system
        ///
        /// This computes the state at version the request started
        transition!{
            readonly_finish(rid: ReqId, version: LogIdx, ret: ReturnType) {
                require(pre.readonly_reqs.dom().contains(rid));

                require let ReadReq::Req { op, version: current } = pre.readonly_reqs.index(rid);

                require(current <= version <= pre.log.len());
                require(version <= pre.version);
                require(ret == pre.nrstate_at_version(version).read(op));

                update readonly_reqs = pre.readonly_reqs.remove(rid);
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        //
        // Update Operation Transitions
        // ----------------------------
        //
        // Update operation happen in two steps:
        //  1. add the update to the local update requests
        //  2. collect the updates and store them in the log
        //  3. increase the version of the log
        //  4. return the version of the log at the update
        //
        ////////////////////////////////////////////////////////////////////////////////////////////


        /// Update Request: place an update request in the system
        transition!{
            update_start(rid: ReqId, op: UpdateOp) {
                // XXX: do we actually care whether an readonly request has the same id as an update request?
                // require(!pre.readonly_reqs.dom().contains(rid));
                require(!pre.update_reqs.dom().contains(rid));
                require(!pre.update_resps.dom().contains(rid));

                update update_reqs[rid] = op;
            }
        }

        /// Update Request: Add the update operations to the log
        ///
        /// Collect the updates given by the sequence of requests ids and place them in the log
        /// in-order. This moves the requests from update_reqs to update_resps.
        transition!{
            update_add_ops_to_log(rids: Seq<ReqId>) {
                // all request ids must be in the update requests
                require(forall(|r: ReqId|  #[trigger] rids.contains(r) ==> pre.update_reqs.dom().contains(r)));
                // the request ids must be unique, the sequence defines the update order
                require(seq_unique(rids));

                // add the update operations to the log
                update log = pre.log + Seq::new(rids.len(), |i: int| pre.update_reqs[i as nat]);

                // remove all update requests
                update update_reqs = pre.update_reqs.remove_keys(Set::new(|i| rids.contains(i)));

                // add the responses to the update requests
                update update_resps = pre.update_resps.union_prefer_right(
                        Map::new(|r: ReqId| { rids.contains(r) },
                                 |r: ReqId| { UpdateResp(pre.log.len() + rids.index_of(r) as nat)})
                );
            }
        }

        /// Update Request: Add the update operations to the log
        ///
        /// Collect the updates given by the sequence of requests ids and place them in the log
        /// in-order. This moves the requests from update_reqs to update_resps.
        transition!{
            update_add_ops_to_log_one(rid: ReqId) {
                // all request ids must be in the update requests
                require(pre.update_reqs.dom().contains(rid));

                // add the update operations to the log
                update log = pre.log.push(pre.update_reqs[rid]);

                // remove all update requests
                update update_reqs = pre.update_reqs.remove(rid);

                // add the responses to the update requests
                update update_resps = pre.update_resps.insert(rid, UpdateResp(pre.log.len()));
            }
        }

        /// Update: Increasing the version of the log
        ///
        /// The version value is monotonically increasing and must not be larger than the
        /// length of the log.
        transition!{
            update_incr_version(new_version: LogIdx) {
                require(pre.version <= new_version <= pre.log.len());
                update version = new_version;
            }
        }

        /// Update: Finish the update operation by removing it from the update responses
        transition!{
            update_finish(rid: nat) {
                require(pre.update_resps.dom().contains(rid));
                let uidx = pre.update_resps.index(rid).0;

                require(pre.version > uidx);
                require(pre.log.len() > uidx);

                update update_resps = pre.update_resps.remove(rid);
            }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // Stutter Step
        ////////////////////////////////////////////////////////////////////////////////////////////


        transition!{
            no_op() { }
        }


        ////////////////////////////////////////////////////////////////////////////////////////////
        // Inductiveness Proofs
        ////////////////////////////////////////////////////////////////////////////////////////////


        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(readonly_start)]
        fn readonly_start_inductive(pre: Self, post: Self, rid: ReqId, op: ReadonlyOp) { }

        #[inductive(readonly_read_version)]
        fn readonly_read_version_inductive(pre: Self, post: Self, rid: ReqId) { }

        #[inductive(readonly_finish)]
        fn readonly_finish_inductive(pre: Self, post: Self, rid: ReqId, version: LogIdx, ret: ReturnType) { }

        #[inductive(update_start)]
        fn update_start_inductive(pre: Self, post: Self, rid: ReqId, op: UpdateOp) { }

        #[inductive(update_add_ops_to_log)]
        fn update_add_ops_to_log_inductive(pre: Self, post: Self, rids: Seq<ReqId>) { }

        #[inductive(update_add_ops_to_log_one)]
        fn update_add_ops_to_log_one_inductive(pre: Self, post: Self, rid: ReqId) { }

        #[inductive(update_incr_version)]
        fn update_incr_version_inductive(pre: Self, post: Self, new_version: LogIdx) { }

        #[inductive(update_finish)]
        fn update_finish_inductive(pre: Self, post: Self, rid: nat) { }

        #[inductive(no_op)]
        fn no_op_inductive(pre: Self, post: Self) { }
    }
}
