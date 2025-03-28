// Verified Node Replication Library
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// rust_verify/tests/example.rs ignore
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use state_machines_macros::*;

use vstd::map::Map;
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::set::Set;

use crate::Dispatch;

use super::types::*;
use super::utils::*;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Unbounded Log
// =============
//
// The UnboundedLog is the first Refinement of the SimpleLog. As its name suggests, it also uses
// an unbounded log to represent updates to the data structure, however the log itself is represented
// by a map instead of a sequence. Moreover, the state machine also manages the data structure
// replicas.
//
////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
// Read Only Operations
////////////////////////////////////////////////////////////////////////////////////////////////////
/// ReadonlyState: Tracking the progress of read-only queries
///
/// Used to track the progress of a read-only queries on the data structure.
///
/// A readonly query takes place on a given node (`nid`), and follows the following algorithm:
///
///  1. Read the global value 'version_upper_bound'.
///  2. Wait until node-local value 'local_head' is greater than the value
///     of 'version_upper_bound' that was read in step 1.
///  3. Execute the query against the node-local replica and return the result.
///
/// (In real life, the thread does not just sit around 'waiting' in step 2;
/// it might run a combiner phase in order to advance the local_head.)
///
/// These 3 steps progress the status of the request through the cycle
///    Init -> VersionUpperBound -> ReadyToRead -> Done
///
/// (Note that the request itself does not "care" which nodeId it takes place on;
/// we only track the nodeId to make sure that steps 2 and 3 use the same node.)
/// --> After the changes to integrate this with the page table, we do actually care about the node
///     id because we use it to track what replica gets updated.
///
#[is_variant]
pub ghost enum ReadonlyState<DT: Dispatch> {
    /// a new read request that has come in
    Init { op: DT::ReadOperation, node_id: NodeId },
    /// has read the version upper bound value
    VersionUpperBound { op: DT::ReadOperation, node_id: NodeId, version_upper_bound: LogIdx },
    /// ready to read
    ReadyToRead { op: DT::ReadOperation, node_id: NodeId, version_upper_bound: LogIdx },
    /// read request is done
    Done { op: DT::ReadOperation, node_id: NodeId, version_upper_bound: LogIdx, ret: DT::Response },
}

impl<DT: Dispatch> ReadonlyState<DT> {
    pub open spec fn op(self) -> DT::ReadOperation {
        match self {
            ReadonlyState::Init { op, .. } => op,
            ReadonlyState::VersionUpperBound { op, .. } => op,
            ReadonlyState::ReadyToRead { op, .. } => op,
            ReadonlyState::Done { op, .. } => op,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Update Operation
////////////////////////////////////////////////////////////////////////////////////////////////////
////////// Updates and the combiner phase
//
// This part is a lot more complex; the lifecycle of an "update" is inherently
// tied to the lifecycle of the combiner, so I have to explain the entire combiner
// cycle for this to make sense.
//
// In particular, the combiner cycle starts with some (potentially empty) bulk collection
// of Update requests, which all start in UpdateState::Init.
// By the end of the combiner cycle (when it has gone back to 'Ready'), all the updates
// in that collection will be in UpdateState::Done.
//
// The combiner works as follows (keep in mind this is abstracted a bit from the
// real implementation).
//
//  1. Advance the 'tail' value by 1 for each update in the collection.
//     This creates a "LogEntry" for the given op at the given index.
//     It also updates the update from UpdateState::Init to UpdateState::Placed.
//
//      Note: This always appends to the log; there are never any "holes" in the log,
//      and the 'tail' always marks the end of the log. The log is unbounded
//      and not garbage-collected.
//      Keep in mind that the 'log' here is just an abstraction, and the "cyclic buffer"
//      that physically stores the log entries in real life has additional complexities.
//      We do not handle those complexities at this level of abstraction.
//
//      Note: Even when we have a bulk collection of updates, we still append the log
//      entries one at a time, once for each update. This means the log entries might
//      interleave with those of another thread.
//      This is more permissive than the real implementation, which advances the
//      'tail' with a single CAS operation, meaning that all the log entries
//      for the cycle will be contiguous in the log.
//      In the original Linear Dafny NR project, we modeled this step as a bulk update,
//      matching the implemenation. However, it turned out that:
//          (i) modeling 'bulk update' steps is kind of annoying
//          (ii) we never took advantage of the contiguity in the invariants
//      Since the single-step version is easier to model, and we don't lose anything for it,
//      that's what we do here.
//
//  2. Read the 'local_head' value for the given node.
//
//  3. Read the global 'tail' value.
//
//  4. Process all log entries in the range local_head..tail.
//     (This should include both the log entries we just creates, plus maybe some other
//     log entries from other nodes.)
//
//      NOTE: the global 'tail' value might change over the course of execution,
//      but we're going to stick with the local copy that we just read
//      (i.e., the value on the stack).
//
//     To process a log entry, we first apply the operation to the replica, and get
//     back a "return value". Next, we check if the log entry is for the given nodeId,
//     classifying it as "remote" or "local".
//      - If it's remote, we're done.
//      - If it's local, then we find the Update object in our bulk collection, and
//        update it from UpdateState::Placed to UpdateState::Applied, recording the
//        return value.
//
//  5. Update the global value of 'version_upper_bound'.
//     This step lets us move all the updates to UpdateState::Done.
//
//  6. Update the value of 'local_head'.
//
// Now, there are a bunch of things we need to prove so that the whole thing makes sense
// and so that the implementation can actually follow along and return data to the clients.
//
// Specifically, we have a sequence of "return ids" (recorded in the 'queued_ops' field)
// that need to get processed. When the implementation handles a "local" operation off the
// log, it appends the return value into a buffer; when it's done, it expects the buffer
// of return values to line up with all the update requests that it started with.
//
// What this means is that we need to show:
//   - When we process a "local" operation, its ReqId corresponds to the next
//     ReqId recorded in the queued_ops (i.e., the one at 'queue_index'.)
//   - When we have finished the entire loop, we have finished processing all
//     the ReqIds we expected (i.e., `queue_index == queued_ops.len()`).
//
// This means we need to establish an invariant between the combiner state and the
// log state at all times. Specifically, we need an invariant that relates the combiner
// state to the log entries whose node_ids match the combiner's node, describing where
// they are and in what order.
//
// The invariant roughly says that during step (4), (the "Loop" state):
//   The ReqIds in `queued_ops`, sliced from queue_index .. queued_ops.len()
//   match
//   The ReqIds in the log that are local, sliced from
//          local_head .. tail
// (Note that queue_index and local_head are the cursors that advance throughout the loop,
// while tail is the one recorded in step 3, so it's fixed.)
// Furthermore:
//   There are no local operations in the log between
//   the recorded tail and the global tail.
// See the invariant `wf_combiner_for_node_id`, as well as the predicates
// `LogRangeMatchesQueue` and `LogRangeNoNodeId`.
//
// Example: suppose N is the local node_id, and [a, b, c, d] are the request ids.
// We might be in a state that looks like this: (Here, '...' indicates remote entries,
// and '(N, x)' means a log entry with node id N that corresponds to request id x.)
//
//       CombinerState                                           CombinerState   global
//       local_head                                              tail     tail
//          |                                                              |               |
//       ===================================================================================
//          |          |       |       |        |       |          |       |       |       |
//  Log:    |  (N, b)  |  ...  |  ...  | (N, c) |  ...  |  (N, d)  |  ...  |  ...  |  ...  |
//          |          |       |       |        |       |          |       |       |       |
//       ===================================================================================
//
//  ---- Combiner state (in `CombinerState::Loop` phase).
//
//      queued_ops =  [  a,   b,   c,   d   ]
//                          ^
//                          |
//                  queue_index = 1
//
// ---- Update state:
//
//    a => UpdateState::Applied { ... }
//    b => UpdateState::Placed { ... }
//    c => UpdateState::Placed { ... }
//    d => UpdateState::Placed { ... }
//
// In the example, `LogRangeMatchesQueue` is the relation that shows that (b, c, d)
// agree between the queued_ops and the log; whereas `LogRangeNoNodeId` shows that there
// are no more local entries between the Combiner tail and the global tail.
//
// And again, in the real implementation, b, c, d will actually be contiguous in the log,
// but the state shown above is permitted by the model here.
// If we _were_ going to make use of contiguity, then the place to do it would probably
// be the definition of `LogRangeMatchesQueue`, but as I explained earlier, I didn't
// find it helpful.
//
// Another technical note: the LogEntry doesn't actually store the ReqId on it;
// `LogRangeMatchesQueue` has to connect the request id to the UpdateState, which then
// has a pointer into the log via `idx`. (It's possible that this could be simplified.)
#[is_variant]
pub ghost enum UpdateState<DT: Dispatch> {
    /// upated request has entered the system
    Init { op: DT::WriteOperation },
    /// update has been placed into the log
    Placed { op: DT::WriteOperation, idx: LogIdx },
    /// the update has been applied to the data structure
    Applied { ret: DT::Response, idx: LogIdx },
    /// the update is ready to be returned
    Done { ret: DT::Response, idx: LogIdx },
}

#[is_variant]
pub ghost enum CombinerState {
    Ready,
    Placed { queued_ops: Seq<ReqId> },
    LoadedLocalVersion { queued_ops: Seq<ReqId>, lversion: LogIdx },
    Loop {
        /// sequence of request ids of the local node
        queued_ops: Seq<ReqId>,
        /// version of the local replica
        lversion: LogIdx,
        /// index into the queued ops
        idx: nat,
        /// the global tail we'v read
        tail: LogIdx,
    },
    UpdatedVersion { queued_ops: Seq<ReqId>, tail: LogIdx },
}

impl CombinerState {
    pub open spec fn queued_ops(self) -> Seq<ReqId> {
        match self {
            CombinerState::Ready => Seq::empty(),
            CombinerState::Placed { queued_ops } => queued_ops,
            CombinerState::LoadedLocalVersion { queued_ops, .. } => queued_ops,
            CombinerState::Loop { queued_ops, .. } => queued_ops,
            CombinerState::UpdatedVersion { queued_ops, .. } => queued_ops,
        }
    }

    pub open spec fn queued_ops_set(&self) -> Set<ReqId> {
        seq_to_set(self.queued_ops())
    }
}

} // verus!
// end verus!
tokenized_state_machine! {
UnboundedLog<DT: Dispatch> {
    fields {
        /// the number of replicas
        #[sharding(constant)]
        pub num_replicas: nat,

        #[sharding(map)]
        pub log: Map<LogIdx, LogEntry<DT>>,

        #[sharding(variable)]
        pub tail: nat,

        #[sharding(map)]
        pub replicas: Map<NodeId, DT::View>,

        #[sharding(map)]
        pub local_versions: Map<NodeId, LogIdx>, // previously called "local tails"

        #[sharding(variable)]
        pub version_upper_bound: LogIdx, // previously called "ctail"

        #[sharding(map)]
        pub local_reads: Map<ReqId, ReadonlyState<DT>>,

        #[sharding(map)]
        pub local_updates: Map<ReqId, UpdateState<DT>>,

        #[sharding(map)]
        pub combiner: Map<NodeId, CombinerState>
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Invariant
    ////////////////////////////////////////////////////////////////////////////////////////////

    #[invariant]
    pub fn inv_request_ids_finite(&self) -> bool {
        &&& self.local_reads.dom().finite()
        &&& self.local_updates.dom().finite()
        &&& self.combiner.dom().finite()
    }

     /// there must be a replica for all nodes
     #[invariant]
     pub fn inv_replicas_complete(&self) -> bool {
         forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
             self.replicas.contains_key(node_id)
     }

    // /// ther emust be a local version for all nodes
    // #[invariant]
    // pub fn inv_local_versions_complete(&self) -> bool {
    //     forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
    //         self.local_versions.contains_key(node_id)
    // }

    /// there must be a combiner for all node
    #[invariant]
    pub fn inv_local_combiner_complete(&self) -> bool {
        forall |node_id: NodeId| 0 <= node_id < self.num_replicas <==>
            self.combiner.contains_key(node_id)
    }

    #[invariant]
    pub fn combiner_local_versions_domains(&self) -> bool {
        forall |k| self.local_versions.contains_key(k) <==> self.combiner.contains_key(k)
    }

    #[invariant]
    pub fn combiner_replicas_domains(&self) -> bool {
        forall |k| #![auto] self.replicas.contains_key(k) <==> self.combiner.contains_key(k)
    }

    pub open spec fn wf_node_id(&self, node_id: NodeId) -> bool {
        &&& 0 <= node_id < self.num_replicas
        &&& self.combiner.contains_key(node_id)
        &&& self.local_versions.contains_key(node_id)
        &&& self.replicas.contains_key(node_id)
    }


    // #[invariant]
    // pub fn inv_queued_ops_in_local_updates(&self) -> bool {
    //     forall |node_id, rid|
    //         (#[trigger] self.combiner.contains_key(node_id) && !(#[trigger] self.local_updates.contains_key(rid)))
    //             ==> !self.combiner[node_id].queued_ops().contains(rid)
    // }



    // && Inv_WF(s)
    // && Inv_GlobalTailCompleteTailOrdering(s)

    /// the version upper bound must be smaller or equal to the global tail
    /// Inv_GlobalTailCompleteTailOrdering
    #[invariant]
    pub fn inv_version_in_range(&self) -> bool {
        self.version_upper_bound <= self.tail
    }


    /// all local versions are less or equal to the version upper bound
    /// Inv_CompletedTailLowerBound && Inv_GlobalTailLowerBound(s)
    #[invariant]
    pub fn inv_local_version_upper_bound_heads(&self) -> bool {
        forall |node_id| (#[trigger]  self.local_versions.contains_key(node_id))
            ==> self.local_versions[node_id] <= self.version_upper_bound
    }


    /// The read request states are valid
    /// Inv_ReadRequest_WF(s) && Inv_ReadOnlyCtailsCompleteTailOrdering(s) && Inv_ReadOnlyStateNodeIdExists(s)
    #[invariant]
    pub fn inv_readonly_requests_wf(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
             ==> self.wf_readstate(self.local_reads[rid])
    }

    pub open spec fn wf_readstate(&self, rs: ReadonlyState<DT>) -> bool {
        match rs {
            ReadonlyState::Init{op, node_id} => {
                true
            }
            ReadonlyState::VersionUpperBound{op, node_id, version_upper_bound} => {
                version_upper_bound <= self.version_upper_bound
            }
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
            ReadonlyState::Done{op, ret, node_id, version_upper_bound } => {
                &&& self.wf_node_id(node_id)
                &&& version_upper_bound <= self.version_upper_bound
                &&& version_upper_bound <= self.current_local_version(node_id)
            }
        }
    }


    /// the combiner states are wellformed
    /// Inv_CombinerStateValid(s)
    #[invariant]
    pub open spec fn combiner_states_wf(&self) -> bool {
        forall |node_id| (#[trigger] self.combiner.contains_key(node_id))
             ==> self.wf_combiner_for_node_id(node_id)
    }

    pub open spec fn wf_combiner_for_node_id(&self, node_id: NodeId) -> bool
        recommends self.wf_node_id(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready => {
                // from other inv
                // &&& self.local_versions.contains_key(node_id)
                // &&& self.local_versions[node_id] <= self.tail
                &&& LogRangeNoNodeId(self.log, self.local_versions[node_id], self.tail, node_id)
            }
            CombinerState::Placed { queued_ops } => {
                // &&& self.local_versions.contains_key(node_id)
                // &&& self.local_versions[node_id] <= self.tail
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, self.local_versions[node_id], self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
               // we've just read the local tail value, and no-one else should modify that
                &&& lversion == self.local_versions[node_id]
                // by transitivity we have lversion <= self.version_upper_bound and self.tail
                // the local tail should be smaller or equal than the ctail
                // &&& lversion <= self.version_upper_bound
                // &&& lversion <= self.tail
                &&& LogRangeMatchesQueue(queued_ops, self.log, 0, lversion, self.tail, node_id, self.local_updates)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
                &&& seq_unique(queued_ops)
            }
            CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                // the global tail may have already advanced...
                &&& tail <= self.tail
                // we're advancing the local tail here
                &&& lversion >= self.local_versions[node_id]
                // the local tail should always be smaller or equal to the global tail
                &&& lversion <= tail
                // the log now contains all entries up to localtail
                &&& LogContainsEntriesUpToHere(self.log, lversion)
                &&& 0 <= idx <= queued_ops.len()
                &&& LogRangeMatchesQueue(queued_ops, self.log, idx, lversion, tail, node_id, self.local_updates)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, idx)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, idx)
                &&& seq_unique(queued_ops)
            }
            CombinerState::UpdatedVersion{ queued_ops, tail } => {
                // the global tail may have already advanced...
                // tail <= self.tail // by transitivity: self.version_upper_bound <= self.tail
                // update the ctail value
                &&& tail <= self.version_upper_bound
                // the local tail should be smaller than this one here
                &&& self.local_versions[node_id] <= tail
                // the log now contains all entries up to tail
                &&& LogContainsEntriesUpToHere(self.log, tail)
                &&& LogRangeNoNodeId(self.log, tail, self.tail, node_id)
                &&& QueueRidsUpdateDone(queued_ops, self.local_updates, queued_ops.len())
                &&& seq_unique(queued_ops)
            }
        }
    }


    /// the log contains entries up to the global tail
    /// Inv_LogEntriesGlobalTail(s)
    ///
    /// Inv_LogEntriesUpToCTailExists(s) && Inv_LogEntriesUpToLocalTailExist(s) are implied
    #[invariant]
    pub fn inv_log_complete(&self) -> bool {
        &&& LogContainsEntriesUpToHere(self.log, self.tail)
        &&& LogNoEntriesFromHere(self.log, self.tail)
    }


    /// Wellformed local update state
    /// Inv_LocalUpdatesIdx(s)
    #[invariant]
    pub fn inv_local_updates(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.inv_local_updates_wf(self.local_updates[rid])
    }

    pub open spec fn inv_local_updates_wf(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Init { op } => { true },
            UpdateState::Placed { op: _, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Applied { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.tail
            },
            UpdateState::Done { ret, idx } => {
                &&& self.log.contains_key(idx)
                &&& idx < self.version_upper_bound
            },
        }
    }


    /// The results of the read operation must match
    /// Inv_ReadOnlyResult(s)
    #[invariant]
    pub fn inv_read_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_reads.contains_key(rid))
            ==>  self.read_results_match(self.local_reads[rid])
    }

    pub open spec fn read_results_match(&self, read: ReadonlyState<DT>) -> bool {
        match read {
            ReadonlyState::Done { ret, version_upper_bound, op, node_id } => {
                exists |v: nat| (#[trigger] rangeincl(version_upper_bound, v, self.version_upper_bound))
                    && v <= self.current_local_version(node_id)
                    && ret == DT::dispatch_spec(compute_nrstate_at_version(self.log, v), op)
            },
            _ => true,
        }
    }


    /// The results of the updates must match
    /// Inv_UpdateResults(s)
    #[invariant]
    pub fn inv_update_results(&self) -> bool {
        forall |rid| (#[trigger] self.local_updates.contains_key(rid))
            ==>  self.update_results_match(self.local_updates[rid])
    }

    pub open spec fn update_results_match(&self, update: UpdateState<DT>) -> bool {
        match update {
            UpdateState::Applied { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            UpdateState::Done { ret, idx } => {
                ret == DT::dispatch_mut_spec(compute_nrstate_at_version(self.log, idx), self.log[idx].op).1
            },
            _ => true,
        }
    }


    /// All combiners must have distinct request ids they are working on
    /// Inv_CombinerRidsDistinct(s)
    #[invariant]
    pub fn inv_combiner_rids_distinct(&self) -> bool
    {
      forall |node_id1, node_id2|
          (#[trigger] self.combiner.contains_key(node_id1)
          && #[trigger] self.combiner.contains_key(node_id2)
          && node_id1 != node_id2) ==>
            seq_disjoint(self.combiner[node_id1].queued_ops(), self.combiner[node_id2].queued_ops())
    }


    /// the state of the replica must match the current version of the log
    #[invariant]
    pub open spec fn replica_state(&self) -> bool {
        forall |node_id| (#[trigger] self.replicas.contains_key(node_id)) ==>
            self.replicas[node_id] == compute_nrstate_at_version(self.log, self.current_local_version(node_id))
    }

    #[invariant]
    pub open spec fn current_local_version_in_range(&self) -> bool {
        forall |node_id| (#[trigger] self.replicas.contains_key(node_id)) ==>
            self.current_local_version(node_id) <= self.tail
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // State Machine Initialization
    ////////////////////////////////////////////////////////////////////////////////////////////

    init!{
        initialize(number_of_nodes: nat) {
            require(number_of_nodes > 0);

            init num_replicas = number_of_nodes;
            init log = Map::empty();
            init tail = 0;
            init replicas = Map::new(|n: NodeId| n < number_of_nodes, |n| DT::init_spec());
            init local_versions = Map::new(|n: NodeId| n < number_of_nodes, |n| 0);
            init version_upper_bound = 0;
            init local_reads = Map::empty();
            init local_updates = Map::empty();
            init combiner = Map::new(|n: NodeId| n < number_of_nodes, |n| CombinerState::Ready);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////
    // Readonly Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////

    /// Read Request: Read the version of the log
    ///
    /// The algorithm waits while local_version < read_version
    transition!{
        readonly_version_upper_bound(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::Init { op, node_id } ];
            add    local_reads += [ rid => ReadonlyState::VersionUpperBound {
                                                op, version_upper_bound: pre.version_upper_bound, node_id } ];
        }
    }

    /// Read Request: wait until the version of the state has reached the version of the log
    ///
    /// The algorithm waits while local_version < read_version
    transition!{
        readonly_ready_to_read(rid: ReqId) {
            remove local_reads    -= [ rid => let ReadonlyState::VersionUpperBound { op, version_upper_bound, node_id } ];
            have   local_versions >= [ node_id => let local_head ];

            require(local_head >= version_upper_bound);

            add local_reads += [ rid => ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} ];
        }
    }

    /// Read Request: perform the read request on the local replica, the combiner must not be busy
    transition!{
        readonly_apply(rid: ReqId) {
            remove local_reads -= [ rid => let ReadonlyState::ReadyToRead { op, node_id, version_upper_bound } ];
            have   combiner    >= [ node_id => CombinerState::Ready ];
            have   replicas    >= [ node_id => let state ];

            let ret = DT::dispatch_spec(state, op);

            add local_reads += [ rid => ReadonlyState::Done{ op, node_id, version_upper_bound, ret } ];
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Out-of-band Read Transition
    ////////////////////////////////////////////////////////////////////////////////////////////////


    /// Out-of-band read (e.g. by the MMU) on a replica
    readonly!{
        readonly_view_oob(replica: nat, res: DT::View) {
            //require label is Internal; // TODO: ??
            require replica < pre.num_replicas;
            require res == pre.replicas[replica];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Update Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////

    /// Combiner: Collect the operations and place them into the log
    transition!{
        update_place_ops_in_log_one(node_id: NodeId, rid: ReqId) {
            // Only allowing a single request at a time
            // (in contrast to the seagull one which does it in bulk).
            // Hopefully this leads to some easier proofs.
            remove combiner      -= [ node_id => let CombinerState::Placed{ queued_ops } ];
            remove local_updates -= [ rid => let UpdateState::Init{ op }];

            update tail = pre.tail + 1;
            add log           += [ pre.tail => LogEntry{ op, node_id }];
            add local_updates += [ rid => UpdateState::Placed{ op, idx: pre.tail }];
            add combiner      += [ node_id => CombinerState::Placed { queued_ops: queued_ops.push(rid) } ];
        }
    }

    transition!{
        update_done(rid:ReqId) {
            remove local_updates -= [ rid => let UpdateState::Applied { ret, idx } ];

            // we must have applied the
            require(pre.version_upper_bound > idx);

            add local_updates += [ rid => UpdateState::Done { ret, idx } ];
        }
    }

    /*/// Update: Remove a finished update from the system
    transition!{
        update_finish(rid:ReqId) {
            remove local_updates -= [ rid => let UpdateState::Done { ret, idx } ];
        }
    }*/


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Combiner Execute Transitions
    ////////////////////////////////////////////////////////////////////////////////////////////


    /// Combiner: start the combiner to execute the update operations on the local replica
    transition!{
        exec_trivial_start(node_id: NodeId) {
            remove combiner -= [ node_id => CombinerState::Ready ];

            add    combiner += [ node_id => CombinerState::Placed { queued_ops: Seq::empty() } ];
        }
    }

    /// Combiner: read the version of the local replica
    transition!{
        exec_load_local_version(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Placed { queued_ops } ];

            have   local_versions >= [node_id => let lversion];

            add    combiner      += [ node_id => CombinerState::LoadedLocalVersion { queued_ops, lversion }];
        }
    }

    /// Combiner: read the global tail
    transition!{
        exec_load_global_head(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            add    combiner += [ node_id => CombinerState::Loop { queued_ops, lversion, idx: 0, tail: pre.tail } ];
        }
    }

    /// Combiner: Safety condition, the queue index must be within bounds
    property!{
        pre_exec_dispatch_local(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];
            have log      >= [ lversion => let log_entry ];

            require(log_entry.node_id == node_id);
            require(lversion < tail);
            assert(idx < queued_ops.len()) by {
                // assert(pre.wf_combiner_for_node_id(node_id));
                // assert(lversion < tail);
                // assert(pre.log.index(lversion).node_id == node_id);
            };
            assert(queued_ops.len() > 0);
        }
    }

    /// Combiner: dispatch a local update and apply it to the local replica and record the outcome of the update
    transition!{
        exec_dispatch_local(node_id: NodeId) {
            remove combiner      -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx } ];
            remove replicas      -= [ node_id => let old_nr_state ];
            let rid = queued_ops.index(idx as int);
            remove local_updates -= [ rid => let local_update ];

            have log >= [lversion => let log_entry];

            // require(local_update.is_Placed());

            // apply all updates between lhead and global tail that were enqueued from local node
            require(lversion < tail);
            require(log_entry.node_id == node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add local_updates += [ rid => UpdateState::Applied { ret, idx: lversion }];
            add replicas      += [ node_id => new_nr_state];
            add combiner      += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx: idx + 1}];
        }
    }

    /// Combiner: dispatch a remote update and apply it to the local replica
    transition!{
        exec_dispatch_remote(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx } ];
            remove replicas -= [ node_id => let old_nr_state ];

            have   log      >= [ lversion => let log_entry ];

            // apply all updates between lhead and global tail that were enqueued from remote nodes
            require(lversion < tail);
            require(log_entry.node_id != node_id);
            let (new_nr_state, ret) = DT::dispatch_mut_spec(old_nr_state, log_entry.op);

            add replicas    += [ node_id => new_nr_state ];
            add combiner    += [ node_id => CombinerState::Loop { queued_ops, lversion: lversion + 1, tail, idx}];
        }
    }

    /// Combiner: Safety condition, if we applied all updates, idx must be the length of the list
    property!{
        pre_exec_update_version_upper_bound(node_id: NodeId) {
            have combiner >= [ node_id => let CombinerState::Loop{ queued_ops, lversion, tail, idx } ];

            require(lversion == tail);
            assert(idx == queued_ops.len()) by {
                // assert(pre.wf_combiner_for_node_id(node_id));
                // assert(lversion == tail);
            };
        }
    }

    /// Combiner: update the version upper bound when all updates have been applied to the local replica
    transition!{
        exec_update_version_upper_bound(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::Loop { queued_ops, lversion, tail, idx, }];

            // we applied all updates up to the global tail we've read
            require(lversion == tail);

            // assert(idx == queued_ops.len()) by {
            //     //assert(pre.wf_combiner_for_node_id(node_id));
            // };

            update version_upper_bound = if pre.version_upper_bound >= tail {
                pre.version_upper_bound
            } else {
                tail
            };
            add combiner += [ node_id => CombinerState::UpdatedVersion { queued_ops, tail } ];
        }
    }

    /// Combiner: is done, bump the local version and combiner returns to ready state
    transition!{
        exec_finish(node_id: NodeId) {
            remove combiner       -= [ node_id => let CombinerState::UpdatedVersion { queued_ops, tail } ];
            remove local_versions -= [ node_id => let old_local_head ];

            // here have the local updates updated to done.

            add    local_versions += [ node_id => tail ];
            add    combiner       += [ node_id => CombinerState::Ready ];
        }
    }

    /// Combiner: is done, without any change
    transition!{
        exec_finish_no_change(node_id: NodeId) {
            remove combiner -= [ node_id => let CombinerState::LoadedLocalVersion { queued_ops, lversion } ];

            require(lversion == pre.tail);
            assert(queued_ops.len() == 0);

            add    combiner += [ node_id => CombinerState::Ready];
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////////
    // Inductiveness Proofs
    ////////////////////////////////////////////////////////////////////////////////////////////


    #[inductive(initialize)]
    fn initialize_inductive(post: Self, number_of_nodes: nat) {

        // XXX: is it really that hard to show finetness of map domain?
        let max_dom = (post.num_replicas - 1) as nat;
        let cmap = map_new_rec(max_dom, CombinerState::Ready);
        assert(cmap.dom().finite()) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> post.combiner.contains_key(n));
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n)) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(forall |n: nat| 0 <= n <= max_dom <==> cmap.contains_key(n));
        assert(forall |n: nat| 0 <= n < post.num_replicas <==> cmap.contains_key(n));

        assert(forall |n: nat| post.combiner.contains_key(n) <==> #[trigger]cmap.contains_key(n));
        assert(post.combiner.dom() =~= cmap.dom());
        assert(forall |n| #[trigger]post.combiner.contains_key(n) ==> post.combiner[n] == CombinerState::Ready);

        assert(forall |n| #[trigger]cmap.contains_key(n) ==> cmap[n] == CombinerState::Ready) by {
            map_new_rec_dom_finite(max_dom, CombinerState::Ready);
        }
        assert(post.combiner =~= cmap);
        // assert_maps_equal!(post.combiner, cmap);
    }


    #[inductive(readonly_version_upper_bound)]
    fn readonly_version_upper_bound_inductive(pre: Self, post: Self, rid: ReqId) { }

    #[inductive(readonly_ready_to_read)]
    fn readonly_ready_to_read_inductive(pre: Self, post: Self, rid: ReqId) {
        match post.local_reads[rid] {
            ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                assert(post.combiner.contains_key(node_id));
                assert(post.local_versions.contains_key(node_id));
                assert(post.replicas.contains_key(node_id));
                assert(version_upper_bound <= post.version_upper_bound);
                assert(version_upper_bound <= post.current_local_version(node_id));
            }
            _ => { }
        };
        assert(post.wf_readstate(post.local_reads[rid]));
    }

    #[inductive(readonly_apply)]
    fn readonly_apply_inductive(pre: Self, post: Self, rid: ReqId) {
        let ret = post.local_reads[rid].get_Done_ret();
        let nid = post.local_reads[rid].get_Done_node_id();
        let vup = post.local_reads[rid].get_Done_version_upper_bound();
        let v = post.local_versions[nid];
        assert(rangeincl(vup, v, post.version_upper_bound));
    }

    pub proof fn add_ticket_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        input: crate::InputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::add_ticket(pre, post, input, rid),
            rid == get_fresh_nat(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner)
        ensures post.invariant(),
    {
        get_fresh_nat_not_in(pre.local_updates.dom() + pre.local_reads.dom(), pre.combiner);
        match input {
            crate::InputOperation::Read(op, node_id) => {
                assert(post.inv_readonly_requests_wf());
            }
            crate::InputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    assert(post.combiner[node_id] == pre.combiner[node_id]);
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                            assert(post.wf_combiner_for_node_id(node_id));
                        }
                        CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {
                        }
                    }
                }
            }
        }
    }

    #[inductive(update_done)]
    fn update_done_inductive(pre: Self, post: Self, rid: ReqId) {
        assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
            match post.combiner[node_id] {
                CombinerState::Placed { queued_ops } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop{ queued_ops, idx, lversion, tail } => {
                    LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                }
                _ => {}
            }
        }
    }

    pub proof fn consume_stub_inductive(
        pre: UnboundedLog::State<DT>,
        post: UnboundedLog::State<DT>,
        output: crate::OutputOperation<DT>,
        rid: crate::ReqId,
    )
        requires pre.invariant(),
            crate::consume_stub(pre, post, output, rid),
        ensures post.invariant(),
    {
        match output {
            crate::OutputOperation::Read(op) => {
                assert(post.inv_readonly_requests_wf());
            }
            crate::OutputOperation::Write(op) => {
                assert forall |node_id| #[trigger] post.combiner.contains_key(node_id) implies post.wf_combiner_for_node_id(node_id) by {
                    match post.combiner[node_id] {
                        CombinerState::Placed { queued_ops } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, post.local_versions[node_id], post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::LoadedLocalVersion{ queued_ops, lversion } => {
                            LogRangeMatchesQueue_update_change_2(queued_ops, post.log, 0, lversion, post.tail, node_id, pre.local_updates, post.local_updates);
                        }
                        CombinerState::Loop { queued_ops, idx, lversion, tail } => {
                            LogRangeMatchesQueue_update_change(queued_ops, post.log, idx, lversion, tail, node_id, pre.local_updates, post.local_updates);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    #[inductive(exec_trivial_start)]
    fn exec_trivial_start_inductive(pre: Self, post: Self, node_id: NodeId) {
        concat_LogRangeNoNodeId_LogRangeMatchesQueue(
            Seq::empty(), post.log, 0,
            pre.local_versions[node_id],
            pre.tail,
            post.tail,
            node_id,
            post.local_updates);

        assert(post.wf_combiner_for_node_id(node_id));
    }

    #[inductive(update_place_ops_in_log_one)]
    fn update_place_ops_in_log_one_inductive(pre: Self, post: Self, node_id: NodeId, rid: ReqId) {

        let old_queued_ops = pre.combiner[node_id].get_Placed_queued_ops();
        let op = pre.local_updates[rid].get_Init_op();

        assert(post.wf_combiner_for_node_id(node_id)) by {
            match post.combiner[node_id] {
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append(old_queued_ops, pre.log, post.log, 0,
                        post.local_versions[node_id], pre.tail,
                        node_id, pre.local_updates, post.local_updates, rid,
                        LogEntry{ op, node_id });
                }
                _ => { }
            }
        }

        assert(post.inv_local_updates_wf(post.local_updates[rid]));

        assert forall |node_id1| #[trigger] post.combiner.contains_key(node_id1)
            && node_id1 != node_id
            implies post.wf_combiner_for_node_id(node_id1)
        by {
            assert(pre.combiner[node_id1] === post.combiner[node_id1]);
            assert(pre.wf_combiner_for_node_id(node_id1));
            match pre.combiner[node_id1] {
                CombinerState::Ready => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        post.local_versions[node_id1], pre.tail, node_id1, LogEntry{ op, node_id });
                }
                CombinerState::Placed{queued_ops} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, post.local_versions[node_id1], pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                    LogRangeMatchesQueue_append_other_augment(queued_ops, pre.log, post.log,
                        0, lversion, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                }
                CombinerState::Loop{queued_ops, lversion, idx, tail} => {
                    LogRangeMatchesQueue_append_other(queued_ops, pre.log, post.log,
                        idx, lversion, tail, pre.tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail,
                        node_id1, LogEntry{ op, node_id });
                }
                CombinerState::UpdatedVersion{queued_ops, tail} => {
                    LogRangeNoNodeId_append_other(pre.log, post.log,
                        tail, pre.tail, node_id1, LogEntry{ op, node_id });
                }
            }
        }

        assert (forall |nid| (#[trigger] pre.replicas.contains_key(nid)) ==> pre.local_versions.contains_key(nid));

        assert forall |nid| (#[trigger] post.replicas.contains_key(nid)) implies
            post.replicas[nid] == compute_nrstate_at_version(post.log, post.current_local_version(nid)) by
        {
            compute_nrstate_at_version_preserves(pre.log, post.log, post.current_local_version(nid));
        }

        assert forall |rid| (#[trigger] post.local_updates.contains_key(rid))
            implies post.update_results_match(post.local_updates[rid]) by
        {
            match post.local_updates[rid] {
                UpdateState::Applied { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                UpdateState::Done { ret, idx } => {
                    compute_nrstate_at_version_preserves(pre.log, post.log, idx);
                },
                _ => {},
            }
        }

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid))
            implies post.read_results_match(post.local_reads[rid]) by
        {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, node_id: node_id0 } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ver <= pre.current_local_version(node_id0)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(pre.log, ver), op));
                    compute_nrstate_at_version_preserves(pre.log, post.log, ver);
                },
                _ => {},
            }
        }
    }


    #[inductive(exec_load_local_version)]
    fn exec_load_local_version_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_load_global_head)]
    fn exec_load_global_head_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_dispatch_local)]
    fn exec_dispatch_local_inductive(pre: Self, post: Self, node_id: NodeId) {
        assert(post.wf_combiner_for_node_id(node_id)) by {
            LogRangeMatchesQueue_update_change(
                post.combiner[node_id].get_Loop_queued_ops(),
                post.log, post.combiner[node_id].get_Loop_idx(), post.combiner[node_id].get_Loop_lversion(),
                pre.combiner[node_id].get_Loop_tail(), node_id, pre.local_updates, post.local_updates);
        }

        let c = pre.combiner[node_id];
        let rid = c.get_Loop_queued_ops().index(c.get_Loop_idx() as int);
        assert forall |node_id0| #[trigger] post.combiner.contains_key(node_id0) && node_id0 != node_id
            implies post.wf_combiner_for_node_id(node_id0)
        by {
            match pre.combiner[node_id0] {
            CombinerState::Ready => {
            }
            CombinerState::Placed{queued_ops} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, post.local_versions[node_id0], post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::LoadedLocalVersion{queued_ops, lversion} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, 0, lversion, post.tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::Loop{queued_ops, idx, lversion, tail} => {
                LogRangeMatchesQueue_update_change_2(
                queued_ops, post.log, idx, lversion, tail, node_id0, pre.local_updates, post.local_updates);
            }
            CombinerState::UpdatedVersion{queued_ops, tail} => {
            }
            }
        }
    }

    #[inductive(exec_dispatch_remote)]
    fn exec_dispatch_remote_inductive(pre: Self, post: Self, node_id: NodeId) {}

    #[inductive(exec_update_version_upper_bound)]
    fn exec_update_version_upper_bound_inductive(pre: Self, post: Self, node_id: NodeId) {
        // assert(post.log == pre.log);
        assert(post.version_upper_bound >= pre.version_upper_bound);

        assert forall |rid| (#[trigger] post.local_reads.contains_key(rid)) implies post.read_results_match(post.local_reads[rid]) by {
            match post.local_reads[rid] {
                ReadonlyState::Done { ret, version_upper_bound, op, node_id: node_id0 } => {
                    let ver = choose |ver| (#[trigger] rangeincl(version_upper_bound, ver, pre.version_upper_bound)
                        && ver <= pre.current_local_version(node_id0)
                        && ret == DT::dispatch_spec(compute_nrstate_at_version(post.log, ver), op));
                    assert(rangeincl(version_upper_bound, ver, post.version_upper_bound));
                },
                _ => {}
            }
        }
    }

    #[inductive(exec_finish)]
    fn exec_finish_inductive(pre: Self, post: Self, node_id: NodeId) { }

    #[inductive(exec_finish_no_change)]
    fn exec_finish_no_change_inductive(pre: Self, post: Self, node_id: NodeId) { }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Helper Functions
    ////////////////////////////////////////////////////////////////////////////////////////////////

    /// obtains the current local version for the given node depending on the combiner state
    pub open spec fn current_local_version(&self, node_id: NodeId) -> nat
        recommends self.combiner.contains_key(node_id) && self.local_versions.contains_key(node_id)
    {
        match self.combiner[node_id] {
            CombinerState::Ready                              => self.local_versions[node_id],
            CombinerState::Placed{ .. }                       => self.local_versions[node_id],
            CombinerState::LoadedLocalVersion{ lversion, .. } => lversion,
            CombinerState::Loop { lversion, .. }              => lversion,
            CombinerState::UpdatedVersion { tail, .. }        => tail,
        }
    }

    // pub open spec fn combiners_fresh_req_id(&self, rid: ReqId) -> bool {
    //     forall |n| self.combiner.contains_key(n)
    //         ==> !self.combiner[n].queued_ops().contains(rid)
    // }
}

} // end tokenized_state_machine!

verus! {

// pub open spec fn combiner_request_ids(node_ids: Set<NodeId>, combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
//     recommends (forall |n| (#[trigger] node_ids.contains(n)) ==> #[trigger]combiners.contains_key(n))
//     decreases node_ids.len() when (node_ids.finite() && node_ids.len() >= 0)
// {
//     if node_ids.finite() {
//         if node_ids.len() == 0 {
//             Set::empty()
//         } else {
//             let node_id = node_ids.choose();
//             combiner_request_ids(node_ids.remove(node_id), combiners) + seq_to_set(combiners[node_id].queued_ops())
//         }
//     } else {
//         arbitrary()
//     }
// }
pub open spec fn combiner_request_ids(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    decreases combiners.dom().len(),
    when (combiners.dom().finite() && combiners.dom().len() >= 0)
    via combiner_request_ids_decreases
{
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
            Set::empty()
        } else {
            let node_id = combiners.dom().choose();
            let req_ids = combiner_request_ids(combiners.remove(node_id));
            req_ids + seq_to_set(combiners[node_id].queued_ops())
        }
    } else {
        arbitrary()
    }
}

#[via_fn]
proof fn combiner_request_ids_decreases(combiners: Map<NodeId, CombinerState>) {
    if combiners.dom().finite() {
        if combiners.dom().len() == 0 {
        } else {
            let node_id = combiners.dom().choose();
            assert(combiners.remove(node_id).dom().len() < combiners.dom().len());  // INCOMPLETENESS weird incompleteness
        }
    } else {
    }
}

pub proof fn combiner_request_ids_proof(combiners: Map<NodeId, CombinerState>) -> Set<ReqId>
    requires
        combiners.dom().finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        Set::empty()
    } else {
        let node_id = combiners.dom().choose();
        let s1 = combiner_request_ids_proof(combiners.remove(node_id));
        s1 + seq_to_set(
            combiners[node_id].queued_ops(),
        )
        // combiner_request_ids_proof(combiners.remove(node_id)) + seq_to_set(combiners[node_id].queued_ops())

    }
}

pub open spec fn combiner_request_id_fresh(
    combiners: Map<NodeId, CombinerState>,
    rid: ReqId,
) -> bool {
    forall|n| (#[trigger] combiners.contains_key(n)) ==> !combiners[n].queued_ops().contains(rid)
}

pub proof fn combiner_request_ids_not_contains(combiners: Map<NodeId, CombinerState>, rid: ReqId)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_id_fresh(combiners, rid) <==> !combiner_request_ids(combiners).contains(
            rid,
        ),
    decreases combiners.dom().len(),
{
    if !(combiners.dom() =~= Set::empty()) {
        let node_id = combiners.dom().choose();
        combiner_request_ids_not_contains(combiners.remove(node_id), rid);
        assert(combiner_request_id_fresh(combiners.remove(node_id), rid) <==> !combiner_request_ids(
            combiners.remove(node_id),
        ).contains(rid));
        if !combiners[node_id].queued_ops().contains(rid) {
            if combiner_request_id_fresh(combiners.remove(node_id), rid) {
                assert forall|n|
                    (#[trigger] combiners.contains_key(
                        n,
                    )) implies !combiners[n].queued_ops().contains(rid) by {
                    if n != node_id {
                        assert(combiners.remove(node_id).contains_key(n));
                    }
                }
            }
        }
    }
}

pub proof fn combiner_request_ids_finite(combiners: Map<NodeId, CombinerState>)
    requires
        combiners.dom().finite(),
    ensures
        combiner_request_ids(combiners).finite(),
    decreases combiners.dom().len(),
{
    if combiners.dom().len() == 0 {
        assert(combiner_request_ids(combiners).finite())
    } else {
        let node_id = combiners.dom().choose();
        assert(combiner_request_ids(combiners.remove(node_id)).finite()) by {
            combiner_request_ids_finite(combiners.remove(node_id));
        }
        assert(seq_to_set(combiners[node_id].queued_ops()).finite()) by {
            seq_to_set_is_finite(combiners[node_id].queued_ops());
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper Functions
////////////////////////////////////////////////////////////////////////////////////////////////////
pub closed spec fn get_fresh_nat(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>) -> nat
    recommends
        reqs.finite() && combiner.dom().finite(),
{
    choose|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n)
}

proof fn max_of_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        forall|x: nat| #[trigger] s.contains(x) ==> x <= r,
    decreases s.len(),
{
    if s.is_empty() {
        0
    } else {
        let v1 = s.choose();
        let v2 = max_of_set(s.remove(v1));
        assert(forall|x: nat| #[trigger] s.contains(x) && x != v1 ==> s.remove(v1).contains(x));
        if v1 >= v2 {
            v1
        } else {
            v2
        }
    }
}

proof fn element_outside_set(s: Set<nat>) -> (r: nat)
    requires
        s.finite(),
    ensures
        !s.contains(r),
{
    max_of_set(s) + 1
}

pub proof fn get_fresh_nat_not_in(reqs: Set<ReqId>, combiner: Map<NodeId, CombinerState>)
    requires
        reqs.finite(),
        combiner.dom().finite(),
    ensures
        !reqs.contains(get_fresh_nat(reqs, combiner)),
        combiner_request_id_fresh(combiner, get_fresh_nat(reqs, combiner)),
{
    let rid = get_fresh_nat(reqs, combiner);
    let combiner_req_ids = combiner_request_ids(combiner);
    assert(!combiner_req_ids.contains(rid) == combiner_request_id_fresh(combiner, rid)) by {
        combiner_request_ids_not_contains(combiner, rid);
    }
    assert(combiner_req_ids.finite()) by {
        combiner_request_ids_finite(combiner);
    }
    let req_ids = reqs + combiner_req_ids;
    assert(req_ids.finite());
    let r = element_outside_set(req_ids);
    // let r = choose |r| !req_ids.contains(r);
    assert(!reqs.contains(r));
    assert(!combiner_req_ids.contains(r));
    assert(combiner_request_id_fresh(combiner, r)) by {
        combiner_request_ids_not_contains(combiner, r);
    }
    assert(exists|n| !reqs.contains(n) && combiner_request_id_fresh(combiner, n));
}

/// the log contains all entries up to, but not including the provided end
pub open spec fn LogContainsEntriesUpToHere<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    end: LogIdx,
) -> bool {
    forall|i: nat| 0 <= i < end ==> log.contains_key(i)
}

/// the log doesn't contain any entries at or above the provided start index
pub open spec fn LogNoEntriesFromHere<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    start: LogIdx,
) -> bool {
    forall|i: nat| start <= i ==> !log.contains_key(i)
}

/// the log contains no entries with the given node id between the supplied indices
pub open spec fn LogRangeNoNodeId<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    start: LogIdx,
    end: LogIdx,
    node_id: NodeId,
) -> bool {
    decreases_when(start <= end);
    decreases(end - start);
    (start < end ==> {
        &&& log.contains_key(start)
        &&& log.index(start).node_id != node_id
        &&& LogRangeNoNodeId(log, start + 1, end, node_id)
    })
}

/// predicate that the a range in the log matches the queue of updates
pub open spec fn LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>,
    log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: LogIdx,
    logIndexUpper: LogIdx,
    nodeId: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
) -> bool {
    recommends([0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper)]);
    decreases_when(logIndexLower <= logIndexUpper);
    decreases(logIndexUpper - logIndexLower);
    // if we hit the end of the log range, we should be at the end of the queue
    &&& (logIndexLower == logIndexUpper ==> queueIndex
        == queue.len())
    // otherwise, we check the log

    &&& (logIndexLower < logIndexUpper ==> {
        &&& log.contains_key(
            logIndexLower,
        )
        // local case: the entry has been written by the local node

        &&& (log.index(logIndexLower).node_id == nodeId ==> {
            // there must be an entry in the queue that matches the log entry
            &&& queueIndex < queue.len()
            &&& updates.contains_key(queue.index(queueIndex as int))
            &&& updates.index(queue.index(queueIndex as int)).is_Placed()
            &&& updates.index(queue.index(queueIndex as int)).get_Placed_idx() == logIndexLower
            &&& LogRangeMatchesQueue(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates,
            )
        })
        // remote case: the entry has been written by the local node, there is nothing to match, recourse

        &&& (log.index(logIndexLower).node_id != nodeId ==> LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper,
            nodeId,
            updates,
        ))
    })
}

// pub open spec fn LogRangeMatchesQueue2<DT: Dispatch>(queue: Seq<ReqId>, log: Map<LogIdx, LogEntry<DT>>, queueIndex: nat,
//     logIndexLower: LogIdx, logIndexUpper: LogIdx, nodeId: NodeId,
//     updates: Map<ReqId, UpdateState<DT>>) -> bool
// {
//     recommends([ 0 <= queueIndex <= queue.len(), LogContainsEntriesUpToHere(log, logIndexUpper) ]);
//     decreases_when(logIndexLower <= logIndexUpper);
//     decreases(logIndexUpper - logIndexLower);
//     // if we hit the end of the log range, we should be at the end of the queue
//     &&& (logIndexLower == logIndexUpper ==> queueIndex == queue.len())
//     // otherwise, we check the log
//     &&& (logIndexLower < logIndexUpper ==> {
//         &&& log.contains_key(logIndexLower)
//         // local case: the entry has been written by the local node
//         &&& (log.index(logIndexLower).node_id == nodeId ==> {
//             // there must be an entry in the queue that matches the log entry
//             &&& queueIndex < queue.len()
//             // &&& updates.contains_key(queue.index(queueIndex as int))
//             // &&& updates.index(queue.index(queueIndex as int)).is_Placed()
//             // &&& updates.index(queue.index(queueIndex as int)).get_Placed_idx() == logIndexLower
//             &&& LogRangeMatchesQueue2(queue, log, queueIndex + 1, logIndexLower + 1, logIndexUpper, nodeId, updates)
//         })
//         // remote case: the entry has been written by the local node, there is nothing to match, recourse
//         &&& (log.index(logIndexLower).node_id != nodeId ==>
//             LogRangeMatchesQueue2(queue, log, queueIndex, logIndexLower + 1, logIndexUpper, nodeId, updates)
//         )
//     })
// }
proof fn LogRangeMatchesQueue_update_change<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates1,
        ),
        forall|rid| #[trigger]
            updates1.contains_key(rid) ==> updates1[rid].is_Placed() && logIndexLower
                <= updates1[rid].get_Placed_idx() < logIndexUpper ==> updates2.contains_key(rid)
                && updates2[rid] === updates1[rid],
    ensures
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates2,
        ),
    decreases logIndexUpper - logIndexLower,
{
    if logIndexLower == logIndexUpper {
    } else {
        if log.index(logIndexLower).node_id == nodeId {
            LogRangeMatchesQueue_update_change(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        } else {
            LogRangeMatchesQueue_update_change(
                queue,
                log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_update_change_2<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    nodeId: nat,
    updates1: Map<ReqId, UpdateState<DT>>,
    updates2: Map<ReqId, UpdateState<DT>>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates1,
        ),
        forall|rid| #[trigger]
            updates1.contains_key(rid) ==> queue.contains(rid) ==> updates2.contains_key(rid)
                && updates2[rid] === updates1[rid],
    ensures
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            nodeId,
            updates2,
        ),
    decreases logIndexUpper - logIndexLower,
{
    if logIndexLower == logIndexUpper {
    } else {
        if log.index(logIndexLower).node_id == nodeId {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        } else {
            LogRangeMatchesQueue_update_change_2(
                queue,
                log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                nodeId,
                updates1,
                updates2,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id == node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed {
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue.push(new_rid),
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        }
        if new_log.index(logIndexLower).node_id != node_id {
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        }
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
            assert(LogRangeMatchesQueue(
                queue.push(new_rid),
                new_log,
                queueIndex,
                logIndexLower,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        } else {
            LogRangeMatchesQueue_append(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append_other<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    logLen: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper <= logLen,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed { op: log_entry.op, idx: logLen }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logLen, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower != logIndexUpper {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append_other(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                logLen,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        } else {
            LogRangeMatchesQueue_append_other(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                logLen,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeMatchesQueue_append_other_augment<DT: Dispatch>(
    queue: Seq<nat>,
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    queueIndex: nat,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    updates: Map<ReqId, UpdateState<DT>>,
    new_updates: Map<ReqId, UpdateState<DT>>,
    new_rid: ReqId,
    log_entry: LogEntry<DT>,
)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        new_updates.contains_key(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed {
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall|rid| #[trigger]
            updates.contains_key(rid) && rid != new_rid ==> new_updates.contains_key(rid)
                && new_updates[rid] === updates[rid],
        LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            logIndexLower,
            logIndexUpper,
            node_id,
            updates,
        ),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log.index(logIndexLower).node_id != node_id);
        assert(LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex,
            logIndexLower + 1,
            logIndexUpper + 1,
            node_id,
            new_updates,
        ));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex + 1,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
            assert(LogRangeMatchesQueue(
                queue,
                new_log,
                queueIndex,
                logIndexLower,
                logIndexUpper + 1,
                node_id,
                new_updates,
            ));
        } else {
            LogRangeMatchesQueue_append_other_augment(
                queue,
                log,
                new_log,
                queueIndex,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                updates,
                new_updates,
                new_rid,
                log_entry,
            );
        }
    }
}

proof fn LogRangeNoNodeId_append_other<DT: Dispatch>(
    log: Map<nat, LogEntry<DT>>,
    new_log: Map<nat, LogEntry<DT>>,
    logIndexLower: nat,
    logIndexUpper: nat,
    node_id: NodeId,
    log_entry: LogEntry<DT>,
)
    requires
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures
        LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),
    decreases (logIndexUpper - logIndexLower),
{
    if logIndexLower == logIndexUpper + 1 {
    } else if logIndexLower == logIndexUpper {
        assert(new_log.contains_key(logIndexLower));
        assert(new_log[logIndexLower].node_id != node_id);
        assert(LogRangeNoNodeId(new_log, logIndexLower + 1, logIndexUpper + 1, node_id));
    } else {
        assert(new_log.index(logIndexLower) === log.index(logIndexLower));
        if new_log.index(logIndexLower).node_id == node_id {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                log_entry,
            );
            assert(LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id));
        } else {
            LogRangeNoNodeId_append_other(
                log,
                new_log,
                logIndexLower + 1,
                logIndexUpper,
                node_id,
                log_entry,
            );
        }
    }
}

/// the updates below the current pointer are either in the applied or done state.
pub open spec fn QueueRidsUpdateDone<DT: Dispatch>(
    queued_ops: Seq<ReqId>,
    localUpdates: Map<ReqId, UpdateState<DT>>,
    bound: nat,
) -> bool
    recommends
        0 <= bound <= queued_ops.len(),
{
    // Note that use localUpdates.contains_key(queued_ops[j]) as a *hypothesis*
    // here. This is because the model actually allows an update to "leave early"
    // before the combiner phase completes. (This is actually an instance of our
    // model being overly permissive.)
    forall|j|
        0 <= j < bound ==> localUpdates.contains_key(#[trigger] queued_ops[j]) ==> {
            ||| localUpdates[queued_ops[j]].is_Applied()
            ||| localUpdates[queued_ops[j]].is_Done()
        }
}

/// the updates in the queue above or equal the current pointer are in placed state
pub open spec fn QueueRidsUpdatePlaced<DT: Dispatch>(
    queued_ops: Seq<ReqId>,
    localUpdates: Map<ReqId, UpdateState<DT>>,
    bound: nat,
) -> bool
    recommends
        0 <= bound <= queued_ops.len(),
{
    forall|j|
        bound <= j < queued_ops.len() ==> {
            &&& localUpdates.contains_key(#[trigger] queued_ops[j])
            &&& localUpdates[queued_ops[j]].is_Placed()
        }
}

proof fn concat_LogRangeNoNodeId_LogRangeMatchesQueue<DT: Dispatch>(
    queue: Seq<ReqId>,
    log: Map<LogIdx, LogEntry<DT>>,
    queueIndex: nat,
    a: nat,
    b: nat,
    c: nat,
    nodeId: nat,
    updates: Map<ReqId, UpdateState<DT>>,
)
    requires
        a <= b <= c,
        0 <= queueIndex <= queue.len(),
        LogRangeNoNodeId(log, a, b, nodeId),
        LogRangeMatchesQueue(queue, log, queueIndex, b, c, nodeId, updates),
    ensures
        LogRangeMatchesQueue(queue, log, queueIndex, a, c, nodeId, updates),
    decreases b - a,
{
    if a != b {
        concat_LogRangeNoNodeId_LogRangeMatchesQueue(
            queue,
            log,
            queueIndex,
            a + 1,
            b,
            c,
            nodeId,
            updates,
        );
    }
}

/// constructs the state of the data structure at a specific version given the log
///
/// This function recursively applies the update operations to the initial state of the
/// data structure and returns the state of the data structure at the given version.
pub open spec fn compute_nrstate_at_version<DT: Dispatch>(
    log: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
) -> DT::View
    recommends
        forall|i| 0 <= i < version ==> log.contains_key(i),
    decreases version,
{
    if version == 0 {
        DT::init_spec()
    } else {
        let ver = (version - 1) as nat;
        DT::dispatch_mut_spec(compute_nrstate_at_version(log, ver), log[ver].op).0
    }
}

pub proof fn compute_nrstate_at_version_preserves<DT: Dispatch>(
    a: Map<LogIdx, LogEntry<DT>>,
    b: Map<LogIdx, LogEntry<DT>>,
    version: LogIdx,
)
    requires
        forall|i| 0 <= i < version ==> a.contains_key(i),
        forall|i| 0 <= i < version ==> a[i] == b[i],
    ensures
        compute_nrstate_at_version(a, version) == compute_nrstate_at_version(b, version),
    decreases version,
{
    if version > 0 {
        compute_nrstate_at_version_preserves(a, b, (version - 1) as nat);
    }
}

} // verus!
// end verus!
