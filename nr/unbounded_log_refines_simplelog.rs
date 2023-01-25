// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use super::pervasive::*;
use super::pervasive::seq::*;
use super::pervasive::set::*;
use super::pervasive::map::*;

use state_machines_macros::*;

use super::types::*;
use super::utils::*;
use super::unbounded_log::{UnboundedLog, ReadonlyState, UpdateState, CombinerState, LogEntry};
use super::simple_log::{SimpleLog, ReadReq as SReadReq, UpdateResp as SUpdateResp};

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Refinement Proof: UnboundedLog refines SimpleLog
// ================================================
//
// ...
//
////////////////////////////////////////////////////////////////////////////////////////////////////


verus!{

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


// #[proof]
// fn refinement(pre: UnboundedLog::State, post: UnboundedLog::State)
//     requires
//         pre.invariant(),
//         post.invariant(),
//         interp(pre).invariant(),
//         UnboundedLog::State::next_strong(pre, post),
//     ensures
//         SimpleLog::State::next(interp(pre), interp(post)),
// {
//     case_on_next_strong!{pre, post, UnboundedLog => {
//         readonly_new(op) => {
//             let rid = get_new_nat(pre.local_reads.dom());
//             assert_maps_equal!(
//                 pre.local_reads.insert(rid, ReadonlyState::Init {op}),
//                 post.local_reads
//             );
//             assert_maps_equal!(
//                 interp(pre).readonly_reqs.insert(rid, ReadReq::Init{op}),
//                 interp(post).readonly_reqs
//             );
//             SimpleLog::show::start_readonly(interp(pre), interp(post), rid, op);
//         }
//         readonly_read_ctail(rid) => {

//             assert(interp(pre).readonly_reqs.dom().contains(rid));

//             SimpleLog::show::read_ctail(interp(pre), interp(post), rid);
//         }
//         readonly_ready_to_read(rid, node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         readonly_apply(rid) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         readonly_finish(rid, op, version_upper_bound, node_id, ret) => {
//             assume(false);
//             //SimpleLog::show::finish_readonly(interp(pre), interp(post), rid, );
//         }
//         exec_trivial_start(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         advance_tail_one(node_id, rid) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_load_tail(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_load_local_head(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_load_global_head(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_dispatch_local(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_dispatch_remote(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_update_version_upper_bound(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//         exec_goto_ready(node_id) => {
//             SimpleLog::show::no_op(interp(pre), interp(post));
//         }
//     }}
// }








// proof fn concat_LogRangeNoNodeId_LogRangeMatchesQueue(
//     queue: Seq<nat>, log: Map<nat, LogEntry>,
//     queueIndex: nat, a: nat, b: nat, c: nat, nodeId: nat, updates: Map<nat, UpdateState>)
// requires
//     a <= b <= c,
//     0 <= queueIndex <= queue.len(),
//     LogRangeNoNodeId(log, a, b, nodeId),
//     LogRangeMatchesQueue(queue, log, queueIndex, b, c, nodeId, updates),
// ensures LogRangeMatchesQueue(queue, log, queueIndex, a, c, nodeId, updates)
// decreases b - a
// {
//   if a == b {
//   } else {
//     concat_LogRangeNoNodeId_LogRangeMatchesQueue(
//         queue, log, queueIndex,
//         a+1, b, c,
//         nodeId, updates);
//   }
// }

// proof fn append_LogRangeMatchesQueue(
//       queue: Seq<nat>,
//       log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
//       queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
//       updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
//       new_rid: ReqId, log_entry: LogEntry)
//     requires
//         0 <= queueIndex <= queue.len(),
//         logIndexLower <= logIndexUpper,
//         log_entry.node_id == node_id,
//         new_updates.dom().contains(new_rid),
//         new_updates.index(new_rid) === (UpdateState::Placed{
//             op: log_entry.op,
//             idx: logIndexUpper,
//         }),
//         !queue.contains(new_rid),
//         forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
//             new_updates.dom().contains(rid)
//             && new_updates.index(rid) === updates.index(rid),
//         LogRangeMatchesQueue(queue, log,
//             queueIndex, logIndexLower, logIndexUpper, node_id, updates),
//         new_log === log.insert(logIndexUpper, log_entry),

//     ensures LogRangeMatchesQueue(
//         queue.push(new_rid),
//         new_log,
//         queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

//     decreases(logIndexUpper - logIndexLower),
// {
//   if logIndexLower == logIndexUpper + 1 {
//   } else if logIndexLower == logIndexUpper {
//      assert( new_log.dom().contains(logIndexLower) );
//      if new_log.index(logIndexLower).node_id == node_id {
//         assert( queueIndex < queue.push(new_rid).len());
//         assert( new_updates.dom().contains(queue.push(new_rid).index(queueIndex as int)));
//         assert( new_updates.index(queue.push(new_rid).index(queueIndex as int)).is_Placed());
//         assert( new_updates.index(queue.push(new_rid).index(queueIndex as int)).get_Placed_idx() == logIndexLower);
//         assert( LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex+1, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
//       }
//       if new_log.index(logIndexLower).node_id != node_id {
//         assert(LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
//       }
//   } else {
//     assert(new_log.index(logIndexLower) === log.index(logIndexLower));
//     if new_log.index(logIndexLower).node_id == node_id {
//         append_LogRangeMatchesQueue(queue, log, new_log, queueIndex + 1,
//             logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);

//         /*assert( queueIndex < queue.push(new_rid).len());

//         assert( updates.dom().contains(queue.index(queueIndex)));
//         let q = queue.push(new_rid).index(queueIndex);
//         assert( updates.dom().contains(q));
//         assert(q != new_rid);
//         assert( new_updates.dom().contains(q));

//         assert( new_updates.index(queue.push(new_rid).index(queueIndex)).is_Placed());
//         assert( new_updates.index(queue.push(new_rid).index(queueIndex)).get_Placed_idx() == logIndexLower);
//         assert( LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex+1, logIndexLower+1, logIndexUpper+1, node_id, new_updates));*/

//         assert(LogRangeMatchesQueue(
//             queue.push(new_rid),
//             new_log,
//             queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
//     } else {
//       append_LogRangeMatchesQueue(queue, log, new_log, queueIndex,
//         logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
//         /*assert (log.index(logIndexLower).node_id != node_id ==>
//           LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower+1, logIndexUpper, node_id, updates)
//         );
//         assert (new_log.index(logIndexLower).node_id != node_id ==>
//           LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates)
//         );
//         return;*/
//     }
//   }
// }

// proof fn append_LogRangeMatchesQueue_other_augment(
//       queue: Seq<nat>,
//       log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
//       queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
//       updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
//       new_rid: ReqId, log_entry: LogEntry)
//     requires
//         0 <= queueIndex <= queue.len(),
//         logIndexLower <= logIndexUpper,
//         log_entry.node_id != node_id,
//         new_updates.dom().contains(new_rid),
//         new_updates.index(new_rid) === (UpdateState::Placed{
//             op: log_entry.op,
//             idx: logIndexUpper,
//         }),
//         !queue.contains(new_rid),
//         forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
//             new_updates.dom().contains(rid)
//             && new_updates.index(rid) === updates.index(rid),
//         LogRangeMatchesQueue(queue, log,
//             queueIndex, logIndexLower, logIndexUpper, node_id, updates),
//         new_log === log.insert(logIndexUpper, log_entry),

//     ensures LogRangeMatchesQueue(
//         queue,
//         new_log,
//         queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

//     decreases(logIndexUpper - logIndexLower),
// {
//   if logIndexLower == logIndexUpper + 1 {
//   } else if logIndexLower == logIndexUpper {
//      assert( new_log.dom().contains(logIndexLower) );
//      assert(new_log.index(logIndexLower).node_id != node_id);
//      assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
//   } else {
//     assert(new_log.index(logIndexLower) === log.index(logIndexLower));
//     if new_log.index(logIndexLower).node_id == node_id {
//         append_LogRangeMatchesQueue_other_augment(queue, log, new_log, queueIndex + 1,
//             logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);

//         assert(LogRangeMatchesQueue(
//             queue,
//             new_log,
//             queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
//     } else {
//       append_LogRangeMatchesQueue_other_augment(queue, log, new_log, queueIndex,
//         logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
//     }
//   }
// }

// proof fn append_LogRangeMatchesQueue_other(
//       queue: Seq<nat>,
//       log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
//       queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, logLen: nat, node_id: NodeId,
//       updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
//       new_rid: ReqId, log_entry: LogEntry)
//     requires
//         0 <= queueIndex <= queue.len(),
//         logIndexLower <= logIndexUpper <= logLen,
//         log_entry.node_id != node_id,
//         new_updates.dom().contains(new_rid),
//         new_updates.index(new_rid) === (UpdateState::Placed{
//             op: log_entry.op,
//             idx: logLen,
//         }),
//         !queue.contains(new_rid),
//         forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
//             new_updates.dom().contains(rid)
//             && new_updates.index(rid) === updates.index(rid),
//         LogRangeMatchesQueue(queue, log,
//             queueIndex, logIndexLower, logIndexUpper, node_id, updates),
//         new_log === log.insert(logLen, log_entry),

//     ensures LogRangeMatchesQueue(
//         queue,
//         new_log,
//         queueIndex, logIndexLower, logIndexUpper, node_id, new_updates),

//     decreases(logIndexUpper - logIndexLower),
// {
//   if logIndexLower == logIndexUpper {
//      //assert( new_log.dom().contains(logIndexLower) );
//      //assert(new_log.index(logIndexLower).node_id != node_id);
//      //assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
//   } else {
//     assert(new_log.index(logIndexLower) === log.index(logIndexLower));
//     if new_log.index(logIndexLower).node_id == node_id {
//         append_LogRangeMatchesQueue_other(queue, log, new_log, queueIndex + 1,
//             logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
//     } else {
//       append_LogRangeMatchesQueue_other(queue, log, new_log, queueIndex,
//         logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
//     }
//   }
// }

// proof fn append_LogRangeNoNodeId_other(
//       log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
//       logIndexLower: nat, logIndexUpper: nat, node_id: NodeId,
//       log_entry: LogEntry)
//     requires
//         logIndexLower <= logIndexUpper,
//         log_entry.node_id != node_id,
//         LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
//         new_log === log.insert(logIndexUpper, log_entry),
//     ensures LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),

//     decreases(logIndexUpper - logIndexLower),
// {
//   if logIndexLower == logIndexUpper + 1 {
//   } else if logIndexLower == logIndexUpper {
//      assert( new_log.dom().contains(logIndexLower) );
//      assert(new_log.index(logIndexLower).node_id != node_id);
//      assert(LogRangeNoNodeId(new_log, logIndexLower+1, logIndexUpper+1, node_id));
//   } else {
//     assert(new_log.index(logIndexLower) === log.index(logIndexLower));
//     if new_log.index(logIndexLower).node_id == node_id {
//         append_LogRangeNoNodeId_other(log, new_log,
//             logIndexLower + 1, logIndexUpper, node_id, log_entry);

//         assert(LogRangeNoNodeId(
//             new_log,
//             logIndexLower, logIndexUpper + 1, node_id));
//     } else {
//       append_LogRangeNoNodeId_other(log, new_log,
//         logIndexLower + 1, logIndexUpper, node_id, log_entry);
//     }
//   }
// }



// proof fn LogRangeMatchesQueue_update_change(queue: Seq<nat>, log: Map<nat, LogEntry>,
//     queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
//     updates1: Map<nat, UpdateState>,
//     updates2: Map<nat, UpdateState>)
// requires
//     0 <= queueIndex <= queue.len(),
//     logIndexLower <= logIndexUpper,
//     LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
//     forall |rid| #[trigger] updates1.dom().contains(rid) ==>
//       updates1.index(rid).is_Placed() && logIndexLower <= updates1.index(rid).get_Placed_idx() < logIndexUpper ==>
//           updates2.dom().contains(rid) && updates2.index(rid) === updates1.index(rid),
// ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2)
// decreases logIndexUpper - logIndexLower
// {
//   if logIndexLower == logIndexUpper {
//   } else {
//     if log.index(logIndexLower).node_id == nodeId {
//       LogRangeMatchesQueue_update_change(queue, log, queueIndex + 1,
//         logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
//     } else {
//       LogRangeMatchesQueue_update_change(queue, log, queueIndex,
//         logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
//     }
//   }
// }

// proof fn LogRangeMatchesQueue_update_change_2(queue: Seq<nat>, log: Map<nat, LogEntry>,
//     queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
//     updates1: Map<nat, UpdateState>,
//     updates2: Map<nat, UpdateState>)
// requires
//     0 <= queueIndex <= queue.len(),
//     logIndexLower <= logIndexUpper,
//     LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
//     forall |rid| #[trigger] updates1.dom().contains(rid) ==> queue.contains(rid) ==>
//           updates2.dom().contains(rid) && updates2.index(rid) === updates1.index(rid),
// ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2),
// decreases logIndexUpper - logIndexLower,
// {
//   if logIndexLower == logIndexUpper {
//   } else {
//     if log.index(logIndexLower).node_id == nodeId {
//       LogRangeMatchesQueue_update_change_2(queue, log, queueIndex + 1,
//         logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
//     } else {
//       LogRangeMatchesQueue_update_change_2(queue, log, queueIndex,
//         logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
//     }
//   }
// }







// pub open spec fn seq_unique<V>(rids: Seq<V>) -> bool {
//   forall |i, j| 0 <= i < rids.len() && 0 <= j < rids.len() && i != j ==>
//       rids.index(i) !== rids.index(j)
// }








} // end verus!