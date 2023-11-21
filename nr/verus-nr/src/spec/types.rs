#[allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::Dispatch;

verus! {

////////////////////////////////////////////////////////////////////////////////////////////////////
// Some Types
////////////////////////////////////////////////////////////////////////////////////////////////////

/// type of the node / replica id
pub type NodeId = nat;

/// the log index
pub type LogIdx = nat;

/// the request id
pub type ReqId = nat;

/// the id of a thread on a replica node
pub type ThreadId = nat;

pub struct LogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: NodeId,
}

/// Represents an entry in the log
///
/// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
pub struct ConcreteLogEntry<DT: Dispatch> {
    pub op: DT::WriteOperation,
    pub node_id: u64,
}

} // verus!
