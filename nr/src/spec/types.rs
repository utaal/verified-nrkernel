#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Nr State and its operations
////////////////////////////////////////////////////////////////////////////////////////////////////

// the following types are currently arbitrary, the depend on the the actual data structure that
// each replica wraps. The NR crate has this basically as a trait that the data structure must
// implement.

/// represents a replica state
pub struct NRState {
    pub u: u8,
}

impl NRState {

    #[verifier(opaque)]
    pub open spec fn init() -> Self {
        NRState { u: 0 }
    }

    /// reads the current state of the replica
    #[verifier(opaque)]
    pub open spec fn read(&self, op: ReadonlyOp) -> ReturnType {
        ReturnType { u: 0 }
    }

    #[verifier(opaque)]
    pub open spec fn update(self, op: UpdateOp) -> (Self, ReturnType) {
        (self, ReturnType { u: 0 })
    }
}

// #[spec]
// #[verifier(opaque)]
// pub fn read(state: NRState, op: ReadonlyOp) -> ReturnType {
//     ReturnType { u: 0 }
// }

// #[spec]
// #[verifier(opaque)]
// pub fn update_state(state: NRState, op: UpdateOp) -> (NRState, ReturnType) {
//     (state, ReturnType { u: 0 })
// }


/// represents a update operation on the replica, in NR this is handled by `dispatch_mut`
pub struct UpdateOp {
    u: u8,
}

impl UpdateOp {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        UpdateOp { u: self.u }
    }
}

/// Represents a read-only operation on the replica, in NR this is handled by `dispatch`
pub struct ReadonlyOp {
    u: u8,
}

/// the operations enum
pub enum Request {
    Update(UpdateOp),
    Readonly(ReadonlyOp),
}

/// Represents the return type of the read-only operation
#[derive(PartialEq, Eq)]
pub struct ReturnType {
    pub u: u8,
}

impl Structural for ReturnType {}

/// Represents an entry in the log
///
/// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
pub struct LogEntry {
    pub op: UpdateOp,
    pub node_id: NodeId,
}

} // verus!
