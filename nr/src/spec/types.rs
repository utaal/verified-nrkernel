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
pub struct DataStructureSpec {
    pub u: u8,
}

impl DataStructureSpec {

    #[verifier(opaque)]
    pub open spec fn init() -> Self {
        DataStructureSpec { u: 0 }
    }

    /// reads the current state of the replica
    #[verifier(opaque)]
    pub open spec fn spec_read(&self, op: ReadonlyOp) -> ReturnType {
        ReturnType { u: 0 }
    }

    #[verifier(opaque)]
    pub open spec fn spec_update(self, op: UpdateOp) -> (Self, ReturnType) {
        (self, ReturnType { u: 0 })
    }
}

pub struct DataStructureType {
    u: u8,
}

impl DataStructureType {
    pub open spec fn interp(&self) -> DataStructureSpec {
        DataStructureSpec { u: 0 }
    }

    pub fn update(&mut self, op: UpdateOp) -> (result: ReturnType)
        ensures old(self).interp().spec_update(op) == (self.interp(), result)
    {
        ReturnType { u: 0 }

    }

    pub fn read(&self, op: ReadonlyOp) -> (result: ReturnType)
        ensures self.interp().spec_read(op) == result
    {
        ReturnType { u: 0 }
    }
}


// #[spec]
// #[verifier(opaque)]
// pub fn read(state: DataStructureSpec, op: ReadonlyOp) -> ReturnType {
//     ReturnType { u: 0 }
// }

// #[spec]
// #[verifier(opaque)]
// pub fn update_state(state: DataStructureSpec, op: UpdateOp) -> (DataStructureSpec, ReturnType) {
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

impl ReturnType {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        ReturnType { u: self.u }
    }
}

/// Represents an entry in the log
///
/// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
pub struct LogEntry {
    pub op: UpdateOp,
    pub node_id: NodeId,
}

} // verus!
