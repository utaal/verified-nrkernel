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
    pub val: u64,
}

impl DataStructureSpec {

    #[verifier(opaque)]
    pub open spec fn init() -> Self {
        DataStructureSpec { val: 0 }
    }

    /// reads the current state of the replica
    #[verifier(opaque)]
    pub open spec fn spec_read(&self, op: ReadonlyOp) -> ReturnType {
        ReturnType::Value(0)
    }

    #[verifier(opaque)]
    pub open spec fn spec_update(self, op: UpdateOp) -> (Self, ReturnType) {
        (self, ReturnType::Ok)
    }
}

pub struct DataStructureType {
    pub val: u64,
}

impl DataStructureType {
    pub open spec fn interp(&self) -> DataStructureSpec {
        DataStructureSpec { val: self.val }
    }

    pub fn update(&mut self, op: UpdateOp) -> (result: ReturnType)
        ensures old(self).interp().spec_update(op) == (self.interp(), result)
    {
        match op {
            UpdateOp::Reset => self.val = 0,
            UpdateOp::Inc => self.val = self.val + 1,
        }
        ReturnType::Ok
    }

    pub fn read(&self, op: ReadonlyOp) -> (result: ReturnType)
        ensures self.interp().spec_read(op) == result
    {
        ReturnType::Value(self.val)
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
pub enum UpdateOp {
    Reset,
    Inc,
}

impl UpdateOp {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        match self {
            UpdateOp::Reset => UpdateOp::Reset,
            UpdateOp::Inc => UpdateOp::Inc,
        }
    }
}

/// Represents a read-only operation on the replica, in NR this is handled by `dispatch`
pub enum ReadonlyOp {
    Get,
}

/// the operations enum
pub enum Request {
    Update(UpdateOp),
    Readonly(ReadonlyOp),
}

/// Represents the return type of the read-only operation
#[derive(PartialEq, Eq)]
pub enum ReturnType {
    Value(u64),
    Ok,
}

impl Structural for ReturnType {}

impl ReturnType {
    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        match self {
            ReturnType::Value(v) => ReturnType::Value(*v),
            ReturnType::Ok => ReturnType::Ok,
        }
    }
}

pub struct LogEntry {
    pub op: UpdateOp,
    pub node_id: NodeId,
}


/// Represents an entry in the log
///
/// datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)
pub struct ConcreteLogEntry {
    pub op: UpdateOp,
    pub node_id: u64,
}


} // verus!
