#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use crate::spec::types::{DataStructureSpec, ReturnTypeSpec};

verus! {

/*
TODO(andrea,reto): restore?
pub struct DataStructureType {
    val: u64,
}

impl DataStructureType {
    pub open spec fn interp(&self) -> DataStructureSpec {
        DataStructureSpec { u: 0 }
    }

    pub fn update(&mut self, op: UpdateOp) -> (result: ReturnType)
        ensures old(self).interp().spec_update(op) == (self.interp(), result.interp())
    {
        ReturnType { u: 0 }

    }

    pub fn read(&self, op: ReadonlyOp) -> (result: ReturnType)
        ensures self.interp().spec_read(op) == result.interp()
    {
        ReturnType { u: 0 }
    }
}

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

/// Represents the return type of the read-only operation
#[derive(PartialEq, Eq)]
pub struct ReturnType {
    pub u: u8,
}

impl Structural for ReturnType {}

impl ReturnType {
    pub open spec fn interp(&self) -> ReturnTypeSpec {
        ReturnTypeSpec { u: 0 }
    }

    pub fn clone(&self) -> (result: Self)
        ensures self == result
    {
        ReturnType { u: self.u }
    }
}
*/

}
