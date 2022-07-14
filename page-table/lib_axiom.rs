use vec::*;
#[allow(unused_imports)]
use builtin::*;
use crate::pervasive::*;
#[allow(unused_imports)]
use seq::*;

use std::convert::TryInto;

// FIXME: figure out how to write tests for these and then write some tests

#[verifier(external_body)]
pub fn u64_from_le_bytes(bytes: Vec<u8>) -> u64 {
    requires(bytes.len() == 8);
    ensures(|r: u64| r == u64_from_le_bytes_spec(bytes.view()));
    // FIXME: make sure this unwrap is safe
    u64::from_le_bytes(bytes.vec.try_into().unwrap())
}

#[verifier(external_body)]
pub fn u64_to_le_bytes(u: u64) -> Vec<u8> {
    ensures(|r: Vec<u8>|[
            r.len() == 8,
            equal(r.view(), u64_to_le_bytes_spec(u)),
    ]);
    Vec { vec: u64::to_le_bytes(u).to_vec() }
}

#[spec]
pub fn u64_from_le_bytes_spec(bytes: Seq<u8>) -> u64 {
    recommends(bytes.len() == 8);
    arbitrary()
}

#[spec]
pub fn u64_to_le_bytes_spec(u: u64) -> Seq<u8> {
    arbitrary()
}

// FIXME: Axiomatizing this for now, probably should implement it. But I can't implement it like
// the exec versions. What's the best way to do it?
#[proof] #[verifier(external_body)]
pub fn axiom_u64_from_le_bytes() {
    ensures([
            forall(|u: u64| #[auto_trigger] u64_to_le_bytes_spec(u).len() == 8),
            forall(|u: u64| #[trigger] u64_from_le_bytes_spec(u64_to_le_bytes_spec(u)) == u),
            forall(|bytes: Seq<u8>| bytes.len() == 8 >>= equal(#[trigger] u64_to_le_bytes_spec(u64_from_le_bytes_spec(bytes)), bytes)),
    ]);
}
