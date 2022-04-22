#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[macro_use]
#[allow(unused_imports)]
use crate::pervasive::*;

#[proof] #[verifier(external_body)]
pub fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[proof] #[verifier(external_body)]
pub fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}