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

#[proof] #[verifier(external_body)]
pub fn div_mul_cancel(a: nat, b: nat) {
    requires([
             a % b == 0,
             b != 0
    ]);
    ensures(a / b * b == a);
}

#[proof] #[verifier(external_body)]
pub fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[proof] #[verifier(external_body)]
pub fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[proof] #[verifier(external_body)]
pub fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[proof] #[verifier(external_body)]
pub fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

#[proof] #[verifier(external_body)]
pub fn subtract_mod_aligned(a: nat, b: nat) {
    requires(0 < b);
    ensures((a - (a % b)) % b == 0);
}
