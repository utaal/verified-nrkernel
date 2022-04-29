#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[macro_use]
#[allow(unused_imports)]
use crate::pervasive::*;

#[proof] #[verifier(non_linear)]
pub fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[proof] #[verifier(non_linear)]
pub fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}

#[proof] #[verifier(non_linear)]
pub fn div_mul_cancel(a: nat, b: nat) {
    requires([
             a % b == 0,
             b != 0
    ]);
    ensures(a / b * b == a);
}

#[proof] #[verifier(non_linear)]
pub fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[proof] #[verifier(non_linear)]
pub fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[proof] #[verifier(non_linear)]
pub fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[proof] #[verifier(non_linear)]
pub fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

#[proof] #[verifier(external_body)]
pub fn subtract_mod_aligned(a: nat, b: nat) {
    requires(0 < b);
    ensures((a - (a % b)) % b == 0);
}

#[proof] #[verifier(external_body)]
pub fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) {
    requires(a % (b * c) == 0);
    ensures(a % b == 0);
}

#[proof] #[verifier(external_body)]
pub fn subtract_mod_eq_zero(a: nat, b: nat, c: nat) {
    requires([
             a % c == 0,
             b % c == 0,
             a <= b,
    ]);
    ensures((b - a) % c == 0);
}

#[proof] #[verifier(non_linear)]
pub fn zero_mod_eq_zero(a: nat) {
    requires(a != 0);
    ensures(0 % a == 0);
}
