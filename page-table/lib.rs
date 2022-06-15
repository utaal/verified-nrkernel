#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[macro_use]
#[allow(unused_imports)]
use crate::pervasive::*;

// mod

#[spec(checked)]
pub fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

#[proof]
pub fn aligned_def() {
    ensures(forall(|addr: nat, size: nat| equal(aligned(addr, size), addr % size == 0)));
}

#[proof] #[verifier(external_body)]
pub fn mod_of_mul_auto() {
    ensures(forall_arith(|a: nat, b: nat| b > 0 >>= aligned(#[trigger] (a * b), b)));
}

#[proof] #[verifier(external_body)]
pub fn mod_of_mul(a: nat, b: nat) {
    requires(b > 0);
    ensures(aligned(a * b, b));
}

#[proof] #[verifier(nonlinear)]
pub fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[proof] #[verifier(external_body)]
pub fn mod_add_zero(a: nat, b: nat, c: nat) {
    requires([
        aligned(a, c),
        aligned(b, c),
        c > 0,
    ]);
    ensures(aligned(a + b, c));
}

#[proof] #[verifier(external_body)]
pub fn subtract_mod_aligned(a: nat, b: nat) {
    requires(0 < b);
    ensures(aligned(a - (a % b), b));
}

#[proof] #[verifier(external_body)]
pub fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) {
    requires([
        aligned(a, b * c),
        c > 0,
    ]);
    ensures(aligned(a, b));
}

#[proof] #[verifier(external_body)]
pub fn subtract_mod_eq_zero(a: nat, b: nat, c: nat) {
    requires([
             c > 0,
             aligned(a, c),
             aligned(b, c),
             a <= b,
    ]);
    ensures(aligned(b - a, c));
}

#[proof] #[verifier(nonlinear)]
pub fn zero_mod_eq_zero(a: nat) {
    requires(a != 0);
    ensures(aligned(0, a));
}

#[proof] #[verifier(external_body)]
pub fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) {
    requires([
        a > b,
        c > 0,
        aligned(b, c),
        a % c > 0,
    ]);
    ensures((a - b) % c > 0);
}

//

#[proof] #[verifier(nonlinear)]
pub fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[proof] #[verifier(nonlinear)]
pub fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}

#[proof] #[verifier(nonlinear)]
pub fn div_mul_cancel(a: nat, b: nat) {
    requires([
             aligned(a, b),
             b != 0
    ]);
    ensures(a / b * b == a);
}

#[proof] #[verifier(nonlinear)]
pub fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[proof] #[verifier(nonlinear)]
pub fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[proof] #[verifier(nonlinear)]
pub fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

// TODO: what a horrible lemma name
#[proof] #[verifier(external_body)]
pub fn leq_add_aligned_less(a: nat, b: nat, c: nat) {
    requires([
             0 < b,
             a < c,
             aligned(a, b),
             aligned(c, b),
    ]);
    ensures(a + b <= c);
}

#[proof] #[verifier(external_body)]
pub fn aligned_transitive_auto() {
    ensures(forall(|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) >>= aligned(a, c)));
}

#[proof] #[verifier(external_body)]
pub fn aligned_transitive(a: nat, b: nat, c: nat) {
    requires([
             0 < b,
             0 < c,
             aligned(a, b),
             aligned(b, c),
    ]);
    ensures(aligned(a, c));
}

// This is a collection of other lemmas in this module. Could prove each of them with an
// assert_forall_by and the corresponding lemma but that seems tedious.
#[proof] #[verifier(external_body)]
pub fn kitchen_sink() {
    ensures([
            forall(|addr: nat, size: nat| equal(aligned(addr, size), addr % size == 0)),
            forall_arith(|a: nat, b: nat| (b > 0) >>= aligned(#[trigger] (a * b), b)),
            forall_arith(|a: nat, b: nat| (b != 0) >>= (#[trigger] (a % b) <= a)),
            // bad triggers:
            forall(|a: nat, b: nat, c: nat| (#[trigger] aligned(a, c) && #[trigger] aligned(b, c) && c > 0) >>= (aligned(a + b, c))),
            // possibly bad trigger:
            forall_arith(|a: nat, b: nat| (0 < b) >>= (aligned(#[trigger] (a - (a % b)), b))),
            // TODO: is there any valid trigger here?
            // forall(|a: nat, b: nat, c: nat| (aligned(a, b * c) && c > 0) >>= (aligned(a, b))),
            // bad triggers:
            forall(|a: nat, b: nat, c: nat| (c > 0 && #[trigger] aligned(a, c) && #[trigger] aligned(b, c) && a <= b) >>= (aligned(b - a, c))),
            forall(|a: nat| (a != 0) >>= (aligned(0, a))),
            forall_arith(|a: nat, b: nat, c: nat| (a > b && c > 0 && aligned(b, c) && #[trigger] (a % c) > 0) >>= (#[trigger] (a - b) % c > 0)),
            // TODO: rewrite these two to a single ensures with with_triggers
            forall_arith(|a: nat, b: nat| (a + 1) * b == #[trigger] (a * b + b)),
            forall_arith(|a: nat, b: nat| #[trigger] ((a + 1) * b) == (a * b + b)),
            // bad triggers:
            forall_arith(|a: nat, b: nat| #[trigger] (a * b) == b * a),
            forall_arith(|a: nat, b: nat| (aligned(a, b) && b != 0) >>= (#[trigger] (a / b * b) == a)),
            forall_arith(|a: nat, b: nat, c: nat| (#[trigger] (a * c) < #[trigger] (b * c)) >>= (a < b)),
            forall_arith(|a: nat, b: nat, c: nat| (a <= b) >>= (#[trigger] (a * c) <= #[trigger] (b * c))),
            forall_arith(|a: nat, b: nat, c: nat| (a <= b) >>= (#[trigger] (c * a) <= #[trigger] (c * b))),
            // forall(|a: nat, b: nat, c: nat| (0 < b && a < c && #[trigger] aligned(a, b) && #[trigger] aligned(c, b)) >>= (a + b <= c)),
    ]);
}
