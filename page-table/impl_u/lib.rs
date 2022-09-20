#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use crate::definitions_t::aligned;
use map::*;

verus! {

#[verifier(external_body)]
pub proof fn mod_of_mul_auto() {
    ensures(forall_arith(|a: nat, b: nat| b > 0 >>= aligned(#[trigger] (a * b), b)));
}

#[verifier(external_body)]
pub proof fn mod_of_mul(a: nat, b: nat) {
    requires(b > 0);
    ensures(aligned(a * b, b));
}

#[verifier(nonlinear)]
pub proof fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

// FIXME: only valid trigger causes trigger loop
// #[verifier(external_body)]
// pub proof fn mod_add_zero_auto() {
//     ensures(forall(|a: nat, b: nat, c: nat| #[trigger] aligned(a, c) && #[trigger] aligned(b, c) && c > 0 ==> aligned(a + b, c)));
// }

#[verifier(external_body)]
pub proof fn mod_add_zero(a: nat, b: nat, c: nat) {
    requires([
        aligned(a, c),
        aligned(b, c),
        c > 0,
    ]);
    ensures(aligned(a + b, c));
}

#[verifier(external_body)]
pub proof fn subtract_mod_aligned(a: nat, b: nat) {
    requires(0 < b);
    ensures(aligned((a - (a % b)) as nat, b));
}

// FIXME: no valid triggers for this?
// #[verifier(external_body)]
// pub proof fn mod_mult_zero_implies_mod_zero_auto() {
//     ensures(forall(|a: nat, b: nat, c: nat| aligned(a, b * c) && c > 0 ==> aligned(a, b)));
// }

#[verifier(external_body)]
pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) {
    requires([
        aligned(a, b * c),
        c > 0,
    ]);
    ensures(aligned(a, b));
}

#[verifier(external_body)]
pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat) {
    requires([
             c > 0,
             aligned(a, c),
             aligned(b, c),
             a <= b,
    ]);
    ensures(aligned((b - a) as nat, c));
}

#[verifier(nonlinear)]
pub proof fn aligned_zero()
    ensures
        forall|a:nat| a != 0 ==> aligned(0, a)
{ }

#[verifier(external_body)]
pub proof fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) {
    requires([
        a > b,
        c > 0,
        aligned(b, c),
        a % c > 0,
    ]);
    ensures((a - b) % c > 0);
}

//

#[verifier(nonlinear)]
pub proof fn mul_distributive(a: nat, b: nat) {
    ensures((a + 1) * b == a * b + b);
}

#[verifier(nonlinear)]
pub proof fn mul_commute(a: nat, b: nat) {
    ensures(a * b == b * a);
}

#[verifier(nonlinear)]
pub proof fn div_mul_cancel(a: nat, b: nat) {
    requires([
             aligned(a, b),
             b != 0
    ]);
    ensures(a / b * b == a);
}

#[verifier(nonlinear)]
pub proof fn less_mul_cancel(a: nat, b: nat, c: nat) {
    requires(a * c < b * c);
    ensures(a < b);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono1(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(a * c <= b * c);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono2(a: nat, b: nat, c: nat) {
    requires(a <= b);
    ensures(c * a <= c * a);
}

#[verifier(nonlinear)]
pub proof fn mult_leq_mono_both(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b <= d,
    ensures
        // Including `0 <=` here because it's used in a place where this is part of an overflow VC
        // and non-nonlinear z3 can't even deal with that.
        0 <= a * b <= c * d;

// #[verifier(nonlinear)]
// pub proof fn mult_less_mono_both1(a: nat, b: nat, c: nat, d: nat)
//     requires
//         a < c,
//         b <= d,
//         0 < c,
//         0 < d,
//     ensures
//         a * b < c * d;

// #[verifier(nonlinear)]
// pub proof fn mult_less_mono_both2(a: nat, b: nat, c: nat, d: nat)
//     requires
//         a <= c,
//         b < d,
//         0 < c,
//         0 < d,
//     ensures
//         a * b < c * d;

// TODO: what a horrible lemma name
#[verifier(external_body)]
pub proof fn leq_add_aligned_less(a: nat, b: nat, c: nat) {
    requires([
             0 < b,
             a < c,
             aligned(a, b),
             aligned(c, b),
    ]);
    ensures(a + b <= c);
}

#[verifier(external_body)]
pub proof fn aligned_transitive_auto() {
    ensures(forall(|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) >>= aligned(a, c)));
}

#[verifier(external_body)]
pub proof fn aligned_transitive(a: nat, b: nat, c: nat) {
    requires([
             0 < b,
             0 < c,
             aligned(a, b),
             aligned(b, c),
    ]);
    ensures(aligned(a, c));
}

//// This is a collection of other lemmas in this module. Could prove each of them with an
//// assert_forall_by and the corresponding lemma but that seems tedious.
//#[proof] #[verifier(external_body)]
//pub fn kitchen_sink() {
//    ensures([
//            forall(|addr: nat, size: nat| equal(aligned(addr, size), addr % size == 0)),
//            forall_arith(|a: nat, b: nat| (b > 0) >>= aligned(#[trigger] (a * b), b)),
//            forall_arith(|a: nat, b: nat| (b != 0) >>= (#[trigger] (a % b) <= a)),
//            // bad triggers:
//            forall(|a: nat, b: nat, c: nat| (#[trigger] aligned(a, c) && #[trigger] aligned(b, c) && c > 0) >>= (aligned(a + b, c))),
//            // possibly bad trigger:
//            forall_arith(|a: nat, b: nat| (0 < b) >>= (aligned(#[trigger] (a - (a % b)), b))),
//            // TODO: is there any valid trigger here?
//            // forall(|a: nat, b: nat, c: nat| (aligned(a, b * c) && c > 0) >>= (aligned(a, b))),
//            // bad triggers:
//            forall(|a: nat, b: nat, c: nat| (c > 0 && #[trigger] aligned(a, c) && #[trigger] aligned(b, c) && a <= b) >>= (aligned(b - a, c))),
//            forall(|a: nat| (a != 0) >>= (aligned(0, a))),
//            forall_arith(|a: nat, b: nat, c: nat| (a > b && c > 0 && aligned(b, c) && #[trigger] (a % c) > 0) >>= (#[trigger] (a - b) % c > 0)),
//            // TODO: rewrite these two to a single ensures with with_triggers
//            forall_arith(|a: nat, b: nat| (a + 1) * b == #[trigger] (a * b + b)),
//            forall_arith(|a: nat, b: nat| #[trigger] ((a + 1) * b) == (a * b + b)),
//            // bad triggers:
//            forall_arith(|a: nat, b: nat| #[trigger] (a * b) == b * a),
//            forall_arith(|a: nat, b: nat| (aligned(a, b) && b != 0) >>= (#[trigger] (a / b * b) == a)),
//            forall_arith(|a: nat, b: nat, c: nat| (#[trigger] (a * c) < #[trigger] (b * c)) >>= (a < b)),
//            forall_arith(|a: nat, b: nat, c: nat| (a <= b) >>= (#[trigger] (a * c) <= #[trigger] (b * c))),
//            forall_arith(|a: nat, b: nat, c: nat| (a <= b) >>= (#[trigger] (c * a) <= #[trigger] (c * b))),
//            // forall(|a: nat, b: nat, c: nat| (0 < b && a < c && #[trigger] aligned(a, b) && #[trigger] aligned(c, b)) >>= (a + b <= c)),
//    ]);
//}

pub proof fn assert_maps_equal_contains_pair<K,V>(m1: Map<K,V>, m2: Map<K,V>)
    requires
        forall|k:K,v:V| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k:K,v:V| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2
{
    assert forall|k|
        m1.dom().contains(k)
        implies m2.dom().contains(k) by
    { assert(m2.contains_pair(k, m1.index(k))); };
    assert forall|k|
        m2.dom().contains(k)
        implies m1.dom().contains(k) by
    { assert(m1.contains_pair(k, m2.index(k))); };
    assert forall|k|
        m1.dom().contains(k) && m2.dom().contains(k)
        implies #[trigger] m2.index(k) === #[trigger] m1.index(k) by
    {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    };
    assert_maps_equal!(m1, m2);
}

}
