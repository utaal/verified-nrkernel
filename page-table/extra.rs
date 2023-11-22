#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::definitions_t::{aligned, bit, bitmask_inc};
use vstd::map::*;


verus! {

#[verus::trusted]
mod trusted {

use vstd::prelude::*;
use crate::definitions_t::{aligned, bit, bitmask_inc};
use vstd::map::*;

pub proof fn mod_of_mul_auto() 
    ensures forall|a: nat, b: nat| b > 0 ==> aligned(#[trigger] (a * b), b),
{
    assert forall|a: nat, b: nat| b > 0 implies aligned(#[trigger] (a * b), b) by {
        mod_of_mul(a, b);
    }
}

pub proof fn mod_of_mul(a: nat, b: nat)
    requires b > 0,
    ensures aligned(a * b, b),
{
    assert((a * b) % b == 0) by (nonlinear_arith)
        requires b != 0
    {
        assume(false); // times out
    }
}

pub proof fn mod_add_zero(a: nat, b: nat, c: nat)
    requires aligned(a, c), aligned(b, c), c > 0,
    ensures aligned(a + b, c),
{
    assert((a + b) % c == 0) by (nonlinear_arith)
        requires a % c == 0 && b % c == 0 && c != 0
    {
        assume(false); // times out
    }
}

pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat)
    requires aligned(a, b * c), c > 0,
    ensures aligned(a, b),
{
    assert(a % b == 0) by (nonlinear_arith)
        requires a % (b * c) == 0 && c != 0,
    {
        // assert((a % b) * (a % c) == 0); // times out
        assume(false);
    }
}

pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat)
    requires c > 0, aligned(a, c), aligned(b, c), a <= b,
    ensures aligned((b - a) as nat, c)
{
    assert(((b - a) as nat) % c == 0) by (nonlinear_arith)
        requires c > 0 && a % c == 0 && b % c == 0 && a <= b,
    {
        assume(false); // times out
    }
}

pub proof fn leq_add_aligned_less(a: nat, b: nat, c: nat)
    requires 0 < b, a < c, aligned(a, b), aligned(c, b),
    ensures a + b <= c,
{
    assert(a + b <= c) by (nonlinear_arith)
        requires 0 < b, a < c && a % b == 0 && c % b == 0,
    {
        assume(false); // times out
    }

}

pub proof fn aligned_transitive_auto()
    ensures forall|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) ==> aligned(a, c),
{
    assert forall|a: nat, b: nat, c: nat| 0 < b && 0 < c && aligned(a, b) && aligned(b, c) implies aligned(a, c) by {
        aligned_transitive(a, b, c);
    }
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

}

pub use trusted::*;


#[verifier(nonlinear)]
pub proof fn mod_less_eq(a: nat, b: nat) {
    requires(b != 0);
    ensures(a % b <= a);
}

#[verifier(nonlinear)]
pub proof fn aligned_zero()
    ensures
        forall|a:nat| a != 0 ==> aligned(0, a)
{ }

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

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both1(a: nat, b: nat, c: nat, d: nat)
    requires
        a < c,
        b <= d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d;

#[verifier(nonlinear)]
pub proof fn mult_less_mono_both2(a: nat, b: nat, c: nat, d: nat)
    requires
        a <= c,
        b < d,
        0 < c,
        0 < d,
    ensures
        a * b < c * d;


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
