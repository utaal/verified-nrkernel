
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::seq::Seq;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::set::Set;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::map::Map;
#[allow(unused_imports)] // XXX: should not be needed!
use super::pervasive::arbitrary;

verus!{

pub open spec fn seq_unique<A>(seq: Seq<A>) -> bool
    // where A: PartialEq + Structural
{
    forall(|i:int, j:int| (0 <= i < seq.len() && 0 <=j < seq.len() && i != j)
            ==> seq.index(i as int) !== seq.index(j as int))
}

/// whether two sequences are disjoint, i.e., they don't have common elements
pub open spec fn seq_disjoint<A>(s: Seq<A>, t: Seq<A>) -> bool
{
   forall(|i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j))
}


pub open spec fn map_contains_value<K, V>(map: Map<K, V>, val: V) -> bool
    // where K: PartialEq + Structural
{
    exists|i: K| #[trigger] map.dom().contains(i) && map.index(i) == val
}


pub closed spec fn get_new_nat(s: Set<nat>) -> nat {
    arbitrary() // TODO
}

#[proof]
pub proof fn get_new_nat_not_in(s: Set<nat>) {
    requires(s.finite());
    ensures(!s.contains(get_new_nat(s)));
    assume(false); // TODO
}


#[verifier(nonlinear)]
pub proof fn int_mod_less_than_same(i: int, len: int)
    requires 0 <= i < len, len > 0
    ensures  (i % len) == i

{
}

// pub proof fn mod_range_not_same1(i: int, j: int)
//     requires
//       16 > 0,
//       i < j < i + 16
//     ensures
//       i % 16 != j % 16
// {
// }

// #[verifier(nonlinear)]
// pub proof fn mod_range_not_same(i: int, j: int, N: int)
//     requires
//       N > 0,
//       i < j < i + N
//     ensures
//       i % N != j % N
// {
//     let ki = i / N;
//     let kj = j / N;

//     assert(ki * N <= i < (ki + 1) * N);
//     assert(kj * N <= j < (kj + 1) * N);

//     // assert(i % N == i - ki * N);
//     // assert(j % N == j - kj * N);

//     // assert(i - ki * N != j - kj * N);
//     assert(false);
// }

}