
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

#[allow(unused_imports)]
use super::pervasive::seq::Seq;
#[allow(unused_imports)]
use super::pervasive::set::Set;
use super::pervasive::arbitrary;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Obtaining A new
////////////////////////////////////////////////////////////////////////////////////////////////////



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




pub closed spec fn get_new_nat(s: Set<nat>) -> nat {
    arbitrary() // TODO
}

#[proof]
pub proof fn get_new_nat_not_in(s: Set<nat>) {
    requires(s.finite());
    ensures(!s.contains(get_new_nat(s)));
    assume(false); // TODO
}

}