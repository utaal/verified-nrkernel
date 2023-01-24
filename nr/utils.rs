
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;


use super::pervasive::seq::Seq;


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

}