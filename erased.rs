#![feature(nonnull_slice_from_raw_parts)]
#[prelude_import]
use std::prelude::rust_2018::*;
#[macro_use]
extern crate std;
extern crate alloc;

pub mod pervasive {

    pub mod map {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::set::*;
        #[doc = " `Map<K, V>` is an abstract map type for specifications."]
        #[doc =
          " To use a \"map\" in compiled code, use an `exec` type like HashMap (TODO)"]
        #[doc = " that has a `Map<K, V>` as its specification type."]
        #[doc = ""]
        #[doc =
          " An object `map: Map<K, V>` has a _domain_, a set of keys given by [`map.dom()`](Map::dom),"]
        #[doc =
          " and a mapping for keys in the domain to values, given by [`map[key]`](Map::index)."]
        #[doc =
          " Alternatively, a map can be thought of as a set of `(K, V)` pairs where each key"]
        #[doc = " appears in at most entry."]
        #[doc = ""]
        #[doc = " In general, a map might be infinite."]
        #[doc =
          " To work specifically with finite maps, see the [`self.finite()`](Set::finite) predicate."]
        #[doc = ""]
        #[doc = " Maps can be constructed in a few different ways:"]
        #[doc = "  * [`Map::empty()`] constructs an empty map."]
        #[doc =
          "  * [`Map::new`] and [`Map::total`] construct a map given functions that specify its domain and the mapping"]
        #[doc = "     from keys to values (a _map comprehension_)."]
        #[doc =
          "  * The [`map!`] macro, to construct small maps of a fixed size."]
        #[doc =
          "  * By manipulating an existing map with [`Map::insert`] or [`Map::remove`]."]
        #[doc = ""]
        #[doc =
          " To prove that two maps are equal, it is usually easiest to use the [`assert_maps_equal!`] macro."]
        #[verifier(external_body)]
        #[proof]
        pub struct Map<#[verifier(maybe_negative)] K,
                       #[verifier(strictly_positive)] V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }
        impl <K, V> Map<K, V> { }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! map_internal {
            [$($key : expr => $value : expr), * $(,) ?] =>
            {
                $crate :: pervasive :: map :: Map :: empty()
                $(.insert($key, $value)) *
            }
        }
        #[doc =
          " Create a map using syntax like `map![key1 => val1, key2 => val, ...]`."]
        #[doc = ""]
        #[doc =
          " This is equivalent to `Map::empty().insert(key1, val1).insert(key2, val2)...`."]
        #[doc = ""]
        #[doc =
          " Note that this does _not_ require all keys to be distinct. In the case that two"]
        #[doc =
          " or more keys are equal, the resulting map uses the value of the rightmost entry."]
        #[macro_export]
        macro_rules! map {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: map :: map_internal! ($($tail) *))
            } ;
        }
        pub use map_internal;
        pub use map;
        #[doc = " Prove two maps equal by _extensionality_. Usage is:"]
        #[doc = ""]
        #[doc = " ```rust"]
        #[doc = " assert_maps_equal!(map1, map2);"]
        #[doc = " ```"]
        #[doc = " "]
        #[doc = " or,"]
        #[doc = " "]
        #[doc = " ```rust"]
        #[doc = " assert_maps_equal!(map1, map2, k: Key => {"]
        #[doc =
          "     // proof goes here that `map1` and `map2` agree on key `k`,"]
        #[doc =
          "     // i.e., `k` is in the domain of `map`` iff it is in the domain of `map2`"]
        #[doc = "     // and if so, then their values agree."]
        #[doc = " });"]
        #[doc = " ```"]
        #[macro_export]
        macro_rules! assert_maps_equal {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: map :: assert_maps_equal_internal!
                 ($($tail) *))
            } ;
        }
        #[macro_export]
        #[doc(hidden)]
        macro_rules! assert_maps_equal_internal {
            ($m1 : expr, $m2 : expr $(,) ?) =>
            { assert_maps_equal_internal! ($m1, $m2, key => { }) } ;
            ($m1 : expr, $m2 : expr, $k : ident $(: $t : ty) ? => $bblock :
             block) =>
            {
                #[spec] let m1 = $crate :: pervasive :: map ::
                check_argument_is_map($m1) ; #[spec] let m2 = $crate ::
                pervasive :: map :: check_argument_is_map($m2) ; :: builtin ::
                assert_by(:: builtin :: equal(m1, m2),
                          {
                              :: builtin ::
                              assert_forall_by(| $k $(: $t) ? |
                                               {
                                                   :: builtin ::
                                                   ensures([:: builtin ::
                                                            imply(#[trigger]
                                                                  m1.dom().contains($k),
                                                                  m2.dom().contains($k))
                                                            && :: builtin ::
                                                            imply(m2.dom().contains($k),
                                                                  m1.dom().contains($k))
                                                            && :: builtin ::
                                                            imply(m1.dom().contains($k)
                                                                  &&
                                                                  m2.dom().contains($k),
                                                                  :: builtin
                                                                  ::
                                                                  equal(m1.index($k),
                                                                        m2.index($k)))])
                                                   ; { $bblock }
                                               }) ; $crate :: pervasive ::
                              assert(m1.ext_equal(m2)) ;
                          }) ;
            }
        }
        pub use assert_maps_equal_internal;
        pub use assert_maps_equal;
    }
    pub mod option {
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        pub enum Option<A> { None, Some(A), }
        #[automatically_derived]
        impl <A> Option<A> { }
        impl <A> Option<A> { }
    }
    pub mod result {
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        pub enum Result<T, E> { Ok(T), Err(E), }
        #[automatically_derived]
        impl <T, E> Result<T, E> { }
    }
    pub mod vec {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::seq::*;
        #[verifier(external_body)]
        pub struct Vec<#[verifier(strictly_positive)] A> {
            pub vec: std::vec::Vec<A>,
        }
        impl <A> Vec<A> {
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn new() -> Self { Vec{vec: std::vec::Vec::new(),} }
            #[verifier(verus_macro)]
            pub fn empty() -> Self { Vec::new() }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn push(&mut self, value: A) { self.vec.push(value); }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn pop(&mut self) -> A {
                unsafe { self.vec.pop().unwrap_unchecked() }
            }
            #[verifier(external_body)]
            #[verifier(autoview)]
            #[verifier(verus_macro)]
            pub fn index(&self, i: usize) -> &A { &self.vec[i] }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn set(&mut self, i: usize, a: A) { self.vec[i] = a; }
            #[verifier(external_body)]
            #[verifier(when_used_as_spec(spec_len))]
            #[verifier(autoview)]
            #[verifier(verus_macro)]
            pub fn len(&self) -> usize { self.vec.len() }
        }
    }
    pub mod seq {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[doc = " `Seq<A>` is a sequence type for specifications."]
        #[doc =
          " To use a \"sequence\" in compiled code, use an `exec` type like [`vec::Vec`]"]
        #[doc = " that has `Seq<A>` as its specification type."]
        #[doc = ""]
        #[doc =
          " An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),"]
        #[doc =
          " and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index)."]
        #[doc = ""]
        #[doc = " Sequences can be constructed in a few different ways:"]
        #[doc =
          "  * [`Seq::empty`] construct an empty sequence (`len() == 0`)"]
        #[doc =
          "  * [`Seq::new`] construct a sequence of a given length, initialized according"]
        #[doc = "     to a given function mapping indices `i` to values `A`."]
        #[doc =
          "  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the"]
        #[doc = "     [`std::vec!`] macro)."]
        #[doc =
          "  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],"]
        #[doc = "    or [`Seq::add`]."]
        #[doc = ""]
        #[doc =
          " To prove that two sequences are equal, it is usually easiest to use the [`assert_seqs_equal!`] macro."]
        #[verifier(external_body)]
        pub struct Seq<#[verifier(strictly_positive)] A> {
            dummy: std::marker::PhantomData<A>,
        }
        impl <A> Seq<A> { }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! seq_internal {
            [$($elem : expr), * $(,) ?] =>
            { $crate :: pervasive :: seq :: Seq :: empty() $(.push($elem)) * }
        }
        #[doc = " Creates a [`Seq`] containing the given elements."]
        #[doc = ""]
        #[doc = " ## Example"]
        #[doc = ""]
        #[doc = " ```rust"]
        #[doc = " let s = seq![11, 12, 13];"]
        #[doc = ""]
        #[doc = " assert(s.len() == 3);"]
        #[doc = " assert(s[0] == 11);"]
        #[doc = " assert(s[1] == 12);"]
        #[doc = " assert(s[2] == 13);"]
        #[doc = " ```"]
        #[macro_export]
        macro_rules! seq {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: seq :: seq_internal! ($($tail) *))
            } ;
        }
        pub use seq_internal;
        pub use seq;
    }
    pub mod seq_lib {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::seq::*;
        impl <A> Seq<A> { }
        #[doc =
          " Prove two sequences `s1` and `s2` are equal by proving that their elements are equal at each index."]
        #[doc = ""]
        #[doc = " More precisely, `assert_seqs_equal!` requires:"]
        #[doc =
          "  * `s1` and `s2` have the same length (`s1.len() == s2.len()`), and"]
        #[doc =
          "  * for all `i` in the range `0 <= i < s1.len()`, we have `s1[i] === s2[i]`."]
        #[doc = ""]
        #[doc =
          " The property that equality follows from these facts is often called _extensionality_."]
        #[doc = ""]
        #[doc = " `assert_seqs_equal!` can handle many trivial-looking"]
        #[doc = " identities without any additional help:"]
        #[doc = ""]
        #[doc = " ```rust"]
        #[doc = " #[proof]"]
        #[doc = " fn subrange_concat(s: Seq<u64>, i: int) {"]
        #[doc = "     requires(["]
        #[doc = "         0 <= i && i <= s.len(),"]
        #[doc = "     ]);"]
        #[doc = " "]
        #[doc = "     let t1 = s.subrange(0, i);"]
        #[doc = "     let t2 = s.subrange(i, s.len());"]
        #[doc = "     let t = t1.add(t2);"]
        #[doc = " "]
        #[doc = "     assert_seqs_equal!(s, t);"]
        #[doc = " "]
        #[doc = "     assert(equal(s, t));"]
        #[doc = " }"]
        #[doc = " ```"]
        #[doc = ""]
        #[doc =
          " In more complex cases, a proof may be required for the equality of each element pair."]
        #[doc = " For example,"]
        #[doc = " "]
        #[doc = " ```rust"]
        #[doc = " #[proof] fn bitvector_seqs() {"]
        #[doc = "     let s = Seq::<u64>::new(5, |i| i as u64);"]
        #[doc = "     let t = Seq::<u64>::new(5, |i| i as u64 | 0);"]
        #[doc = " "]
        #[doc = "     assert_seqs_equal!(s, t, i => {"]
        #[doc = "         // Need to show that s[i] == t[i]"]
        #[doc =
          "         // Prove that the elements are equal by appealing to a bitvector solver:"]
        #[doc = "         let j = i as u64;"]
        #[doc = "         assert_bit_vector(j | 0 == j);"]
        #[doc = "         assert(s[i] == t[i]);"]
        #[doc = "     });"]
        #[doc = " }"]
        #[doc = " ```"]
        #[macro_export]
        macro_rules! assert_seqs_equal {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: seq_lib :: assert_seqs_equal_internal!
                 ($($tail) *))
            } ;
        }
        #[macro_export]
        #[doc(hidden)]
        macro_rules! assert_seqs_equal_internal {
            ($s1 : expr, $s2 : expr $(,) ?) =>
            { assert_seqs_equal_internal! ($s1, $s2, idx => { }) } ;
            ($s1 : expr, $s2 : expr, $idx : ident => $bblock : block) =>
            {
                let s1 = $crate :: pervasive :: seq_lib ::
                check_argument_is_seq($s1) ; let s2 = $crate :: pervasive ::
                seq_lib :: check_argument_is_seq($s2) ; :: builtin ::
                assert_by(:: builtin :: equal(s1, s2),
                          {
                              $crate :: pervasive ::
                              assert(s1.len() == s2.len()) ; :: builtin ::
                              assert_forall_by(| $idx : :: builtin :: int |
                                               {
                                                   :: builtin ::
                                                   requires(0 <= $idx && $idx
                                                            < s1.len()) ; ::
                                                   builtin ::
                                                   ensures(:: builtin ::
                                                           equal(s1.index($idx),
                                                                 s2.index($idx)))
                                                   ; { $bblock }
                                               }) ; $crate :: pervasive ::
                              assert(s1.ext_equal(s2)) ;
                          }) ;
            }
        }
        pub use assert_seqs_equal_internal;
        pub use assert_seqs_equal;
    }
    pub mod set {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::map::*;
        #[doc = " `Set<A>` is a set type for specifications."]
        #[doc = ""]
        #[doc =
          " An object `set: Set<A>` is a subset of the set of all values `a: A`."]
        #[doc =
          " Equivalently, it can be thought of as a boolean predicate on `A`."]
        #[doc = ""]
        #[doc = " In general, a set might be infinite."]
        #[doc =
          " To work specifically with finite sets, see the [`self.finite()`](Set::finite) predicate."]
        #[doc = " "]
        #[doc = " Sets can be constructed in a few different ways:"]
        #[doc = "  * [`Set::empty`] gives an empty set"]
        #[doc = "  * [`Set::full`] gives the set of all elements in `A`"]
        #[doc = "  * [`Set::new`] constructs a set from a boolean predicate"]
        #[doc =
          "  * The [`set!`] macro, to construct small sets of a fixed size"]
        #[doc =
          "  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],"]
        #[doc =
          "    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],"]
        #[doc = "    or [`Set::remove`]."]
        #[doc = ""]
        #[doc =
          " To prove that two sequences are equal, it is usually easiest to use the [`assert_seqs_equal!`] macro."]
        #[verifier(external_body)]
        pub struct Set<#[verifier(maybe_negative)] A> {
            dummy: std::marker::PhantomData<A>,
        }
        impl <A> Set<A> { }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! set_internal {
            [$($elem : expr), * $(,) ?] =>
            {
                $crate :: pervasive :: set :: Set :: empty() $(.insert($elem))
                *
            } ;
        }
        #[macro_export]
        macro_rules! set {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: set :: set_internal! ($($tail) *))
            } ;
        }
        pub use set_internal;
        pub use set;
    }
    pub mod set_lib {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::set::*;
        impl <A> Set<A> { }
        #[doc = " Prove two sets equal by extensionality. Usage is:"]
        #[doc = ""]
        #[doc = " ```rust"]
        #[doc = " assert_sets_equal!(set1, set2);"]
        #[doc = " ```"]
        #[doc = " "]
        #[doc = " or,"]
        #[doc = " "]
        #[doc = " ```rust"]
        #[doc = " assert_sets_equal!(set1, set2, elem => {"]
        #[doc =
          "     // prove that set1.contains(elem) iff set2.contains(elem)"]
        #[doc = " });"]
        #[doc = " ```"]
        #[macro_export]
        macro_rules! assert_sets_equal {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: set_lib :: assert_sets_equal_internal!
                 ($($tail) *))
            } ;
        }
        #[macro_export]
        #[doc(hidden)]
        macro_rules! assert_sets_equal_internal {
            ($s1 : expr, $s2 : expr $(,) ?) =>
            { assert_sets_equal_internal! ($s1, $s2, elem => { }) } ;
            ($s1 : expr, $s2 : expr, $elem : ident $(: $t : ty) ? => $bblock :
             block) =>
            {
                let s1 = $crate :: pervasive :: set_lib ::
                check_argument_is_set($s1) ; let s2 = $crate :: pervasive ::
                set_lib :: check_argument_is_set($s2) ; :: builtin ::
                assert_by(:: builtin :: equal(s1, s2),
                          {
                              :: builtin ::
                              assert_forall_by(| $elem $(: $t) ? |
                                               {
                                                   :: builtin ::
                                                   ensures(:: builtin ::
                                                           imply(s1.contains($elem),
                                                                 s2.contains($elem))
                                                           && :: builtin ::
                                                           imply(s2.contains($elem),
                                                                 s1.contains($elem)))
                                                   ; { $bblock }
                                               }) ; $crate :: pervasive ::
                              assert(s1.ext_equal(s2)) ;
                          }) ;
            }
        }
        pub use assert_sets_equal_internal;
        pub use assert_sets_equal;
    }
    pub mod cell {
        use std::cell::UnsafeCell;
        use std::mem::MaybeUninit;
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::modes::*;
        #[doc =
          " `PCell<V>` (which stands for \"permissioned call\") is the primitive Verus `Cell` type."]
        #[doc = ""]
        #[doc = " Technically, it is a wrapper around"]
        #[doc =
          " `std::cell::UnsafeCell<std::mem::MaybeUninit<V>>`, and thus has the same runtime"]
        #[doc =
          " properties: there are no runtime checks (as there would be for Rust\'s traditional"]
        #[doc =
          " [`std::cell::RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html))."]
        #[doc = " Its data may be uninitialized."]
        #[doc = ""]
        #[doc = " Furthermore (and unlike both"]
        #[doc =
          " [`std::cell::Cell`](https://doc.rust-lang.org/std/cell/struct.Cell.html) and"]
        #[doc =
          " [`std::cell::RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html)),"]
        #[doc = " a `PCell<V>` may be `Sync` (depending on `V`)."]
        #[doc =
          " Thanks to verification, Verus ensures that access to the cell is data-race-free."]
        #[doc = ""]
        #[doc =
          " `PCell` uses a _ghost permission token_ similar to [`ptr::PPtr`] -- see the [`ptr::PPtr`]"]
        #[doc = " documentation for the basics."]
        #[doc =
          " For `PCell`, the associated type of the permission token is [`cell::PermissionOpt`]."]
        #[doc = ""]
        #[doc = " ### Differences from `PPtr`."]
        #[doc = ""]
        #[doc =
          " The key difference is that, whereas [`ptr::PPtr`] represents a fixed address in memory,"]
        #[doc =
          " a `PCell` has _no_ fixed address because a `PCell` might be moved."]
        #[doc =
          " As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,"]
        #[doc =
          " it is a unique identifier that is fixed for a given cell, even when it is moved."]
        #[doc = ""]
        #[doc =
          " The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`]."]
        #[doc =
          " Despite the fact that it is, in some ways, \"like a pointer\", note that"]
        #[doc = " `CellId` does not support any meangingful arithmetic,"]
        #[doc = " has no concept of a \"null ID\","]
        #[doc = " and has no runtime representation."]
        #[doc = ""]
        #[doc =
          " Also note that the `PCell` might be dropped before the `PermissionOpt` token is dropped,"]
        #[doc =
          " although in that case it will no longer be possible to use the `PermissionOpt` in `exec` code"]
        #[doc = " to extract data from the cell."]
        #[doc = ""]
        #[doc = " ### Example (TODO)"]
        #[verifier(external_body)]
        pub struct PCell<#[verifier(strictly_positive)] V> {
            ucell: UnsafeCell<MaybeUninit<V>>,
        }
        #[verifier(external)]
        unsafe impl <T> Sync for PCell<T> { }
        #[verifier(external)]
        unsafe impl <T> Send for PCell<T> { }
        #[verifier(external_body)]
        #[proof]
        pub struct PermissionOpt<#[verifier(strictly_positive)] V> {
            phantom: std::marker::PhantomData<V>,
        }
        #[spec]
        pub struct PermissionOptData<V> {
            pub pcell: CellId,
            pub value: option::Option<V>,
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! pcell_opt_internal {
            [$pcell : expr => $val : expr] =>
            {
                $crate :: pervasive :: cell :: PermissionOptData
                { pcell : $pcell, value : $val, }
            } ;
        }
        #[macro_export]
        macro_rules! pcell_opt {
            [$($tail : tt) *] =>
            {
                :: builtin_macros :: verus_proof_macro_exprs!
                ($crate :: pervasive :: cell :: pcell_opt_internal!
                 ($($tail) *))
            }
        }
        pub use pcell_opt_internal;
        pub use pcell_opt;
        #[verifier(external_body)]
        pub struct CellId {
            id: int,
        }
        impl <V> PermissionOpt<V> { }
        impl <V> PCell<V> {
            #[doc = " Return an empty (\"uninitialized\") cell."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn empty() -> (PCell<V>, Tracked<PermissionOpt<V>>) {
                let p = PCell{ucell: UnsafeCell::new(MaybeUninit::uninit()),};
                (p, Tracked::assume_new())
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn put(&self, perm: &mut Tracked<PermissionOpt<V>>, v: V) {
                unsafe { *(self.ucell.get()) = MaybeUninit::new(v); }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn take(&self, perm: &mut Tracked<PermissionOpt<V>>) -> V {
                unsafe {
                    let mut m = MaybeUninit::uninit();
                    std::mem::swap(&mut m, &mut *self.ucell.get());
                    m.assume_init()
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn replace(&self, perm: &mut Tracked<PermissionOpt<V>>,
                           in_v: V) -> V {
                unsafe {
                    let mut m = MaybeUninit::new(in_v);
                    std::mem::swap(&mut m, &mut *self.ucell.get());
                    m.assume_init()
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn borrow<'a>(&'a self, perm: &'a Tracked<PermissionOpt<V>>)
             -> &'a V {
                unsafe { (*self.ucell.get()).assume_init_ref() }
            }
            #[inline(always)]
            #[verifier(verus_macro)]
            pub fn into_inner(self, perm: Tracked<PermissionOpt<V>>) -> V {
                let mut perm = perm;
                self.take(&mut perm)
            }
            #[inline(always)]
            #[verifier(verus_macro)]
            pub fn new(v: V) -> (PCell<V>, Tracked<PermissionOpt<V>>) {
                let (p, mut t) = Self::empty();
                p.put(&mut t, v);
                (p, t)
            }
        }
    }
    pub mod ptr {
        use std::mem::MaybeUninit;
        use std::alloc::{Layout};
        use std::alloc::{dealloc};
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::modes::*;
        #[doc = " `PPtr<V>` (which stands for \"permissioned pointer\")"]
        #[doc = " is a wrapper around a raw pointer to `V` on the heap."]
        #[doc = ""]
        #[doc =
          " Technically, it is a wrapper around `*mut std::mem::MaybeUninit<V>`, that is, the object"]
        #[doc = " it points to may be uninitialized."]
        #[doc = ""]
        #[doc =
          " In order to access (read or write) the value behind the pointer, the user needs"]
        #[doc =
          " a special _ghost permission token_, [`PermissionOpt<V>`](PermissionOpt). This object is `tracked`,"]
        #[doc =
          " which means that it is \"only a proof construct\" that does not appear in code,"]
        #[doc =
          " but its uses _are_ checked by the borrow-checker. This ensures memory safety,"]
        #[doc = " data-race-freedom, prohibits use-after-free, etc."]
        #[doc = ""]
        #[doc = " ### PermissionOpt objects."]
        #[doc = ""]
        #[doc =
          " The [`PermissionOpt`] object represents both the ability to access the data behind the"]
        #[doc =
          " pointer _and_ the ability to free it (return it to the memory allocator)."]
        #[doc = ""]
        #[doc = " In particular:"]
        #[doc =
          "  * When the user owns a `PermissionOpt<V>` object associated to a given pointer,"]
        #[doc =
          "    they can either read or write its contents, or deallocate (\"free\") it."]
        #[doc =
          "  * When the user has a shared borrow, `&PermissionOpt<V>`, they can read"]
        #[doc = "    the contents (i.e., obtained a shared borrow `&V`)."]
        #[doc = ""]
        #[doc =
          " The `perm: PermissionOpt<V>` object tracks two pieces of data:"]
        #[doc =
          "  * `perm.pptr` is the pointer that the permission is associated to,"]
        #[doc = "     given by [`ptr.id()`](PPtr::id)."]
        #[doc =
          "  * `perm.value` tracks the data that is behind the pointer. Thereby:"]
        #[doc =
          "      * When the user uses the permission to _read_ a value, they always"]
        #[doc = "        read the value as given by the `perm.value`."]
        #[doc =
          "      * When the user uses the permission to _write_ a value, the `perm.value`"]
        #[doc = "        data is updated."]
        #[doc = ""]
        #[doc =
          " For those familiar with separation logic, the `PermissionOpt` object plays a role"]
        #[doc =
          " similar to that of the \"points-to\" operator, _ptr_ ↦ _value_."]
        #[doc = ""]
        #[doc = " ### Differences from `PCell`."]
        #[doc = ""]
        #[doc =
          " `PPtr` is similar to [`cell::PCell`], but has a few key differences:"]
        #[doc =
          "  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,"]
        #[doc = "    the type `T` is placed at some location on the heap."]
        #[doc =
          "  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`."]
        #[doc =
          "  * The `ptr::PermissionOpt` token represents not just the permission to read/write"]
        #[doc = "    the contents, but also to deallocate."]
        #[doc = ""]
        #[doc = " ### Example (TODO)"]
        #[verifier(external_body)]
        pub struct PPtr<#[verifier(strictly_positive)] V> {
            uptr: *mut MaybeUninit<V>,
        }
        #[verifier(external)]
        unsafe impl <T> Sync for PPtr<T> { }
        #[verifier(external)]
        unsafe impl <T> Send for PPtr<T> { }
        #[doc =
          " A `tracked` ghost object that gives the user permission to dereference a pointer"]
        #[doc =
          " for reading or writing, or to free the memory at that pointer."]
        #[doc = ""]
        #[doc =
          " The meaning of a `PermissionOpt` object is given by the data in its"]
        #[doc = " `View` object, [`PermissionOptData`]."]
        #[doc = ""]
        #[doc = " See the [`PPtr`] documentation for more details."]
        #[verifier(external_body)]
        #[proof]
        pub struct PermissionOpt<#[verifier(strictly_positive)] V> {
            phantom: std::marker::PhantomData<V>,
        }
        #[doc = " Represents the meaning of a [`PermissionOpt`] object."]
        #[spec]
        pub struct PermissionOptData<V> {
            #[doc =
              " Indicates that this token is for a pointer `ptr: PPtr<V>`"]
            #[doc = " such that [`ptr.id()`](PPtr::id) equal to this value."]
            pub pptr: int,
            #[doc =
              " Indicates that this token gives the ability to read a value `V` from memory."]
            #[doc =
              " When `None`, it indicates that the memory is uninitialized."]
            pub value: option::Option<V>,
        }
        impl <V> PermissionOpt<V> { }
        impl <V> PPtr<V> {
            #[doc = " Cast a pointer to an integer."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn to_usize(&self) -> usize { self.uptr as usize }
            #[doc = " Cast an integer to a pointer."]
            #[doc = " "]
            #[doc =
              " Note that this does _not_ require or ensure that the pointer is valid."]
            #[doc =
              " Of course, if the user creates an invalid pointer, they would still not be able to"]
            #[doc =
              " create a valid [`PermissionOpt`] token for it, and thus they would never"]
            #[doc = " be able to access the data behind the pointer."]
            #[doc = ""]
            #[doc =
              " This is analogous to normal Rust, where casting to a pointer is always possible,"]
            #[doc = " but dereferencing a pointer is an `unsafe` operation."]
            #[doc =
              " In Verus, casting to a pointer is likewise always possible,"]
            #[doc =
              " while dereferencing it is only allowed when the right preconditions are met."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn from_usize(u: usize) -> Self {
                let uptr = u as *mut MaybeUninit<V>;
                PPtr{uptr,}
            }
            #[doc =
              " Allocates heap memory for type `V`, leaving it uninitialized."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn empty() -> (PPtr<V>, Tracked<PermissionOpt<V>>) {
                let p =
                    PPtr{uptr:
                             Box::leak(box
                                           MaybeUninit::uninit()).as_mut_ptr(),};
                let _exposed_addr = p.uptr as usize;
                (p, Tracked::assume_new())
            }
            #[doc = " Clones the pointer."]
            #[doc = " TODO implement the `Clone` and `Copy` traits"]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn clone(&self) -> PPtr<V> { PPtr{uptr: self.uptr,} }
            #[doc =
              " Moves `v` into the location pointed to by the pointer `self`."]
            #[doc =
              " Requires the memory to be uninitialized, and leaves it initialized."]
            #[doc = ""]
            #[doc = " In the ghost perspective, this updates `perm.value`"]
            #[doc = " from `None` to `Some(v)`."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn put(&self, perm: &mut Tracked<PermissionOpt<V>>, v: V) {
                unsafe { *(self.uptr) = MaybeUninit::new(v); }
            }
            #[doc =
              " Moves `v` out of the location pointed to by the pointer `self`"]
            #[doc = " and returns it."]
            #[doc =
              " Requires the memory to be initialized, and leaves it uninitialized."]
            #[doc = ""]
            #[doc = " In the ghost perspective, this updates `perm@.value`"]
            #[doc = " from `Some(v)` to `None`,"]
            #[doc = " while returning the `v` as an `exec` value."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn take(&self, perm: &mut Tracked<PermissionOpt<V>>) -> V {
                unsafe {
                    let mut m = MaybeUninit::uninit();
                    std::mem::swap(&mut m, &mut *self.uptr);
                    m.assume_init()
                }
            }
            #[doc =
              " Swaps the `in_v: V` passed in as an argument with the value in memory."]
            #[doc =
              " Requires the memory to be initialized, and leaves it initialized with the new value."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn replace(&self, perm: &mut Tracked<PermissionOpt<V>>,
                           in_v: V) -> V {
                unsafe {
                    let mut m = MaybeUninit::new(in_v);
                    std::mem::swap(&mut m, &mut *self.uptr);
                    m.assume_init()
                }
            }
            #[doc =
              " Given a shared borrow of the `PermissionOpt<V>`, obtain a shared borrow of `V`."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn borrow<'a>(&self, perm: &'a Tracked<PermissionOpt<V>>)
             -> &'a V {
                unsafe { (*self.uptr).assume_init_ref() }
            }
            #[doc = " Free the memory pointed to be `perm`."]
            #[doc = " Requires the memory to be uninitialized."]
            #[doc = ""]
            #[doc =
              " This consumes `perm`, since it will no longer be safe to access"]
            #[doc = " that memory location."]
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn dispose(&self, perm: Tracked<PermissionOpt<V>>) {
                unsafe {
                    dealloc(self.uptr as *mut u8,
                            Layout::for_value(&*self.uptr));
                }
            }
            #[doc = " Free the memory pointed to be `perm` and return the "]
            #[doc = " value that was previously there."]
            #[doc = " Requires the memory to be initialized."]
            #[doc =
              " This consumes the [`PermissionOpt`] token, since the user is giving up"]
            #[doc = " access to the memory by freeing it."]
            #[inline(always)]
            #[verifier(verus_macro)]
            pub fn into_inner(self, perm: Tracked<PermissionOpt<V>>) -> V {
                let mut perm = perm;
                let v = self.take(&mut perm);
                self.dispose(perm);
                v
            }
            #[doc =
              " Allocates heap memory for type `V`, leaving it initialized"]
            #[doc = " with the given value `v`."]
            #[inline(always)]
            #[verifier(verus_macro)]
            pub fn new(v: V) -> (PPtr<V>, Tracked<PermissionOpt<V>>) {
                let (p, mut t) = Self::empty();
                p.put(&mut t, v);
                (p, t)
            }
        }
    }
    pub mod invariant {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[proof]
        #[verifier(external_body)]
        pub struct AtomicInvariant<#[verifier(maybe_negative)] V> {
            dummy: builtin::SyncSendIfSend<V>,
        }
        #[verifier(external_body)]
        pub struct LocalInvariant<#[verifier(maybe_negative)] V> {
            dummy: builtin::SendIfSend<V>,
        }
        macro_rules! declare_invariant_impl {
            ($invariant : ident) =>
            {
                #[proof] impl < V > $invariant < V >
                {
                    fndecl! (pub fn inv(& self, _v : V) -> bool) ; fndecl!
                    (pub fn namespace(& self) -> int) ; #[proof]
                    #[verifier(external_body)] #[verifier(returns(proof))] pub
                    fn
                    new(#[proof] v : V, #[spec] inv : impl Fn(V) -> bool,
                        #[spec] ns : int) -> $invariant < V >
                    {
                        requires([inv(v),]) ;
                        ensures(| i : $invariant < V > |
                                forall(| v : V | i.inv(v) == inv(v)) &&
                                equal(i.namespace(), ns)) ; unimplemented! ()
                        ;
                    } #[proof] #[verifier(external_body)]
                    #[verifier(returns(proof))] pub fn
                    into_inner(#[proof] self) -> V
                    { ensures(| v : V | self.inv(v)) ; unimplemented! () ; }
                }
            }
        }
        #[proof]
        impl <V> AtomicInvariant<V> { }
        #[proof]
        impl <V> LocalInvariant<V> { }
        #[doc(hidden)]
        #[proof]
        pub struct InvariantBlockGuard;
        #[doc(hidden)]
        #[verifier(external)]
        pub fn open_atomic_invariant_begin<'a,
                                           V>(_inv: &'a AtomicInvariant<V>)
         -> (&'a InvariantBlockGuard, V) {
            ::core::panicking::panic("not implemented");
        }
        #[doc(hidden)]
        #[verifier(external)]
        pub fn open_local_invariant_begin<'a, V>(_inv: &'a LocalInvariant<V>)
         -> (&'a InvariantBlockGuard, V) {
            ::core::panicking::panic("not implemented");
        }
        #[doc(hidden)]
        #[verifier(external)]
        pub fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) {
            ::core::panicking::panic("not implemented");
        }
        #[macro_export]
        macro_rules! open_atomic_invariant {
            ($eexpr : expr => $iident : ident => $bblock : block) =>
            {
                #[verifier(invariant_block)]
                {
                    #[allow(unused_mut)] let(guard, mut $iident) = $crate ::
                    pervasive :: invariant ::
                    open_atomic_invariant_begin($eexpr) ; $bblock $crate ::
                    pervasive :: invariant ::
                    open_invariant_end(guard, $iident) ;
                }
            }
        }
        #[macro_export]
        macro_rules! open_local_invariant {
            ($eexpr : expr => $iident : ident => $bblock : block) =>
            {
                #[verifier(invariant_block)]
                {
                    #[allow(unused_mut)] let(guard, mut $iident) = $crate ::
                    pervasive :: invariant ::
                    open_local_invariant_begin($eexpr) ; $bblock $crate ::
                    pervasive :: invariant ::
                    open_invariant_end(guard, $iident) ;
                }
            }
        }
    }
    pub mod atomic {
        use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU16, AtomicU32,
                                AtomicU64, AtomicI8, AtomicI16, AtomicI32,
                                AtomicI64, Ordering};
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::modes::*;
        #[allow(unused_imports)]
        use crate::pervasive::result::*;
        macro_rules! make_unsigned_integer_atomic {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty, $wrap_add : ident, $wrap_sub : ident, $int_min : expr,
             $int_max : expr) =>
            {
                verus!
                {
                    pub open spec fn $wrap_add(a : int, b : int) -> int
                    {
                        if a + b > $int_max
                        { a + b - ($int_max - $int_min + 1) } else { a + b }
                    } pub open spec fn $wrap_sub(a : int, b : int) -> int
                    {
                        if a - b < $int_min
                        { a - b + ($int_max - $int_min + 1) } else { a - b }
                    }
                } atomic_types! ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                impl $at_ident
                {
                    atomic_common_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                    atomic_integer_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add,
                     $wrap_sub, $int_min, $int_max) ;
                }
            }
        }
        macro_rules! make_signed_integer_atomic {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty, $wrap_add : ident, $wrap_sub : ident, $int_min : expr,
             $int_max : expr) =>
            {
                verus!
                {
                    pub open spec fn $wrap_add(a : int, b : int) -> int
                    {
                        if a + b > $int_max
                        { a + b - ($int_max - $int_min + 1) } else if a + b <
                        $int_min { a + b + ($int_max - $int_min + 1) } else
                        { a + b }
                    } pub open spec fn $wrap_sub(a : int, b : int) -> int
                    {
                        if a - b > $int_max
                        { a - b - ($int_max - $int_min + 1) } else if a - b <
                        $int_min { a - b + ($int_max - $int_min + 1) } else
                        { a - b }
                    }
                } atomic_types! ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                impl $at_ident
                {
                    atomic_common_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                    atomic_integer_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add,
                     $wrap_sub, $int_min, $int_max) ;
                }
            }
        }
        macro_rules! make_bool_atomic {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty) =>
            {
                atomic_types! ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                impl $at_ident
                {
                    atomic_common_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                    atomic_bool_methods!
                    ($at_ident, $p_ident, $rust_ty, $value_ty) ;
                }
            }
        }
        macro_rules! atomic_types {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty) =>
            {
                #[verifier(external_body)] pub struct $at_ident
                { ato : $rust_ty, } #[proof] #[verifier(unforgeable)] pub
                struct $p_ident
                { #[spec] pub patomic : int, #[spec] pub value : $value_ty, }
                impl $p_ident
                {
                    #[spec] #[verifier(publish)] pub fn
                    is_for(& self, patomic : $at_ident) -> bool
                    { self.patomic == patomic.id() } #[spec]
                    #[verifier(publish)] pub fn
                    points_to(& self, v : $value_ty) -> bool
                    { self.value == v }
                }
            }
        }
        macro_rules! atomic_common_methods {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty) =>
            {
                fndecl! (pub fn id(& self) -> int) ; #[inline(always)]
                #[verifier(external_body)] pub fn new(i : $value_ty) ->
                ($at_ident, Proof < $p_ident >)
                {
                    ensures(| res : ($at_ident, Proof < $p_ident >) |
                            equal(res.1,
                                  Proof($p_ident
                                        { patomic : res.0.id(), value : i })))
                    ; let p = $at_ident { ato : < $rust_ty > :: new(i) } ; let
                    Proof(t) = exec_proof_from_false() ; (p, Proof(t))
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                load(& self, #[proof] perm : & $p_ident) -> $value_ty
                {
                    requires([equal(self.id(), perm.patomic),]) ;
                    ensures(| ret : $value_ty | equal(perm.value, ret)) ;
                    opens_invariants_none() ; return
                    self.ato.load(Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                store(& self, #[proof] perm : & mut $p_ident, v : $value_ty)
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(equal(perm.value, v) &&
                            equal(self.id(), perm.patomic)) ;
                    opens_invariants_none() ;
                    self.ato.store(v, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                compare_exchange(& self, #[proof] perm : & mut $p_ident,
                                 current : $value_ty, new : $value_ty) ->
                Result < $value_ty, $value_ty >
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : Result < $value_ty, $value_ty > |
                            equal(self.id(), perm.patomic) && match ret
                            {
                                Result :: Ok(r) => current == old(perm).value
                                && equal(perm.value, new) &&
                                equal(r, old(perm).value), Result :: Err(r) =>
                                current != old(perm).value &&
                                equal(perm.value, old(perm).value) &&
                                equal(r, old(perm).value),
                            }) ; opens_invariants_none() ; match
                    self.ato.compare_exchange(current, new, Ordering ::
                                              SeqCst, Ordering :: SeqCst)
                    { Ok(x) => Result :: Ok(x), Err(x) => Result :: Err(x), }
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                compare_exchange_weak(& self, #[proof] perm : & mut $p_ident,
                                      current : $value_ty, new : $value_ty) ->
                Result < $value_ty, $value_ty >
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : Result < $value_ty, $value_ty > |
                            equal(self.id(), perm.patomic) && match ret
                            {
                                Result :: Ok(r) => current == old(perm).value
                                && equal(perm.value, new) &&
                                equal(r, old(perm).value), Result :: Err(r) =>
                                equal(perm.value, old(perm).value) &&
                                equal(r, old(perm).value),
                            }) ; opens_invariants_none() ; match
                    self.ato.compare_exchange_weak(current, new, Ordering ::
                                                   SeqCst, Ordering :: SeqCst)
                    { Ok(x) => Result :: Ok(x), Err(x) => Result :: Err(x), }
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                swap(& self, #[proof] perm : & mut $p_ident, v : $value_ty) ->
                $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : $value_ty | equal(perm.value, v) &&
                            equal(old(perm).value, ret) &&
                            equal(self.id(), perm.patomic)) ;
                    opens_invariants_none() ; return
                    self.ato.swap(v, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)] pub fn
                into_inner(self, #[proof] perm : $p_ident) -> $value_ty
                {
                    requires([equal(self.id(), perm.patomic),]) ;
                    ensures(| ret : $value_ty | equal(perm.value, ret)) ;
                    opens_invariants_none() ; return self.ato.into_inner() ;
                }
            }
        }
        macro_rules! atomic_integer_methods {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty, $wrap_add : ident, $wrap_sub : ident, $int_min : expr,
             $int_max : expr) =>
            {
                #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_add_wrapping(& self, #[proof] perm : & mut $p_ident, n :
                                   $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, spec_cast_integer :: <
                             $value_ty, int > (perm.value) ==
                             $wrap_add(spec_cast_integer(old(perm).value),
                                       spec_cast_integer(n)),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_add(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_sub_wrapping(& self, #[proof] perm : & mut $p_ident, n :
                                   $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, spec_cast_integer :: <
                             $value_ty, int > (perm.value) ==
                             $wrap_sub(spec_cast_integer :: < $value_ty, int >
                                       (old(perm).value),
                                       spec_cast_integer(n)),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_sub(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(atomic)] pub fn
                fetch_add(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic), $int_min <=
                              old(perm).value.spec_add(n),
                              old(perm).value.spec_add(n) <= $int_max]) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value == old(perm).value
                             + n,]) ; opens_invariants_none() ;
                    self.fetch_add_wrapping(& mut * perm, n)
                } #[inline(always)] #[verifier(atomic)] pub fn
                fetch_sub(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic), $int_min <=
                              old(perm).value.spec_sub(n),
                              old(perm).value.spec_sub(n) <= $int_max,]) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value == old(perm).value
                             - n,]) ; opens_invariants_none() ;
                    self.fetch_sub_wrapping(& mut * perm, n)
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_and(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==
                             (old(perm).value & n),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_and(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_or(& self, #[proof] perm : & mut $p_ident, n :
                         $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==
                             (old(perm).value | n),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_or(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_xor(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==
                             (old(perm).value ^ n),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_or(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_nand(& self, #[proof] perm : & mut $p_ident, n :
                           $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==!
                             (old(perm).value & n),]) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_nand(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_max(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==
                             (if old(perm).value > n { old(perm).value } else
                              { n }),]) ; opens_invariants_none() ; return
                    self.ato.fetch_max(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_min(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires(equal(self.id(), old(perm).patomic)) ;
                    ensures(| ret : $value_ty |
                            [equal(old(perm).value, ret), perm.patomic ==
                             old(perm).patomic, perm.value ==
                             (if old(perm).value < n { old(perm).value } else
                              { n }),]) ; opens_invariants_none() ; return
                    self.ato.fetch_min(n, Ordering :: SeqCst) ;
                }
            }
        }
        macro_rules! atomic_bool_methods {
            ($at_ident : ident, $p_ident : ident, $rust_ty : ty, $value_ty :
             ty) =>
            {
                #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_and(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : $value_ty | equal(old(perm).value, ret) &&
                            perm.patomic == old(perm).patomic && perm.value ==
                            (old(perm).value && n)) ; opens_invariants_none()
                    ; return self.ato.fetch_and(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_or(& self, #[proof] perm : & mut $p_ident, n :
                         $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : $value_ty | equal(old(perm).value, ret) &&
                            perm.patomic == old(perm).patomic && perm.value ==
                            (old(perm).value || n)) ; opens_invariants_none()
                    ; return self.ato.fetch_or(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_xor(& self, #[proof] perm : & mut $p_ident, n :
                          $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : $value_ty | equal(old(perm).value, ret) &&
                            perm.patomic == old(perm).patomic && perm.value ==
                            ((old(perm).value &&! n) ||
                             (! old(perm).value && n))) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_or(n, Ordering :: SeqCst) ;
                } #[inline(always)] #[verifier(external_body)]
                #[verifier(atomic)] pub fn
                fetch_nand(& self, #[proof] perm : & mut $p_ident, n :
                           $value_ty) -> $value_ty
                {
                    requires([equal(self.id(), old(perm).patomic),]) ;
                    ensures(| ret : $value_ty | equal(old(perm).value, ret) &&
                            perm.patomic == old(perm).patomic && perm.value
                            ==! (old(perm).value && n)) ;
                    opens_invariants_none() ; return
                    self.ato.fetch_nand(n, Ordering :: SeqCst) ;
                }
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicBool {
            ato: AtomicBool,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionBool {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<bool>,
        }
        impl PermissionBool { }
        impl PAtomicBool {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: bool) -> (PAtomicBool, Proof<PermissionBool>) {
                let p = PAtomicBool{ato: <AtomicBool>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> bool {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: bool) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: bool, new: bool)
             -> Result<bool, bool> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: bool, new: bool)
             -> Result<bool, bool> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: bool) -> bool {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> bool { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: bool) -> bool {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: bool) -> bool {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: bool) -> bool {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: bool) -> bool {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicU8 {
            ato: AtomicU8,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionU8 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<u8>,
        }
        impl PermissionU8 { }
        impl PAtomicU8 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: u8) -> (PAtomicU8, Proof<PermissionU8>) {
                let p = PAtomicU8{ato: <AtomicU8>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> u8 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: u8) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: u8, new: u8)
             -> Result<u8, u8> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: u8, new: u8)
             -> Result<u8, u8> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: u8) -> u8 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> u8 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: u8) -> u8 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: u8) -> u8 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: u8) -> u8 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: u8) -> u8 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: u8) -> u8 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: u8) -> u8 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: u8) -> u8 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: u8) -> u8 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: u8) -> u8 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: u8) -> u8 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicU16 {
            ato: AtomicU16,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionU16 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<u16>,
        }
        impl PermissionU16 { }
        impl PAtomicU16 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: u16) -> (PAtomicU16, Proof<PermissionU16>) {
                let p = PAtomicU16{ato: <AtomicU16>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> u16 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: u16) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: u16, new: u16)
             -> Result<u16, u16> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: u16, new: u16)
             -> Result<u16, u16> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: u16) -> u16 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> u16 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: u16) -> u16 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: u16) -> u16 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: u16) -> u16 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: u16) -> u16 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: u16) -> u16 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: u16) -> u16 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: u16) -> u16 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: u16) -> u16 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: u16) -> u16 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: u16) -> u16 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicU32 {
            ato: AtomicU32,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionU32 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<u32>,
        }
        impl PermissionU32 { }
        impl PAtomicU32 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: u32) -> (PAtomicU32, Proof<PermissionU32>) {
                let p = PAtomicU32{ato: <AtomicU32>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> u32 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: u32) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: u32, new: u32)
             -> Result<u32, u32> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: u32, new: u32)
             -> Result<u32, u32> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: u32) -> u32 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> u32 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: u32) -> u32 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: u32) -> u32 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: u32) -> u32 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: u32) -> u32 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: u32) -> u32 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: u32) -> u32 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: u32) -> u32 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: u32) -> u32 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: u32) -> u32 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: u32) -> u32 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicU64 {
            ato: AtomicU64,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionU64 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<u64>,
        }
        impl PermissionU64 { }
        impl PAtomicU64 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: u64) -> (PAtomicU64, Proof<PermissionU64>) {
                let p = PAtomicU64{ato: <AtomicU64>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> u64 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: u64) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: u64, new: u64)
             -> Result<u64, u64> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: u64, new: u64)
             -> Result<u64, u64> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: u64) -> u64 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> u64 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: u64) -> u64 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: u64) -> u64 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: u64) -> u64 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: u64) -> u64 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: u64) -> u64 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: u64) -> u64 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: u64) -> u64 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: u64) -> u64 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: u64) -> u64 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: u64) -> u64 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicI8 {
            ato: AtomicI8,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionI8 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<i8>,
        }
        impl PermissionI8 { }
        impl PAtomicI8 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: i8) -> (PAtomicI8, Proof<PermissionI8>) {
                let p = PAtomicI8{ato: <AtomicI8>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> i8 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: i8) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: i8, new: i8)
             -> Result<i8, i8> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: i8, new: i8)
             -> Result<i8, i8> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: i8) -> i8 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> i8 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: i8) -> i8 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: i8) -> i8 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: i8) -> i8 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: i8) -> i8 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: i8) -> i8 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: i8) -> i8 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: i8) -> i8 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: i8) -> i8 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: i8) -> i8 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: i8) -> i8 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicI16 {
            ato: AtomicI16,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionI16 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<i16>,
        }
        impl PermissionI16 { }
        impl PAtomicI16 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: i16) -> (PAtomicI16, Proof<PermissionI16>) {
                let p = PAtomicI16{ato: <AtomicI16>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> i16 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: i16) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: i16, new: i16)
             -> Result<i16, i16> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: i16, new: i16)
             -> Result<i16, i16> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: i16) -> i16 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> i16 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: i16) -> i16 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: i16) -> i16 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: i16) -> i16 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: i16) -> i16 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: i16) -> i16 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: i16) -> i16 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: i16) -> i16 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: i16) -> i16 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: i16) -> i16 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: i16) -> i16 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicI32 {
            ato: AtomicI32,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionI32 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<i32>,
        }
        impl PermissionI32 { }
        impl PAtomicI32 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: i32) -> (PAtomicI32, Proof<PermissionI32>) {
                let p = PAtomicI32{ato: <AtomicI32>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> i32 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: i32) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: i32, new: i32)
             -> Result<i32, i32> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: i32, new: i32)
             -> Result<i32, i32> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: i32) -> i32 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> i32 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: i32) -> i32 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: i32) -> i32 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: i32) -> i32 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: i32) -> i32 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: i32) -> i32 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: i32) -> i32 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: i32) -> i32 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: i32) -> i32 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: i32) -> i32 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: i32) -> i32 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
        #[verifier(external_body)]
        pub struct PAtomicI64 {
            ato: AtomicI64,
        }
        #[proof]
        #[verifier(unforgeable)]
        pub struct PermissionI64 {
            #[spec]
            pub patomic: std::marker::PhantomData<int>,
            #[spec]
            pub value: std::marker::PhantomData<i64>,
        }
        impl PermissionI64 { }
        impl PAtomicI64 {
            #[inline(always)]
            #[verifier(external_body)]
            pub fn new(i: i64) -> (PAtomicI64, Proof<PermissionI64>) {
                let p = PAtomicI64{ato: <AtomicI64>::new(i),};
                let Proof(t) = exec_proof_from_false();
                (p, Proof(t))
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn load(&self) -> i64 {
                return self.ato.load(Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn store(&self, v: i64) {
                self.ato.store(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange(&self, current: i64, new: i64)
             -> Result<i64, i64> {
                match self.ato.compare_exchange(current, new,
                                                Ordering::SeqCst,
                                                Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn compare_exchange_weak(&self, current: i64, new: i64)
             -> Result<i64, i64> {
                match self.ato.compare_exchange_weak(current, new,
                                                     Ordering::SeqCst,
                                                     Ordering::SeqCst) {
                    Ok(x) => Result::Ok(x),
                    Err(x) => Result::Err(x),
                }
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn swap(&self, v: i64) -> i64 {
                return self.ato.swap(v, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            pub fn into_inner(self) -> i64 { return self.ato.into_inner(); }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_add_wrapping(&self, n: i64) -> i64 {
                return self.ato.fetch_add(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_sub_wrapping(&self, n: i64) -> i64 {
                return self.ato.fetch_sub(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_add(&self, n: i64) -> i64 {
                self.fetch_add_wrapping(n)
            }
            #[inline(always)]
            #[verifier(atomic)]
            pub fn fetch_sub(&self, n: i64) -> i64 {
                self.fetch_sub_wrapping(n)
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_and(&self, n: i64) -> i64 {
                return self.ato.fetch_and(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_or(&self, n: i64) -> i64 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_xor(&self, n: i64) -> i64 {
                return self.ato.fetch_or(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_nand(&self, n: i64) -> i64 {
                return self.ato.fetch_nand(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_max(&self, n: i64) -> i64 {
                return self.ato.fetch_max(n, Ordering::SeqCst);
            }
            #[inline(always)]
            #[verifier(external_body)]
            #[verifier(atomic)]
            pub fn fetch_min(&self, n: i64) -> i64 {
                return self.ato.fetch_min(n, Ordering::SeqCst);
            }
        }
    }
    pub mod atomic_ghost {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::invariant::*;
        use crate::pervasive::atomic::*;
        use crate::pervasive::modes::*;
        macro_rules! declare_atomic_type {
            ($at_ident : ident, $patomic_ty : ident, $perm_ty : ty, $value_ty
             : ty) =>
            {
                pub struct $at_ident < #[verifier(maybe_negative)] G >
                {
                    pub patomic : $patomic_ty, #[proof] pub atomic_inv :
                    AtomicInvariant < ($perm_ty, G) >,
                } impl < G > $at_ident < G >
                {
                    #[spec] #[verifier(publish)] pub fn
                    has_inv(& self, f : impl Fn($value_ty, G) -> bool) -> bool
                    {
                        forall(| p | #[trigger] self.atomic_inv.inv(p) ==
                               (self.patomic.id() == p.0.patomic &&
                                f(p.0.value, p.1)))
                    } #[spec] #[verifier(publish)] pub fn
                    has_inv_fn(& self, f : impl Fn($value_ty) -> G) -> bool
                    { self.has_inv(| v : $value_ty, g : G | equal(g, f(v))) }
                    #[inline(always)] pub fn
                    new(u : $value_ty, #[proof] g : G, #[spec] f : impl
                        Fn($value_ty, G) -> bool) -> Self
                    {
                        requires(f(u, g)) ; ensures(| t : Self | t.has_inv(f))
                        ; let(patomic, Proof(perm)) = $patomic_ty :: new(u) ;
                        #[proof] let pair = (perm, g) ; #[proof] let
                        atomic_inv = AtomicInvariant ::
                        new(pair, | p | patomic.id() == p.0.patomic &&
                            f(p.0.value, p.1), spec_literal_int("0")) ;
                        $at_ident { patomic, atomic_inv, }
                    }
                }
            }
        }
        pub struct AtomicU64<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicU64,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionU64,
                                                                      G)>>,
        }
        impl <G> AtomicU64<G> {
            #[inline(always)]
            pub fn new(u: u64) -> Self {
                let (patomic, Proof(_)) = PAtomicU64::new(u);
                AtomicU64{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicU32<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicU32,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionU32,
                                                                      G)>>,
        }
        impl <G> AtomicU32<G> {
            #[inline(always)]
            pub fn new(u: u32) -> Self {
                let (patomic, Proof(_)) = PAtomicU32::new(u);
                AtomicU32{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicU16<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicU16,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionU16,
                                                                      G)>>,
        }
        impl <G> AtomicU16<G> {
            #[inline(always)]
            pub fn new(u: u16) -> Self {
                let (patomic, Proof(_)) = PAtomicU16::new(u);
                AtomicU16{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicU8<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicU8,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionU8,
                                                                      G)>>,
        }
        impl <G> AtomicU8<G> {
            #[inline(always)]
            pub fn new(u: u8) -> Self {
                let (patomic, Proof(_)) = PAtomicU8::new(u);
                AtomicU8{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicI64<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicI64,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionI64,
                                                                      G)>>,
        }
        impl <G> AtomicI64<G> {
            #[inline(always)]
            pub fn new(u: i64) -> Self {
                let (patomic, Proof(_)) = PAtomicI64::new(u);
                AtomicI64{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicI32<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicI32,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionI32,
                                                                      G)>>,
        }
        impl <G> AtomicI32<G> {
            #[inline(always)]
            pub fn new(u: i32) -> Self {
                let (patomic, Proof(_)) = PAtomicI32::new(u);
                AtomicI32{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicI16<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicI16,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionI16,
                                                                      G)>>,
        }
        impl <G> AtomicI16<G> {
            #[inline(always)]
            pub fn new(u: i16) -> Self {
                let (patomic, Proof(_)) = PAtomicI16::new(u);
                AtomicI16{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicI8<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicI8,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionI8,
                                                                      G)>>,
        }
        impl <G> AtomicI8<G> {
            #[inline(always)]
            pub fn new(u: i8) -> Self {
                let (patomic, Proof(_)) = PAtomicI8::new(u);
                AtomicI8{patomic, std::marker::PhantomData,}
            }
        }
        pub struct AtomicBool<#[verifier(maybe_negative)] G> {
            pub patomic: PAtomicBool,
            #[proof]
            pub atomic_inv: std::marker::PhantomData<AtomicInvariant<(PermissionBool,
                                                                      G)>>,
        }
        impl <G> AtomicBool<G> {
            #[inline(always)]
            pub fn new(u: bool) -> Self {
                let (patomic, Proof(_)) = PAtomicBool::new(u);
                AtomicBool{patomic, std::marker::PhantomData,}
            }
        }
        /// Macro to perform a given atomic operation on a given atomic
        /// while providing access to its ghost state.
        /// `atomic_with_ghost!` supports the types
        /// [`AtomicU64`] [`AtomicU32`], [`AtomicU16`], [`AtomicU8`],
        /// [`AtomicI64`], [`AtomicI32`], [`AtomicI16`], [`AtomicI8`], and [`AtomicBool`].
        ///
        /// For each type, it supports all applicable atomic operations among
        /// `load`, `store`, `swap`, `compare_exchange`, `compare_exchange_weak`,
        /// `fetch_add`, `fetch_add_wrapping`, `fetch_sub`, `fetch_sub_wrapping`,
        /// `fetch_or`, `fetch_and`, `fetch_xor`, `fetch_nand`, `fetch_max`, and `fetch_min`.
        ///
        /// Naturally, `AtomicBool` does not support the arithmetic-specific operations.
        ///
        /// In general, the syntax is:
        ///
        ///     let result = atomic_with_ghost!(
        ///         $atomic => $operation_name($operands...);
        ///         update $prev -> $next;         // `update` line is optional
        ///         returning $ret;                // `returning` line is optional
        ///         ghost $g => {
        ///             /* Proof code with access to `tracked` variable `g: G` */
        ///         }
        ///     );
        ///
        /// Here, the `$operation_name` is one of `load`, `store`, etc. Meanwhile,
        /// `$prev`, `$next`, and `$ret` are all identifiers which 
        /// will be available as spec variable inside the block to describe the
        /// atomic action which is performed.
        ///
        /// For example, suppose the user performs `fetch_add(1)`. The atomic
        /// operation might load the value 5, add 1, store the value 6,
        /// and return the original value, 5. In that case, we would have
        /// `prev == 5`, `next == 6`, and `ret == 5`.
        ///
        /// The specification for a given operation is given as a relation between
        /// `prev`, `next`, and `ret`; that is, at the beginning of the proof block,
        /// the user may assume the given specification holds:
        ///
        /// | operation                     | specification                                                                                                              |
        /// |-------------------------------|----------------------------------------------------------------------------------------------------------------------------|
        /// | `load()`                      | `next == prev && rev == prev`                                                                                              |
        /// | `store(x)`                    | `next == x && ret == ()`                                                                                                   |
        /// | `swap(x)`                     | `next == x && ret == prev`                                                                                                 |
        /// | `compare_exchange(x, y)`      | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `prev != x && next == prev && ret == Err(prev)` ("failure") |
        /// | `compare_exchange_weak(x, y)` | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `next == prev && ret == Err(prev)` ("failure")              |
        /// | `fetch_add(x)` (*)            | `next == prev + x && ret == prev`                                                                                          |
        /// | `fetch_add_wrapping(x)`       | `next == wrapping_add(prev, x) && ret == prev`                                                                             |
        /// | `fetch_sub(x)` (*)            | `next == prev - x && ret == prev`                                                                                          |
        /// | `fetch_sub_wrapping(x)`       | `next == wrapping_sub(prev, x) && ret == prev`                                                                             |
        /// | `fetch_or(x)`                 | <code>next == prev \| x && ret == prev</code>                                                                              |
        /// | `fetch_and(x)`                | `next == prev & x && ret == prev`                                                                                          |
        /// | `fetch_xor(x)`                | `next == prev ^ x && ret == prev`                                                                                          |
        /// | `fetch_nand(x)`               | `next == !(prev & x) && ret == prev`                                                                                       |
        /// | `fetch_max(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
        /// | `fetch_min(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
        /// | `no_op()` (**)                | `next == prev && ret == ()`                                                                                                |
        ///
        /// (*) Note that `fetch_add` and `fetch_sub` do not specify
        /// wrapping-on-overflow; instead, they require the user to
        /// prove that overflow _does not occur_, i.e., the user must show
        /// that `next` is in bounds for the integer type in question.
        /// Furthermore, for `fetch_add` and `fetch_sub`, the spec values of
        /// `prev`, `next`, and `ret` are all given with type `int`, so the
        /// user may reason about boundedness within the proof block.
        ///
        /// (As executable code, `fetch_add` is equivalent to `fetch_add_wrapping`,
        /// and likewise for `fetch_sub` and `fetch_sub_wrapping`.
        /// We have both because it's frequently the case that the user needs to verify
        /// lack-of-overflow _anyway_, and having it as an explicit precondition by default
        /// then makes verification errors easier to diagnose. Furthermore, when overflow is
        /// intended, the wrapping operations document that intent.)
        ///
        /// (**) `no_op` is entirely a ghost operation and doesn't emit any actual instruction.
        /// This allows the user to access the ghost state and the stored value (as `spec` data)
        /// without actually performing a load.
        ///
        /// ---
        ///
        /// At the beginning of the proof block, the user may assume, in addition
        /// to the specified relation between `prev`, `next`, and `ret`, that
        /// `atomic.inv(prev, g)` holds. The user is required to update `g` such that
        /// `atomic.inv(next, g)` holds at the end of the block.
        /// In other words, the ghost block has the implicit pre- and post-conditions:
        ///
        ///     let result = atomic_with_ghost!(
        ///         $atomic => $operation_name($operands...);
        ///         update $prev -> $next;
        ///         returning $ret;
        ///         ghost $g => {
        ///             assume(specified relation on (prev, next, ret));
        ///             assume(atomic.inv(prev, g));
        ///
        ///             // User code here; may update variable `g` with full
        ///             // access to variables in the outer context.
        ///
        ///             assert(atomic.inv(next, g));
        ///         }
        ///     );
        ///
        /// Note that the necessary action on ghost state might depend
        /// on the result of the operation; for example, if the user performs a
        /// compare-and-swap, then the ghost action that they then need to do
        /// will probably depend on whether the operation succeeded or not.
        ///
        /// The value returned by the `atomic_with_ghost!(...)` expression will be equal
        /// to `ret`, although the return value is an `exec` value (the actual result of
        /// the operation) while `ret` is a `spec` value.
        ///
        /// ### Example (TODO)
        #[macro_export]
        macro_rules! atomic_with_ghost {
            ($atomic : expr => $operation_name : ident($($operands : tt) *) ;
             update $prev : ident -> $next : ident ; returning $ret : ident ;
             ghost $g : ident => $b : block) =>
            {
                atomic_with_ghost_inner!
                ($operation_name, $atomic, ($($operands) *), $prev, $next,
                 $ret, $g, $b)
            } ;
            ($atomic : expr => $operation_name : ident($($operands : tt) *) ;
             update $prev : ident -> $next : ident ; ghost $g : ident => $b :
             block) =>
            {
                atomic_with_ghost_inner!
                ($operation_name, $atomic, ($($operands) *), $prev, $next, _,
                 $g, $b)
            } ;
            ($atomic : expr => $operation_name : ident($($operands : tt) *) ;
             returning $ret : ident ; ghost $g : ident => $b : block) =>
            {
                atomic_with_ghost_inner!
                ($operation_name, $atomic, ($($operands) *), _, _, $ret, $g,
                 $b)
            } ;
            ($atomic : expr => $operation_name : ident($($operands : tt) *) ;
             ghost $g : ident => $b : block) =>
            {
                atomic_with_ghost_inner!
                ($operation_name, $atomic, ($($operands) *), _, _, _, $g, $b)
            } ;
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_inner {
            (load, $e : expr, (), $prev : pat, $next : pat, $ret : pat, $g :
             ident, $b : block) =>
            { atomic_with_ghost_load! ($e, $prev, $next, $ret, $g, $b) } ;
            (store, $e : expr, ($operand : expr), $prev : pat, $next : pat,
             $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_store!
                ($e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (swap, $e : expr, ($operand : expr), $prev : pat, $next : pat,
             $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (swap, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_or, $e : expr, ($operand : expr), $prev : pat, $next : pat,
             $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_or, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_and, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_and, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_xor, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_xor, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_nand, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_nand, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_max, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_max, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_min, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_min, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_add_wrapping, $e : expr, ($operand : expr), $prev : pat,
             $next : pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_add_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_sub_wrapping, $e : expr, ($operand : expr), $prev : pat,
             $next : pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_1_operand!
                (fetch_sub_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_add, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_fetch_add!
                ($e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (fetch_sub, $e : expr, ($operand : expr), $prev : pat, $next :
             pat, $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_fetch_sub!
                ($e, $operand, $prev, $next, $ret, $g, $b)
            } ;
            (compare_exchange, $e : expr,
             ($operand1 : expr, $operand2 : expr), $prev : pat, $next : pat,
             $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_2_operand!
                (compare_exchange, $e, $operand1, $operand2, $prev, $next,
                 $ret, $g, $b)
            } ;
            (compare_exchange_weak, $e : expr,
             ($operand1 : expr, $operand2 : expr), $prev : pat, $next : pat,
             $ret : pat, $g : ident, $b : block) =>
            {
                atomic_with_ghost_update_with_2_operand!
                (compare_exchange_weak, $e, $operand1, $operand2, $prev,
                 $next, $ret, $g, $b)
            } ;
            (no_op, $e : expr, (), $prev : pat, $next : pat, $ret : pat, $g :
             ident, $b : block) =>
            { atomic_with_ghost_no_op! ($e, $prev, $next, $ret, $g, $b) } ;
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_store {
            ($e : expr, $operand : expr, $prev : pat, $next : pat, $res : pat,
             $g : ident, $b : block) =>
            {
                {
                    let atomic = & $e ; crate :: open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(mut perm, mut $g) =
                         pair ; #[spec] let $prev = perm.value ;
                         atomic.patomic.store(& mut perm, $operand) ; #[spec]
                         let $next = perm.value ; #[spec] let $res = () ;
                         { $b } pair = (perm, $g) ;
                     }) ;
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_load {
            ($e : expr, $prev : pat, $next : pat, $res : pat, $g : ident, $b :
             block) =>
            {
                {
                    let result ; let atomic = & $e ; crate ::
                    open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(perm, mut $g) =
                         pair ; result = atomic.patomic.load(& perm) ; #[spec]
                         let $res = result ; #[spec] let $prev = result ;
                         #[spec] let $next = result ; { $b } pair = (perm, $g)
                         ;
                     }) ; result
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_no_op {
            ($e : expr, $prev : pat, $next : pat, $res : pat, $g : ident, $b :
             block) =>
            {
                {
                    let atomic = & $e ; crate :: open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(perm, mut $g) =
                         pair ; #[spec] let $res = result ; #[spec] let $prev
                         = result ; #[spec] let $next = result ; { $b } pair =
                         (perm, $g) ;
                     }) ;
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_update_with_1_operand {
            ($name : ident, $e : expr, $operand : expr, $prev : pat, $next :
             pat, $res : pat, $g : ident, $b : block) =>
            {
                {
                    let result ; let atomic = & $e ; crate ::
                    open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(mut perm, mut $g) =
                         pair ; #[spec] let $prev = perm.value ; result =
                         atomic.patomic.$name(& mut perm, $operand) ; #[spec]
                         let $res = result ; #[spec] let $next = perm.value ;
                         { $b } pair = (perm, $g) ;
                     }) ; result
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_update_with_2_operand {
            ($name : ident, $e : expr, $operand1 : expr, $operand2 : expr,
             $prev : pat, $next : pat, $res : pat, $g : ident, $b : block) =>
            {
                {
                    let result ; let atomic = & $e ; crate ::
                    open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(mut perm, mut $g) =
                         pair ; #[spec] let $prev = perm.value ; result =
                         atomic.patomic.$name(& mut perm, $operand1,
                                              $operand2) ; #[spec] let $res =
                         result ; #[spec] let $next = perm.value ; { $b } pair
                         = (perm, $g) ;
                     }) ; result
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_update_fetch_add {
            ($e : expr, $operand : expr, $prev : pat, $next : pat, $res : pat,
             $g : ident, $b : block) =>
            {
                {
                    let result ; let atomic = & $e ; crate ::
                    open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(mut perm, mut $g) =
                         pair ; #[spec] let $prev = perm.value as int ; let op
                         = $operand ; #[spec] let computed = perm.value +
                         (op as int) ; #[spec] let $res = computed ; #[spec]
                         let $next = computed ; { $b } result =
                         atomic.patomic.fetch_add(& mut perm, op) ; pair =
                         (perm, $g) ;
                     }) ; result
                }
            }
        }
        #[doc(hidden)]
        #[macro_export]
        macro_rules! atomic_with_ghost_update_fetch_sub {
            ($e : expr, $operand : expr, $prev : pat, $next : pat, $res : pat,
             $g : ident, $b : block) =>
            {
                {
                    let result ; let atomic = & $e ; crate ::
                    open_atomic_invariant!
                    (& atomic.atomic_inv => pair =>
                     {
                         #[allow(unused_mut)] #[proof] let(mut perm, mut $g) =
                         pair ; #[spec] let $prev = perm.value as int ; let op
                         = $operand ; #[spec] let computed = perm.value -
                         (op as int) ; #[spec] let $res = computed ; #[spec]
                         let $next = computed ; { $b } result =
                         atomic.patomic.fetch_sub(& mut perm, op) ; pair =
                         (perm, $g) ;
                     }) ; result
                }
            }
        }
    }
    pub mod modes {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        use std::marker::PhantomData;
        #[verifier(external_body)]
        pub fn ghost_exec<A>() -> Ghost<A> { Ghost::assume_new() }
        #[verifier(external_body)]
        pub fn tracked_exec<A>() -> Tracked<A> { Tracked::assume_new() }
        #[verifier(external_body)]
        pub fn tracked_exec_borrow<'a, A>() -> &'a Tracked<A> {
            ::core::panicking::panic("not implemented");
        }
        pub struct Gho<A>(
                          #[spec]
                          pub std::marker::PhantomData<A>);
        pub struct Trk<A>(
                          #[proof]
                          pub std::marker::PhantomData<A>);
        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn ghost_unwrap_gho<A>(a: Ghost<Gho<A>>) -> Ghost<A> {
            Ghost::assume_new()
        }
        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn tracked_unwrap_gho<A>(a: Tracked<Gho<A>>) -> Tracked<A> {
            Tracked::assume_new()
        }
        #[inline(always)]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn tracked_unwrap_trk<A>(a: Tracked<Trk<A>>) -> Tracked<A> {
            Tracked::assume_new()
        }
        #[verifier(external_body)]
        pub struct Spec<#[verifier(strictly_positive)] A> {
            phantom: PhantomData<A>,
        }
        pub struct Proof<A>(
                            #[proof]
                            pub std::marker::PhantomData<A>);
        impl <A> Spec<A> {
            #[verifier(external_body)]
            pub fn exec() -> Spec<A> { Spec{phantom: PhantomData,} }
        }
        impl <A> Clone for Spec<A> {
            #[verifier(external_body)]
            fn clone(&self) -> Self { Spec{phantom: PhantomData,} }
        }
        impl <A> Copy for Spec<A> { }
        impl <A> PartialEq for Spec<A> {
            #[verifier(external_body)]
            fn eq(&self, _rhs: &Spec<A>) -> bool { true }
        }
        impl <A> Eq for Spec<A> { }
        impl <A> PartialEq for Proof<A> {
            #[verifier(external_body)]
            fn eq(&self, _rhs: &Proof<A>) -> bool { true }
        }
        impl <A> Eq for Proof<A> { }
        #[allow(dead_code)]
        #[inline(always)]
        pub fn exec_proof_from_false<A>() -> Proof<A> {
            Proof(std::marker::PhantomData)
        }
    }
    pub mod multiset {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::set::*;
        #[doc =
          " `Multiset<V>` is an abstract multiset type for specifications."]
        #[doc = ""]
        #[doc =
          " `Multiset<V>` can be encoded as a (total) map from elements to natural numbers,"]
        #[doc = " where the number of nonzero entries is finite."]
        #[doc = ""]
        #[doc = " Multisets can be constructed in a few different ways:"]
        #[doc = "  * [`Multiset::empty()`] constructs an empty multiset."]
        #[doc =
          "  * By manipulating existings multisets with [`Multiset::add`], [`Multiset::insert`],"]
        #[doc =
          "    [`Multiset::sub`], [`Multiset::remove`], or [`Multiset::filter`]."]
        #[doc =
          "  * TODO: `multiset!` constructor macro, multiset from set, from map, etc."]
        #[doc = ""]
        #[doc =
          " To prove that two multisets are equal, it is usually easiest to use the "]
        #[doc = " [`assert_multisets_equal!`] macro."]
        #[verifier(external_body)]
        pub struct Multiset<#[verifier(strictly_positive)] V> {
            dummy: std::marker::PhantomData<V>,
        }
        impl <V> Multiset<V> { }
        #[macro_export]
        macro_rules! assert_multisets_equal {
            ($m1 : expr, $m2 : expr $(,) ?) =>
            { assert_multisets_equal! ($m1, $m2, key => { }) } ;
            ($m1 : expr, $m2 : expr, $k : ident $(: $t : ty) ? => $bblock :
             block) =>
            {
                #[spec] let m1 = $m1 ; #[spec] let m2 = $m2 ; :: builtin ::
                assert_by(:: builtin :: equal(m1, m2),
                          {
                              :: builtin ::
                              assert_forall_by(| $k $(: $t) ? |
                                               {
                                                   :: builtin ::
                                                   ensures([:: builtin ::
                                                            equal(m1.count($k),
                                                                  m2.count($k))])
                                                   ; { $bblock }
                                               }) ; $crate :: pervasive ::
                              assert(m1.ext_equal(m2)) ;
                          }) ;
            }
        }
    }
    pub mod state_machine_internal {
        //! Helper utilities used by the `state_machine_macros` codegen.
        #![allow(unused_imports)]
        #![doc(hidden)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use crate::pervasive::seq::*;
        use crate::pervasive::map::*;
        use crate::pervasive::option::*;
        #[verifier(external_body)]
        pub struct SyncSendIfSyncSend<#[verifier(strictly_positive)] T> {
            _sync_send: builtin::SyncSendIfSyncSend<T>,
        }
        #[doc(hidden)]
        impl <A> Seq<A> { }
        #[doc(hidden)]
        impl <K, V> Map<K, V> { }
    }
    pub mod thread {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::pervasive::result::*;
        pub trait Spawnable<Ret: Sized>: Sized {
            #[verifier(verus_macro)]
            #[exec]
            fn run(self)
            -> Ret;
        }
        #[verifier(external_body)]
        pub struct JoinHandle<#[verifier(maybe_negative)] Ret> {
            handle: std::thread::JoinHandle<Ret>,
        }
        impl <Ret> JoinHandle<Ret> {
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn join(self) -> Result<Ret, ()> {
                let res =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                                                                              {
                                                                                  match self.handle.join()
                                                                                      {
                                                                                      Ok(r)
                                                                                      =>
                                                                                      Result::Ok(r),
                                                                                      Err(_)
                                                                                      =>
                                                                                      Result::Err(()),
                                                                                  }
                                                                              }));
                match res {
                    Ok(res) => res,
                    Err(_) => {
                        {
                            ::std::io::_print(::core::fmt::Arguments::new_v1(&["panic on join\n"],
                                                                             &match ()
                                                                                  {
                                                                                  _args
                                                                                  =>
                                                                                  [],
                                                                              }));
                        };
                        std::process::abort();
                    }
                }
            }
        }
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn spawn<Param: Spawnable<Ret> + Send + 'static, Ret: Send +
                     'static>(p: Param) -> JoinHandle<Ret> {
            let res =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                                                                          {
                                                                              let handle =
                                                                                  std::thread::spawn(move
                                                                                                         ||
                                                                                                         p.run());
                                                                              JoinHandle{handle,}
                                                                          }));
            match res {
                Ok(res) => res,
                Err(_) => {
                    {
                        ::std::io::_print(::core::fmt::Arguments::new_v1(&["panic on spawn\n"],
                                                                         &match ()
                                                                              {
                                                                              _args
                                                                              =>
                                                                              [],
                                                                          }));
                    };
                    std::process::abort();
                }
            }
        }
    }
    pub mod string {
        #![feature(rustc_attrs)]
        use super::seq::Seq;
        use super::vec::Vec;
        use builtin::*;
        use builtin_macros::verus;
        #[verifier(external_body)]
        pub struct String {
            inner: std::string::String,
        }
        #[rustc_diagnostic_item = "pervasive::string::StrSlice"]
        #[verifier(external_body)]
        pub struct StrSlice<'a> {
            inner: &'a str,
        }
        #[rustc_diagnostic_item = "pervasive::string::new_strlit"]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub const fn new_strlit<'a>(s: &'a str) -> StrSlice<'a> {
            StrSlice{inner: s,}
        }
        impl <'a> StrSlice<'a> {
            #[doc = " The len() function in rust returns the byte length."]
            #[doc =
              " It is more useful to talk about the length of characters and therefore this function was added."]
            #[doc =
              " Please note that this function counts the unicode variation selectors as characters."]
            #[doc = " Warning: O(n)"]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn unicode_len(&self) -> usize { self.inner.chars().count() }
            #[doc = " Warning: O(n) not O(1) due to unicode decoding needed"]
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn get_char(&self, i: usize) -> char {
                self.inner.chars().nth(i).unwrap()
            }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn substring_ascii(&self, from: usize, to: usize)
             -> StrSlice<'a> {
                StrSlice{inner: &self.inner[from..to],}
            }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn substring_char(&self, from: usize, to: usize)
             -> StrSlice<'a> {
                let mut char_pos = 0;
                let mut byte_start = None;
                let mut byte_end = None;
                let mut byte_pos = 0;
                let mut it = self.inner.chars();
                loop {
                    if char_pos == from { byte_start = Some(byte_pos); }
                    if char_pos == to { byte_end = Some(byte_pos); break ; }
                    if let Some(c) = it.next() {
                        char_pos += 1;
                        byte_pos += c.len_utf8();
                    } else { break ; }
                }
                let byte_start = byte_start.unwrap();
                let byte_end = byte_end.unwrap();
                StrSlice{inner: &self.inner[byte_start..byte_end],}
            }
            #[verifier(verus_macro)]
            pub fn to_string(self) -> String { String::from_str(self) }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn get_ascii(&self, i: usize) -> u8 {
                self.inner.as_bytes()[i]
            }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn as_bytes(&self) -> Vec<u8> {
                let mut v = Vec::new();
                for c in self.inner.as_bytes().iter() { v.push(*c); }
                v
            }
        }
        impl String {
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn from_str<'a>(s: StrSlice<'a>) -> String {
                String{inner: s.inner.to_string(),}
            }
            #[verifier(external_body)]
            #[verifier(verus_macro)]
            pub fn as_str<'a>(&'a self) -> StrSlice<'a> {
                let inner = self.inner.as_str();
                StrSlice{inner,}
            }
        }
    }
    #[allow(unused_imports)]
    use builtin::*;
    #[verifier(external_body)]
    #[allow(dead_code)]
    pub fn unreached<A>() -> A {
        { ::std::rt::begin_panic("unreached_external") }
    }
    #[verifier(external_body)]
    pub fn print_u64(i: u64) {
        {
            ::std::io::_print(::core::fmt::Arguments::new_v1(&["", "\n"],
                                                             &match (&i,) {
                                                                  _args =>
                                                                  [::core::fmt::ArgumentV1::new(_args.0,
                                                                                                ::core::fmt::Display::fmt)],
                                                              }));
        };
    }
    /// Allows you to prove a boolean predicate by assuming its negation and proving
    /// a contradiction. Equivalent to writing `if !b { /* proof here */; assert(false); }`
    /// but is more concise and documents intent.
    ///
    /// ```rust
    /// assert_by_contradiction!(b, {
    ///     // assume !b here
    ///     // prove `false`
    /// });
    /// ```
    #[macro_export]
    macro_rules! assert_by_contradiction_macro {
        ($predicate : expr, $bblock : block) =>
        {
            :: builtin ::
            assert_by($predicate,
                      {
                          if! $predicate
                          { $bblock crate :: pervasive :: assert(false) ; }
                      }) ;
        }
    }
    #[macro_export]
    macro_rules! assert_by_contradiction {
        ($($a : tt) *) =>
        {
            verus_proof_macro_exprs!
            (assert_by_contradiction_macro! ($($a) *))
        }
    }
}
pub mod impl_u {
    pub mod l0 {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use modes::*;
        use seq::*;
        use option::{*, Option::*};
        use map::*;
        use set::*;
        use set_lib::*;
        use crate::impl_u::lib;
        use vec::*;
        use crate::definitions_t::{MemRegion, overlap, between, Arch, aligned,
                                   PageTableEntry, Flags};
        use result::{*, Result::*};
        pub struct PageTableContents {
            pub map: Map<nat, PageTableEntry>,
            pub arch: Arch,
            pub lower: nat,
            pub upper: nat,
        }
        impl PageTableContents { }
    }
    pub mod l1 {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use modes::*;
        use seq::*;
        use seq_lib::*;
        use option::{*, Option::*};
        use map::*;
        use set::*;
        use set_lib::*;
        use vec::*;
        use crate::definitions_t::{new_seq, lemma_new_seq};
        use crate::impl_u::lib;
        use crate::impl_u::indexing;
        use result::{*, Result::*};
        use crate::definitions_t::{MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS,
                                   MAX_ENTRY_SIZE};
        use crate::definitions_t::{MemRegion, overlap, Arch, between, aligned,
                                   PageTableEntry, Flags};
        use crate::impl_u::l0::{self, ambient_arith, ambient_lemmas1};
        #[proof]
        pub enum NodeEntry {
            Directory(Directory),
            Page(PageTableEntry),
            Empty(),
        }
        #[automatically_derived]
        impl NodeEntry { }
        #[proof]
        pub struct Directory {
            pub entries: Seq<NodeEntry>,
            pub layer: nat,
            pub base_vaddr: nat,
            pub arch: Arch,
        }
        impl Directory { }
        impl <A, B> Result<A, B> { }
        impl <A> Result<A, A> { }
    }
    pub mod l2_impl {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use modes::*;
        use seq::*;
        use option::{*, Option::*};
        use map::*;
        use set::*;
        use set_lib::*;
        use seq_lib::*;
        use vec::*;
        use result::{*, Result::*};
        use crate::definitions_t::{Arch, ArchExec, MemRegion, MemRegionExec,
                                   PageTableEntry, PageTableEntryExec, Flags,
                                   overlap, between, aligned, aligned_exec,
                                   new_seq, lemma_new_seq, MapResult,
                                   UnmapResult, candidate_mapping_in_bounds};
        use crate::definitions_t::{x86_arch, MAX_BASE, MAX_NUM_ENTRIES,
                                   MAX_NUM_LAYERS, MAX_ENTRY_SIZE, WORD_SIZE,
                                   PAGE_SIZE, MAXPHYADDR, MAXPHYADDR_BITS,
                                   L1_ENTRY_SIZE, L2_ENTRY_SIZE,
                                   L3_ENTRY_SIZE};
        use crate::impl_u::l1;
        use crate::impl_u::l0::{ambient_arith};
        use crate::mem_t as mem;
        use crate::mem_t::{word_index_spec};
        use crate::impl_u::indexing;
        macro_rules! bit { ($v : expr) => { 1u64 << $v } }
        macro_rules! bitmask_inc {
            ($low : expr, $high : expr) =>
            { (! (! 0u64 << (($high + 1u64) - $low))) << $low }
        }
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_P: u64 = 1u64 << 0u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_RW: u64 = 1u64 << 1u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_US: u64 = 1u64 << 2u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_PWT: u64 = 1u64 << 3u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_PCD: u64 = 1u64 << 4u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_A: u64 = 1u64 << 5u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_FLAG_XD: u64 = 1u64 << 63u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_ADDR: u64 =
            (!(!0u64 << ((MAXPHYADDR_BITS + 1u64) - 12u64))) << 12u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_PG_FLAG_D: u64 = 1u64 << 6u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_PG_FLAG_G: u64 = 1u64 << 8u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_PG_FLAG_PAT: u64 = 1u64 << 12u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L1_PG_FLAG_PS: u64 = 1u64 << 7u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L2_PG_FLAG_PS: u64 = 1u64 << 7u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L3_PG_FLAG_PAT: u64 = 1u64 << 7u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_DIR_ADDR: u64 = MASK_ADDR;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L1_PG_ADDR: u64 =
            (!(!0u64 << ((MAXPHYADDR_BITS + 1u64) - 30u64))) << 30u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L2_PG_ADDR: u64 =
            (!(!0u64 << ((MAXPHYADDR_BITS + 1u64) - 21u64))) << 21u64;
        #[verifier(verus_macro)]
        #[verifier(publish)]
        pub const MASK_L3_PG_ADDR: u64 =
            (!(!0u64 << ((MAXPHYADDR_BITS + 1u64) - 12u64))) << 12u64;
        #[spec]
        pub enum GhostPageDirectoryEntry {
            Directory {
                addr: usize,
                #[doc =
                  " Present; must be 1 to map a page or reference a directory"]
                flag_P: bool,
                #[doc =
                  " Read/write; if 0, writes may not be allowed to the page controlled by this entry"]
                flag_RW: bool,
                #[doc =
                  " User/supervisor; user-mode accesses are not allowed to the page controlled by this entry"]
                flag_US: bool,
                #[doc = " Page-level write-through"]
                flag_PWT: bool,
                #[doc = " Page-level cache disable"]
                flag_PCD: bool,
                #[doc =
                  " Accessed; indicates whether software has accessed the page referenced by this entry"]
                flag_A: bool,
                #[doc =
                  " If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from"]
                #[doc =
                  " the page controlled by this entry); otherwise, reserved (must be 0)"]
                flag_XD: bool,
            },
            Page {
                addr: usize,
                #[doc =
                  " Present; must be 1 to map a page or reference a directory"]
                flag_P: bool,
                #[doc =
                  " Read/write; if 0, writes may not be allowed to the page controlled by this entry"]
                flag_RW: bool,
                #[doc =
                  " User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry"]
                flag_US: bool,
                #[doc = " Page-level write-through"]
                flag_PWT: bool,
                #[doc = " Page-level cache disable"]
                flag_PCD: bool,
                #[doc =
                  " Accessed; indicates whether software has accessed the page referenced by this entry"]
                flag_A: bool,
                #[doc =
                  " Dirty; indicates whether software has written to the page referenced by this entry"]
                flag_D: bool,
                #[doc =
                  " Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise"]
                flag_G: bool,
                #[doc =
                  " Indirectly determines the memory type used to access the page referenced by this entry"]
                flag_PAT: bool,
                #[doc =
                  " If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from"]
                #[doc =
                  " the page controlled by this entry); otherwise, reserved (must be 0)"]
                flag_XD: bool,
            },
            Empty,
        }
        #[automatically_derived]
        impl GhostPageDirectoryEntry { }
        #[repr(transparent)]
        pub struct PageDirectoryEntry {
            pub entry: u64,
            #[spec]
            pub layer: std::marker::PhantomData<nat>,
        }
        impl PageDirectoryEntry {
            #[verifier(verus_macro)]
            pub fn new_page_entry(layer: usize, pte: PageTableEntryExec)
             -> Self {
                Self::new_entry(layer, pte.frame.base as u64, true,
                                pte.flags.is_writable,
                                pte.flags.is_supervisor, false, false,
                                pte.flags.disable_execute)
            }
            #[verifier(verus_macro)]
            pub fn new_dir_entry(layer: usize, address: u64) -> Self {
                Self::new_entry(layer, address, false, true, true, false,
                                false, false)
            }
            #[verifier(verus_macro)]
            pub fn new_entry(layer: usize, address: u64, is_page: bool,
                             is_writable: bool, is_supervisor: bool,
                             is_writethrough: bool, disable_cache: bool,
                             disable_execute: bool) -> PageDirectoryEntry {
                let e =
                    PageDirectoryEntry{entry:
                                           {
                                               address | MASK_FLAG_P |
                                                   if is_page && layer != 3 {
                                                       MASK_L1_PG_FLAG_PS
                                                   } else { 0 } |
                                                   if is_writable {
                                                       MASK_FLAG_RW
                                                   } else { 0 } |
                                                   if is_supervisor {
                                                       MASK_FLAG_US
                                                   } else { 0 } |
                                                   if is_writethrough {
                                                       MASK_FLAG_PWT
                                                   } else { 0 } |
                                                   if disable_cache {
                                                       MASK_FLAG_PCD
                                                   } else { 0 } |
                                                   if disable_execute {
                                                       MASK_FLAG_XD
                                                   } else { 0 }
                                           },
                                       layer: std::marker::PhantomData,};

                #[verifier(proof_block)]
                { }
                e
            }
            #[verifier(verus_macro)]
            pub fn address(&self) -> u64 { self.entry & MASK_ADDR }
            #[verifier(verus_macro)]
            pub fn is_mapping(&self) -> bool {
                (self.entry & MASK_FLAG_P) == MASK_FLAG_P
            }
            #[verifier(verus_macro)]
            pub fn is_page(&self, layer: usize) -> bool {
                (layer == 3) ||
                    ((self.entry & MASK_L1_PG_FLAG_PS) == MASK_L1_PG_FLAG_PS)
            }
            #[verifier(verus_macro)]
            pub fn is_dir(&self, layer: usize) -> bool {
                !self.is_page(layer)
            }
        }
        pub struct PTDir {
            pub region: MemRegion,
            pub entries: Seq<Option<PTDir>>,
            #[doc =
              " reflexive-transitive closure of `region` over `entries`"]
            pub used_regions: Set<MemRegion>,
        }
        pub struct PageTable {
            pub memory: mem::PageTableMemory,
            pub arch: ArchExec,
            pub ghost_pt: Ghost<PTDir>,
        }
        impl PageTable {
            #[doc = " Get the entry at address ptr + i * WORD_SIZE"]
            #[verifier(nonlinear)]
            #[verifier(verus_macro)]
            fn entry_at(&self, layer: usize, ptr: usize, i: usize,
                        pt: Ghost<PTDir>) -> PageDirectoryEntry {

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };
                PageDirectoryEntry{entry:
                                       self.memory.read(ptr + i * WORD_SIZE,
                                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec()),
                                   std::marker::PhantomData,}
            }
            #[allow(unused_parens)]
            #[verifier(verus_macro)]
            fn resolve_aux(&self, layer: usize, ptr: usize, base: usize,
                           vaddr: usize, pt: Ghost<PTDir>)
             -> (Result<usize, ()>) {
                let idx: usize =
                    self.arch.index_for_vaddr(layer, base, vaddr);
                let entry = self.entry_at(layer, ptr, idx, pt);
                let interp: Ghost<l1::Directory> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                #[verifier(proof_block)]
                { }
                if entry.is_mapping() {
                    let entry_base: usize =
                        self.arch.entry_base(layer, base, idx);

                    #[verifier(proof_block)]
                    { }
                    if entry.is_dir(layer) {

                        #[verifier(proof_block)]
                        { };
                        let dir_addr = entry.address() as usize;

                        #[verifier(proof_block)]
                        { };
                        let dir_pt: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { }
                        let res =
                            self.resolve_aux(layer + 1, dir_addr, entry_base,
                                             vaddr, dir_pt);

                        #[verifier(proof_block)]
                        { };
                        res
                    } else {

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        let offset: usize = vaddr - entry_base;

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        let res = Ok(entry.address() as usize + offset);

                        #[verifier(proof_block)]
                        { };
                        res
                    }
                } else {

                    #[verifier(proof_block)]
                    { };

                    #[verifier(proof_block)]
                    { };

                    #[verifier(proof_block)]
                    { };
                    Err(())
                }
            }
            #[allow(unused_parens)]
            #[verifier(verus_macro)]
            fn resolve(&self, vaddr: usize) -> (Result<usize, ()>) {

                #[verifier(proof_block)]
                { }
                let (cr3_region, cr3) = self.memory.cr3();
                let res = self.resolve_aux(0, cr3, 0, vaddr, self.ghost_pt);
                res
            }
            #[verifier(spinoff_prover)]
            #[allow(unused_parens)]
            #[verifier(verus_macro)]
            fn map_frame_aux(&mut self, layer: usize, ptr: usize, base: usize,
                             vaddr: usize, pte: PageTableEntryExec,
                             pt: Ghost<PTDir>)
             -> (Result<Ghost<(PTDir, Set<MemRegion>)>, ()>) {
                let idx: usize =
                    self.arch.index_for_vaddr(layer, base, vaddr);
                let idxg: Ghost<usize> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                let entry = self.entry_at(layer, ptr, idx, pt);
                let interp: Ghost<l1::Directory> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                #[verifier(proof_block)]
                { { }; }
                let entry_base: usize =
                    self.arch.entry_base(layer, base, idx);

                #[verifier(proof_block)]
                { }
                if entry.is_mapping() {
                    if entry.is_dir(layer) {
                        if self.arch.entry_size(layer) == pte.frame.size {

                            #[verifier(proof_block)]
                            { };
                            Err(())
                        } else {
                            let dir_addr = entry.address() as usize;

                            #[verifier(proof_block)]
                            { };
                            let dir_pt: Ghost<PTDir> =
                                #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                            #[verifier(proof_block)]
                            { };
                            match self.map_frame_aux(layer + 1, dir_addr,
                                                     entry_base, vaddr, pte,
                                                     dir_pt) {
                                Ok(rec_res) => {
                                    let dir_pt_res: Ghost<PTDir> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                    let new_regions: Ghost<Set<MemRegion>> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    let pt_res: Ghost<PTDir> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    let ptrg: Ghost<usize> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { { } };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { { } };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { { } };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { { } };

                                    #[verifier(proof_block)]
                                    { { } };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    let res: Ghost<(PTDir, Set<MemRegion>)> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                    Ok(res)
                                }
                                Err(e) => {

                                    #[verifier(proof_block)]
                                    { };
                                    Err(e)
                                }
                            }
                        }
                    } else {

                        #[verifier(proof_block)]
                        { };
                        Err(())
                    }
                } else {
                    if self.arch.entry_size(layer) == pte.frame.size {

                        #[verifier(proof_block)]
                        { { }; }
                        let new_page_entry =
                            PageDirectoryEntry::new_page_entry(layer, pte);

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        let write_addr = ptr + idx * WORD_SIZE;
                        let pwmem: Ghost<mem::PageTableMemory> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                        self.memory.write(write_addr,
                                          #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec(),
                                          new_page_entry.entry);

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        let ptrg: Ghost<usize> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { { } };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { { } };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { { } };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { }

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        Ok(#[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec())
                    } else {
                        let new_dir_region = self.memory.alloc_page();
                        let new_dir_ptr = new_dir_region.base;
                        let new_dir_ptr_u64 = new_dir_ptr as u64;
                        let new_dir_pt: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { }
                        let new_dir_entry =
                            PageDirectoryEntry::new_dir_entry(layer,
                                                              new_dir_ptr_u64);

                        #[verifier(proof_block)]
                        { };
                        let write_addr = ptr + idx * WORD_SIZE;

                        #[verifier(proof_block)]
                        { };
                        self.memory.write(write_addr,
                                          #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec(),
                                          new_dir_entry.entry);
                        let pt_with_empty: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                        let self_with_empty: Ghost<Self> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { { }; { }; }

                        #[verifier(proof_block)]
                        { { } };
                        match self.map_frame_aux(layer + 1, new_dir_ptr,
                                                 entry_base, vaddr, pte,
                                                 new_dir_pt) {
                            Ok(rec_res) => {
                                let dir_pt_res: Ghost<PTDir> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                let dir_new_regions: Ghost<Set<MemRegion>> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                let pt_final: Ghost<PTDir> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                let new_regions: Ghost<Set<MemRegion>> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                #[verifier(proof_block)]
                                { { }; { }; }

                                #[verifier(proof_block)]
                                { ; ; { }; { }; }
                                Ok(#[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec())
                            }
                            Err(e) => {

                                #[verifier(proof_block)]
                                { };
                                Err(e)
                            }
                        }
                    }
                }
            }
            #[verifier(verus_macro)]
            pub fn map_frame(&mut self, vaddr: usize, pte: PageTableEntryExec)
             -> MapResult {

                #[verifier(proof_block)]
                { }
                let (cr3_region, cr3) = self.memory.cr3();
                match self.map_frame_aux(0, cr3, 0, vaddr, pte, self.ghost_pt)
                    {
                    Ok(res) => {
                        let pt_res: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                        let new_regions: Ghost<Set<MemRegion>> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { };
                        let self_before_pt_update: Ghost<Self> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                        self.ghost_pt = pt_res;

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { }
                        MapResult::Ok
                    }
                    Err(e) => {

                        #[verifier(proof_block)]
                        { }
                        MapResult::ErrOverlap
                    }
                }
            }
            #[verifier(verus_macro)]
            fn is_directory_empty(&self, layer: usize, ptr: usize,
                                  pt: Ghost<PTDir>) -> bool {

                #[verifier(proof_block)]
                { };
                let mut idx = 0;
                let num_entries = self.arch.num_entries(layer);
                while idx < num_entries {

                    #[verifier(proof_block)]
                    { };
                    let entry = self.entry_at(layer, ptr, idx, pt);
                    if entry.is_mapping() {

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };
                        return false;
                    }
                    idx = idx + 1;
                }
                true
            }
            #[verifier(spinoff_prover)]
            #[allow(unused_parens)]
            #[verifier(verus_macro)]
            fn unmap_aux(&mut self, layer: usize, ptr: usize, base: usize,
                         vaddr: usize, pt: Ghost<PTDir>)
             -> (Result<Ghost<(PTDir, Set<MemRegion>)>, ()>) {
                let idx: usize =
                    self.arch.index_for_vaddr(layer, base, vaddr);
                let idxg: Ghost<usize> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                let entry = self.entry_at(layer, ptr, idx, pt);
                let interp: Ghost<l1::Directory> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                #[verifier(proof_block)]
                { }
                let entry_base: usize =
                    self.arch.entry_base(layer, base, idx);

                #[verifier(proof_block)]
                { }
                if entry.is_mapping() {
                    if entry.is_dir(layer) {
                        let dir_addr = entry.address() as usize;

                        #[verifier(proof_block)]
                        { };
                        let dir_pt: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { };
                        match self.unmap_aux(layer + 1, dir_addr, entry_base,
                                             vaddr, dir_pt) {
                            Ok(rec_res) => {
                                let dir_pt_res: Ghost<PTDir> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                let removed_regions: Ghost<Set<MemRegion>> =
                                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                #[verifier(proof_block)]
                                { };

                                #[verifier(proof_block)]
                                { };

                                #[verifier(proof_block)]
                                { };

                                #[verifier(proof_block)]
                                { };
                                if self.is_directory_empty(layer + 1,
                                                           dir_addr,
                                                           dir_pt_res) {
                                    let write_addr = ptr + idx * WORD_SIZE;

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    self.memory.write(write_addr,
                                                      #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec(),
                                                      0u64);
                                    let pt_res: Ghost<PTDir> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                                    let res: Ghost<(PTDir, Set<MemRegion>)> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    Ok(res)
                                } else {
                                    let pt_res: Ghost<PTDir> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    let res: Ghost<(PTDir, Set<MemRegion>)> =
                                        #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };

                                    #[verifier(proof_block)]
                                    { };
                                    Ok(res)
                                }
                            }
                            Err(e) => {

                                #[verifier(proof_block)]
                                { };

                                #[verifier(proof_block)]
                                { };
                                Err(e)
                            }
                        }
                    } else {
                        if aligned_exec(vaddr, self.arch.entry_size(layer)) {
                            let write_addr = ptr + idx * WORD_SIZE;

                            #[verifier(proof_block)]
                            { };
                            self.memory.write(write_addr,
                                              #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec(),
                                              0u64);
                            let pt_res: Ghost<PTDir> = pt;
                            let removed_regions: Ghost<Set<MemRegion>> =
                                #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                            let res: Ghost<(PTDir, Set<MemRegion>)> =
                                #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };
                            Ok(res)
                        } else {

                            #[verifier(proof_block)]
                            { };

                            #[verifier(proof_block)]
                            { };
                            Err(())
                        }
                    }
                } else {

                    #[verifier(proof_block)]
                    { };

                    #[verifier(proof_block)]
                    { };
                    Err(())
                }
            }
            #[verifier(verus_macro)]
            pub fn unmap(&mut self, vaddr: usize) -> UnmapResult {

                #[verifier(proof_block)]
                { }
                let (cr3_region, cr3) = self.memory.cr3();
                match self.unmap_aux(0, cr3, 0, vaddr, self.ghost_pt) {
                    Ok(res) => {
                        let pt_res: Ghost<PTDir> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();

                        #[verifier(proof_block)]
                        { };
                        let self_before_pt_update: Ghost<Self> =
                            #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                        self.ghost_pt = pt_res;

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { };

                        #[verifier(proof_block)]
                        { }
                        UnmapResult::Ok
                    }
                    Err(e) => {

                        #[verifier(proof_block)]
                        { }
                        UnmapResult::ErrNoSuchMapping
                    }
                }
            }
        }
    }
    pub mod l2_refinement {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use modes::*;
        use seq::*;
        use option::{*, Option::*};
        use map::*;
        use set::*;
        use set_lib::*;
        use seq_lib::*;
        use vec::*;
        use crate::mem_t as mem;
        use result::{*, Result::*};
        use crate::definitions_t::{x86_arch, x86_arch_exec,
                                   x86_arch_exec_spec, MAX_BASE,
                                   MAX_NUM_ENTRIES, MAX_NUM_LAYERS,
                                   MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE,
                                   MAXPHYADDR, MAXPHYADDR_BITS, L0_ENTRY_SIZE,
                                   L1_ENTRY_SIZE, L2_ENTRY_SIZE,
                                   L3_ENTRY_SIZE, candidate_mapping_in_bounds,
                                   aligned,
                                   candidate_mapping_overlaps_existing_vmem};
        use crate::impl_u::l1;
        use crate::impl_u::l0::{ambient_arith};
        use crate::spec_t::impl_spec;
        use crate::impl_u::l2_impl;
        use crate::impl_u::spec_pt;
        use crate::definitions_t::{PageTableEntryExec, MapResult,
                                   UnmapResult};
        use crate::spec_t::hardware::interp_pt_mem;
        pub struct PageTableImpl {
        }
        impl impl_spec::PTImpl for PageTableImpl {
            #[verifier(verus_macro)]
            fn implspec_map_frame(&self, memory: mem::PageTableMemory,
                                  base: usize, pte: PageTableEntryExec)
             -> (MapResult, mem::PageTableMemory) {

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };
                let ghost_pt: Ghost<l2_impl::PTDir> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                let mut page_table =
                    l2_impl::PageTable{memory: memory,
                                       arch: x86_arch_exec(),
                                       ghost_pt: ghost_pt,};

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { { } };

                #[verifier(proof_block)]
                { }

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };
                let old_page_table: Ghost<l2_impl::PageTable> =
                    #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec();
                let res = page_table.map_frame(base, pte);

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { };

                #[verifier(proof_block)]
                { { }; }
                (res, page_table.memory)
            }
            #[verifier(verus_macro)]
            fn implspec_unmap(&self, memory: mem::PageTableMemory,
                              base: usize)
             -> (UnmapResult, mem::PageTableMemory) {

                #[verifier(proof_block)]
                { };
                (UnmapResult::Ok, memory)
            }
        }
    }
    pub mod spec_pt {
        #![allow(unused_imports)]
        use crate::pervasive::*;
        use builtin::*;
        use builtin_macros::*;
        use seq::*;
        use map::*;
        use option::{*, Option::*};
        use crate::impl_u::l0;
        use crate::definitions_t::{PageTableEntry, MapResult, UnmapResult,
                                   ResolveResult, Arch, overlap, MemRegion,
                                   aligned, between,
                                   candidate_mapping_in_bounds,
                                   candidate_mapping_overlaps_existing_vmem,
                                   candidate_mapping_overlaps_existing_pmem};
        use crate::definitions_t::{PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE,
                                   L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE};
        pub struct PageTableVariables {
            pub map: Map<nat, PageTableEntry>,
        }
        impl PageTableVariables { }
        pub enum PageTableStep {
            Map {
                vaddr: nat,
                pte: PageTableEntry,
                result: MapResult,
            },
            Unmap {
                vaddr: nat,
                result: UnmapResult,
            },
            Resolve {
                vaddr: nat,
                pte: Option<(nat, PageTableEntry)>,
                result: ResolveResult,
            },
            Stutter,
        }
    }
    pub mod lib {
        #[allow(unused_imports)]
        use builtin::*;
        #[allow(unused_imports)]
        use builtin_macros::*;
        #[macro_use]
        #[allow(unused_imports)]
        use crate::pervasive::*;
        #[allow(unused_imports)]
        use crate::definitions_t::aligned;
    }
    pub mod indexing {
        #![allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;
        use crate::pervasive::*;
        use modes::*;
        use seq::*;
        use option::{*, Option::*};
        use map::*;
        use set::*;
        use set_lib::*;
        use vec::*;
        use result::{*, Result::*};
        use crate::impl_u::lib;
        use crate::definitions_t::{aligned, between};
    }
}
pub mod definitions_t {
    #![allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;
    use crate::pervasive::*;
    use modes::*;
    use seq::*;
    use option::{*, Option::*};
    use map::*;
    use set::*;
    use set_lib::*;
    use vec::*;
    use result::{*, Result::*};
    use crate::impl_u::lib;
    use crate::impl_u::indexing;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const PT_BOUND_HIGH: usize = 512 * 512 * 1024 * 1024 * 1024;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;
    #[verifier(verus_macro)]
    #[exec]
    pub fn aligned_exec(addr: usize, size: usize) -> bool { addr % size == 0 }
    pub enum MapResult { ErrOverlap, Ok, }
    #[automatically_derived]
    impl MapResult { }
    pub enum UnmapResult { ErrNoSuchMapping, Ok, }
    #[automatically_derived]
    impl UnmapResult { }
    pub enum ResolveResult { ErrUnmapped, PAddr(nat), }
    #[automatically_derived]
    impl ResolveResult { }
    pub enum LoadResult { Pagefault, Value(nat), }
    #[automatically_derived]
    impl LoadResult { }
    pub enum StoreResult { Pagefault, Ok, }
    #[automatically_derived]
    impl StoreResult { }
    pub enum RWOp {
        Store {
            new_value: nat,
            result: StoreResult,
        },
        Load {
            is_exec: bool,
            result: LoadResult,
        },
    }
    #[automatically_derived]
    impl RWOp { }
    pub struct MemRegion {
        pub base: nat,
        pub size: nat,
    }
    impl MemRegion { }
    #[verifier(verus_macro)]
    fn overlap_sanity_check() {

        #[verifier(proof_block)]
        { };

        #[verifier(proof_block)]
        { };

        #[verifier(proof_block)]
        { };

        #[verifier(proof_block)]
        { };

        #[verifier(proof_block)]
        { };

        #[verifier(proof_block)]
        { };
    }
    pub struct MemRegionExec {
        pub base: usize,
        pub size: usize,
    }
    impl MemRegionExec { }
    pub struct Flags {
        pub is_writable: bool,
        pub is_supervisor: bool,
        pub disable_execute: bool,
    }
    pub struct PageTableEntry {
        pub frame: MemRegion,
        pub flags: Flags,
    }
    pub struct PageTableEntryExec {
        pub frame: MemRegionExec,
        pub flags: Flags,
    }
    impl PageTableEntryExec { }
    pub struct ArchLayerExec {
        #[doc = " Address space size mapped by a single entry at this layer"]
        pub entry_size: usize,
        #[doc = " Number of entries of at this layer"]
        pub num_entries: usize,
    }
    impl Clone for ArchLayerExec {
        #[verifier(verus_macro)]
        fn clone(&self) -> Self {
            ArchLayerExec{entry_size: self.entry_size,
                          num_entries: self.num_entries,}
        }
    }
    impl ArchLayerExec { }
    pub struct ArchExec {
        pub layers: Vec<ArchLayerExec>,
    }
    impl ArchExec {
        #[verifier(verus_macro)]
        pub fn entry_size(&self, layer: usize) -> usize {
            self.layers.index(layer).entry_size
        }
        #[verifier(verus_macro)]
        pub fn num_entries(&self, layer: usize) -> usize {
            self.layers.index(layer).num_entries
        }
        #[verifier(verus_macro)]
        pub fn index_for_vaddr(&self, layer: usize, base: usize, vaddr: usize)
         -> usize {
            let es = self.entry_size(layer);

            #[verifier(proof_block)]
            { };
            let offset = vaddr - base;

            #[verifier(proof_block)]
            { };

            #[verifier(proof_block)]
            { };
            let res = offset / es;

            #[verifier(proof_block)]
            { { } }
            res
        }
        #[verifier(nonlinear)]
        #[verifier(verus_macro)]
        pub fn entry_base(&self, layer: usize, base: usize, idx: usize)
         -> usize {

            #[verifier(proof_block)]
            { }
            base + idx * self.entry_size(layer)
        }
        #[verifier(verus_macro)]
        pub fn next_entry_base(&self, layer: usize, base: usize, idx: usize)
         -> usize {

            #[verifier(proof_block)]
            { { }; }
            let offset = (idx + 1) * self.entry_size(layer);

            #[verifier(proof_block)]
            { { }; }
            base + offset
        }
    }
    pub struct ArchLayer {
        #[doc = " Address space size mapped by a single entry at this layer"]
        pub entry_size: nat,
        #[doc = " Number of entries at this layer"]
        pub num_entries: nat,
    }
    pub struct Arch {
        pub layers: Seq<ArchLayer>,
    }
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const MAXPHYADDR_BITS: u64 = 52;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const WORD_SIZE: usize = 8;
    #[verifier(verus_macro)]
    #[verifier(publish)]
    pub const PAGE_SIZE: usize = 4096;
    impl Arch { }
    #[verifier(external_body)]
    #[verifier(verus_macro)]
    #[exec]
    pub fn x86_arch_exec() -> ArchExec {
        ArchExec{layers:
                     Vec{vec:
                             <[_]>::into_vec(box
                                                 [ArchLayerExec{entry_size:
                                                                    L0_ENTRY_SIZE,
                                                                num_entries:
                                                                    512,},
                                                  ArchLayerExec{entry_size:
                                                                    L1_ENTRY_SIZE,
                                                                num_entries:
                                                                    512,},
                                                  ArchLayerExec{entry_size:
                                                                    L2_ENTRY_SIZE,
                                                                num_entries:
                                                                    512,},
                                                  ArchLayerExec{entry_size:
                                                                    L3_ENTRY_SIZE,
                                                                num_entries:
                                                                    512,}]),},}
    }
}
pub mod mem_t {
    #![allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;
    use crate::pervasive::*;
    use modes::*;
    use seq::*;
    use option::{*, Option::*};
    use map::*;
    use set::*;
    use set_lib::*;
    use vec::*;
    use result::{*, Result::*};
    use crate::definitions_t::{Arch, ArchExec, MemRegion, MemRegionExec,
                               overlap, between, aligned, new_seq,
                               PageTableEntry};
    use crate::definitions_t::{MAX_BASE, MAX_NUM_ENTRIES, MAX_NUM_LAYERS,
                               MAX_ENTRY_SIZE, WORD_SIZE, PAGE_SIZE,
                               MAXPHYADDR, MAXPHYADDR_BITS};
    use crate::impl_u::l1;
    use crate::impl_u::l0::{ambient_arith};
    use crate::impl_u::indexing;
    #[verifier(verus_macro)]
    pub fn word_index(offset: usize) -> usize { offset / WORD_SIZE }
    pub struct TLB {
    }
    impl TLB {
        #[doc = " Invalidates any TLB entries containing `vbase`."]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn invalidate_entry(&mut self, vbase: usize) { unreached() }
    }
    #[verifier(external_body)]
    pub struct PageTableMemory {
        #[doc =
          " `ptr` is the starting address of the physical memory linear mapping"]
        ptr: *mut u64,
    }
    impl PageTableMemory {
        #[doc =
          " `cr3` returns the physical address at which the layer 0 page directory is mapped as well as"]
        #[doc = " the corresponding memory region"]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn cr3(&self) -> (Ghost<MemRegion>, usize) { unreached() }
        #[doc = " Allocates one page and returns its physical address"]
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn alloc_page(&mut self) -> MemRegionExec { unreached() }
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn write(&mut self, offset: usize, region: Ghost<MemRegion>,
                     value: u64) {
            let word_offset: isize = word_index(offset) as isize;
            unsafe { self.ptr.offset(word_offset).write(value); }
        }
        #[verifier(external_body)]
        #[verifier(verus_macro)]
        pub fn read(&self, offset: usize, region: Ghost<MemRegion>) -> u64 {
            let word_offset: isize = word_index(offset) as isize;
            unsafe { self.ptr.offset(word_offset).read() }
        }
    }
}
pub mod spec_t {
    pub mod hlspec {
        #![allow(unused_imports)]
        use crate::pervasive::*;
        use seq::*;
        use set::*;
        use crate::*;
        use builtin::*;
        use builtin_macros::*;
        use state_machines_macros::*;
        use map::*;
        use crate::definitions_t::{between, overlap, MemRegion,
                                   PageTableEntry, Flags, RWOp, LoadResult,
                                   StoreResult, MapResult, UnmapResult,
                                   ResolveResult, aligned,
                                   candidate_mapping_in_bounds,
                                   candidate_mapping_overlaps_existing_vmem};
        use crate::definitions_t::{PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE,
                                   L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE,
                                   WORD_SIZE};
        use option::{*, Option::None, Option::Some};
        use crate::mem_t::{word_index_spec};
        pub struct AbstractConstants {
            pub phys_mem_size: nat,
        }
        pub struct AbstractVariables {
            #[doc = " Word-indexed virtual memory"]
            pub mem: Map<nat, nat>,
            #[doc =
              " `mappings` constrains the domain of mem and tracks the flags. We could instead move the"]
            #[doc =
              " flags into `map` as well and write the specification exclusively in terms of `map` but that"]
            #[doc =
              " also makes some of the preconditions awkward, e.g. full mappings have the same flags, etc."]
            pub mappings: Map<nat, PageTableEntry>,
        }
        pub enum AbstractStep {
            ReadWrite {
                vaddr: nat,
                op: RWOp,
                pte: Option<(nat, PageTableEntry)>,
            },
            Map {
                vaddr: nat,
                pte: PageTableEntry,
                result: MapResult,
            },
            Unmap {
                vaddr: nat,
                result: UnmapResult,
            },
            Resolve {
                vaddr: nat,
                pte: Option<(nat, PageTableEntry)>,
                result: ResolveResult,
            },
            Stutter,
        }
    }
    pub mod hardware {
        #![allow(unused_imports)]
        use crate::pervasive::*;
        use builtin::*;
        use builtin_macros::*;
        use state_machines_macros::*;
        use map::*;
        use seq::*;
        #[allow(unused_imports)]
        use set::*;
        use crate::definitions_t::{PageTableEntry, RWOp, LoadResult,
                                   StoreResult, between, aligned};
        use crate::mem_t as mem;
        use crate::mem_t::{word_index_spec};
        use crate::impl_u::l0;
        use option::{*, Option::*};
        pub struct HWVariables {
            #[doc = " Word-indexed physical memory"]
            pub mem: Seq<nat>,
            pub pt_mem: mem::PageTableMemory,
            pub tlb: Map<nat, PageTableEntry>,
        }
        pub enum HWStep {
            ReadWrite {
                vaddr: nat,
                paddr: nat,
                op: RWOp,
                pte: Option<(nat, PageTableEntry)>,
            },
            PTMemOp,
            TLBFill {
                vaddr: nat,
                pte: PageTableEntry,
            },
            TLBEvict {
                vaddr: nat,
            },
        }
        #[automatically_derived]
        impl HWStep { }
    }
    pub mod os {
        #![allow(unused_imports)]
        use crate::pervasive::*;
        use builtin::*;
        use builtin_macros::*;
        use map::*;
        use seq::*;
        use set_lib::*;
        use option::{*, Option::*};
        use crate::spec_t::{hardware, hlspec};
        use crate::impl_u::spec_pt;
        use crate::definitions_t::{between, MemRegion, overlap,
                                   PageTableEntry, RWOp, MapResult,
                                   UnmapResult, ResolveResult, Arch, aligned,
                                   new_seq,
                                   candidate_mapping_overlaps_existing_vmem,
                                   candidate_mapping_overlaps_existing_pmem};
        use crate::definitions_t::{PT_BOUND_LOW, PT_BOUND_HIGH, L3_ENTRY_SIZE,
                                   L2_ENTRY_SIZE, L1_ENTRY_SIZE, PAGE_SIZE,
                                   WORD_SIZE};
        use crate::mem_t::{word_index_spec};
        use option::{*, Option::*};
        pub struct OSVariables {
            pub system: hardware::HWVariables,
        }
        impl OSVariables { }
        pub enum OSStep {
            HW {
                step: hardware::HWStep,
            },
            Map {
                vaddr: nat,
                pte: PageTableEntry,
                result: MapResult,
            },
            Unmap {
                vaddr: nat,
                result: UnmapResult,
            },
            Resolve {
                vaddr: nat,
                pte: Option<(nat, PageTableEntry)>,
                result: ResolveResult,
            },
        }
        impl OSStep { }
    }
    pub mod impl_spec {
        #![allow(unused_imports)]
        use builtin_macros::*;
        use builtin::*;
        use crate::spec_t::hlspec;
        use crate::pervasive::*;
        use crate::definitions_t::{PageTableEntryExec, MapResult,
                                   UnmapResult};
        use crate::impl_u::spec_pt;
        use crate::spec_t::hardware::interp_pt_mem;
        use crate::mem_t as mem;
        use crate::impl_u::l2_impl;
        pub struct PTState {
            pub memory: mem::PageTableMemory,
        }
        pub trait PTImpl {
            #[verifier(verus_macro)]
            fn implspec_map_frame(&self, memory: mem::PageTableMemory,
                                  base: usize, pte: PageTableEntryExec)
            -> (MapResult, mem::PageTableMemory);
            #[verifier(verus_macro)]
            fn implspec_unmap(&self, memory: mem::PageTableMemory,
                              base: usize)
            -> (UnmapResult, mem::PageTableMemory);
        }
    }
}
fn main() { }
verification results:: verified: 35 errors: 0
total-time:           20789 ms
    rust-time:            18441 ms
        init-and-types:        7054 ms
        lifetime-time:         5481 ms
        compile-time:          5904 ms
    vir-time:               740 ms
        rust-to-vir:            399 ms
        verify:                 297 ms
        erase:                   16 ms
    air-time:               932 ms
    smt-time:               659 ms
        smt-init:                 0 ms
        smt-run:                659 ms
