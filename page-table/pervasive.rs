pub mod option {
    #[allow(unused_imports)]
    use crate::pervasive::*;
    pub enum Option<A> { None, Some(A), }
    #[automatically_derived]
    impl <A> Option<A> { }
    impl <A> Option<A> { }
}
pub mod result {
    #[allow(unused_imports)]
    pub enum Result<T, E> { Ok(T), Err(E), }
    #[automatically_derived]
    impl <T, E> Result<T, E> { }
}
pub mod vec {
    #[allow(unused_imports)]
    use crate::pervasive::*;
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
