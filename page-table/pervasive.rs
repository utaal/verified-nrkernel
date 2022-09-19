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
    pub struct Vec<A> {
        pub vec: alloc::vec::Vec<A>,
    }
    impl <A> Vec<A> {
        pub fn new() -> Self { Vec{vec: alloc::vec::Vec::new(),} }
        pub fn empty() -> Self { Vec::new() }
        pub fn push(&mut self, value: A) { self.vec.push(value); }
        pub fn pop(&mut self) -> A {
            unsafe { self.vec.pop().unwrap_unchecked() }
        }
        pub fn index(&self, i: usize) -> &A { &self.vec[i] }
        pub fn set(&mut self, i: usize, a: A) { self.vec[i] = a; }
        pub fn len(&self) -> usize { self.vec.len() }
    }
}
