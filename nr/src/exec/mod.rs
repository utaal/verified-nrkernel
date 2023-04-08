pub mod rwlock;
pub mod log;
pub mod replica;
pub mod context;
pub mod utils;

/// a simpe cache padding for the struct fields
#[repr(align(128))]
pub struct CachePadded<T>(pub T);