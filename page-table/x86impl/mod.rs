#[macro_export]
macro_rules! bit {
    ($x:expr) => {
        1 << $x
    };
}

pub mod paging;
