mod array;
mod bv;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

pub use array::*;
pub use bv::*;
