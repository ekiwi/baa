mod array;
mod bv;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

/// Wraps either an array or a bit vector value.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Array(ArrayValue),
    BitVec(BitVecValue),
}

pub use array::*;
pub use bv::*;
