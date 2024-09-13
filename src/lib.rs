// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod arithmetic;
pub(crate) mod io;
mod ops;
mod value;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

pub use arithmetic::mask;
pub use ops::{ArrayMutOps, ArrayOps, BitVecMutOps, BitVecOps, DENSE_ARRAY_MAX_INDEX_WIDTH};
pub use value::borrowed::{ArrayValueMutRef, ArrayValueRef, BitVecValueMutRef, BitVecValueRef};
pub use value::container::ValueRef;
pub use value::indexed::{
    ArrayValueIndex, BitVecValueIndex, IndexToMutRef, IndexToRef, ValueInterner,
};
pub use value::owned::{ArrayValue, BitVecValue};
