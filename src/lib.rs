// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod arithmetic;
pub(crate) mod io;
mod value;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

#[derive(Debug, Error)]
pub enum Error {}

use thiserror::Error;
pub use value::{
    BitVecMutOps, BitVecOps, BitVecValue, BitVecValueMutRef, BitVecValueRef,
    ValueIndexed, ValueStorage,
};
