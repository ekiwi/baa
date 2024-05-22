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

use thiserror::Error;
#[derive(Debug, Error)]
pub enum Error {}

pub use ops::{BitVecMutOps, BitVecOps};
pub use value::borrowed::{BitVecValueMutRef, BitVecValueRef};
pub use value::indexed::{BitVecValueIndex, ValueStorage};
pub use value::owned::BitVecValue;
