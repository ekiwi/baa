// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

mod borrowed;
mod indexed;
mod ops;
mod owned;

pub use borrowed::{ArrayValueMutRef, ArrayValueRef};
pub use indexed::ArrayValueIndex;
pub use ops::{ArrayMutOps, ArrayOps};
pub use owned::ArrayValue;
