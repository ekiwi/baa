// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Traits for operations on arrays.

use crate::{BitVecValue, BitVecValueRef, WidthInt, Word};

/// Operations implemented by read-only array values with a dense representation.
pub trait ArrayOps {
    fn index_width(&self) -> WidthInt;
    fn data_width(&self) -> WidthInt;
    #[inline]
    fn words_per_element(&self) -> usize {
        self.data_width().div_ceil(Word::BITS) as usize
    }
    #[inline]
    fn num_elements(&self) -> usize {
        1usize << self.index_width()
    }
    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue;
}

/// Operations implemented by mutable array values with a dense representation.
pub trait ArrayMutOps: ArrayOps {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    );

    /// sets all bits to zero
    fn clear(&mut self);
}
