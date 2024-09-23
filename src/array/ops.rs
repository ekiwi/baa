// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Traits for operations on arrays.

use crate::{BitVecValue, BitVecValueRef, WidthInt, Word};

pub const DENSE_ARRAY_MAX_INDEX_WIDTH: WidthInt = 48;

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
    // {
    //     let index = index.into();
    //     debug_assert!(self.index_width() <= DENSE_ARRAY_MAX_INDEX_WIDTH);
    //     debug_assert_eq!(self.index_width(), index.width());
    //     debug_assert_eq!(index.words().len(), 1);
    //     let start = self.words_per_element() * index.words()[0] as usize;
    //     let end = start + self.words_per_element();
    //     BitVecValueRef::new(self.data_width(), &self.words()[start..end])
    // }
    // fn is_equal<R: ArrayOps + ?Sized>(&self, rhs: &R) -> bool;

    // {
    //     debug_assert_eq!(self.index_width(), rhs.index_width());
    //     debug_assert_eq!(self.data_width(), rhs.data_width());
    //     self.words() == rhs.words()
    // }
}

/// Operations implemented by mutable array values with a dense representation.
pub trait ArrayMutOps: ArrayOps {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    );

    // {
    //     let index = index.into();
    //     debug_assert!(self.index_width() <= DENSE_ARRAY_MAX_INDEX_WIDTH);
    //     debug_assert_eq!(self.index_width(), index.width());
    //     debug_assert_eq!(index.words().len(), 1);
    //     let start = self.words_per_element() * index.words()[0] as usize;
    //     let end = start + self.words_per_element();
    //     let mut element =
    //         BitVecValueMutRef::new(self.data_width(), &mut self.words_mut()[start..end]);
    //     element.assign(data);
    // }

    // only performs well for dense arrays
    // fn assign<'a>(&mut self, value: impl Into<ArrayValueRef<'a>>) {
    //     let value = value.into();
    //     debug_assert_eq!(self.index_width(), value.index_width());
    //     debug_assert_eq!(self.data_width(), value.data_width());
    //     debug_assert_eq!(self.words_mut().len(), value.words().len());
    //     self.words_mut().copy_from_slice(value.words());
    // }
    /// sets all bits to zero
    fn clear(&mut self);

    // {
    //     self.words_mut().iter_mut().for_each(|w| {
    //         *w = 0;
    //     });
    // }
}
