// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Borrowed bit-vector and array values.

use crate::{
    ArrayMutOps, ArrayOps, ArrayValue, BitVecMutOps, BitVecOps, BitVecValue, WidthInt, Word,
};

/// Bit-vector value that does not own its storage.
#[derive(Clone, Copy)]
pub struct BitVecValueRef<'a> {
    pub(crate) width: WidthInt,
    pub(crate) words: &'a [Word],
}

impl<'a> BitVecValueRef<'a> {
    pub(crate) fn new(width: WidthInt, words: &'a [Word]) -> Self {
        Self { width, words }
    }
}

impl<'a> From<&'a BitVecValue> for BitVecValueRef<'a> {
    fn from(value: &'a BitVecValue) -> Self {
        Self::new(value.width, value.words.as_ref())
    }
}

impl<'a> std::fmt::Debug for BitVecValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitVecValueRef({})", self.to_bit_str())
    }
}

pub struct BitVecValueMutRef<'a> {
    pub(crate) width: WidthInt,
    pub(crate) words: &'a mut [Word],
}

impl<'a> BitVecValueMutRef<'a> {
    pub(crate) fn new(width: WidthInt, words: &'a mut [Word]) -> Self {
        Self { width, words }
    }
}

impl<'a> From<&'a mut BitVecValue> for BitVecValueMutRef<'a> {
    fn from(value: &'a mut BitVecValue) -> Self {
        Self::new(value.width, value.words.as_mut())
    }
}
impl<'a> std::fmt::Debug for BitVecValueMutRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitVecValueMutRef({})", self.to_bit_str())
    }
}

impl<'a> BitVecOps for BitVecValueRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> BitVecOps for BitVecValueMutRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> BitVecMutOps for BitVecValueMutRef<'a> {
    fn words_mut(&mut self) -> &mut [Word] {
        self.words
    }
}

/// Bit-vector array value that does not own its storage.
#[derive(Clone)]
pub struct ArrayValueRef<'a> {
    pub(crate) index_width: WidthInt,
    pub(crate) data_width: WidthInt,
    pub(crate) words: &'a [Word],
}

impl<'a> ArrayValueRef<'a> {
    pub(crate) fn new(index_width: WidthInt, data_width: WidthInt, words: &'a [Word]) -> Self {
        Self {
            index_width,
            data_width,
            words,
        }
    }
}

impl<'a> From<&'a ArrayValue> for ArrayValueRef<'a> {
    fn from(value: &'a ArrayValue) -> Self {
        Self::new(value.index_width, value.index_width, value.words.as_ref())
    }
}

impl<'a> std::fmt::Debug for ArrayValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ArrayValueRef(bv<{}> -> bv<{}>)",
            self.index_width, self.data_width
        )
    }
}

impl<'a> ArrayOps for ArrayValueRef<'a> {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }

    fn data_width(&self) -> WidthInt {
        self.data_width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

/// Mutable bit-vector array value that does not own its storage.
pub struct ArrayValueMutRef<'a> {
    pub(crate) index_width: WidthInt,
    pub(crate) data_width: WidthInt,
    pub(crate) words: &'a mut [Word],
}

impl<'a> ArrayValueMutRef<'a> {
    pub(crate) fn new(index_width: WidthInt, data_width: WidthInt, words: &'a mut [Word]) -> Self {
        Self {
            index_width,
            data_width,
            words,
        }
    }
}

impl<'a> From<&'a mut ArrayValue> for ArrayValueMutRef<'a> {
    fn from(value: &'a mut ArrayValue) -> Self {
        Self::new(
            value.index_width,
            value.index_width,
            value.words.as_mut_slice(),
        )
    }
}

impl<'a> std::fmt::Debug for ArrayValueMutRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ArrayValueMutRef(bv<{}> -> bv<{}>)",
            self.index_width, self.data_width
        )
    }
}

impl<'a> ArrayOps for ArrayValueMutRef<'a> {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }

    fn data_width(&self) -> WidthInt {
        self.data_width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> ArrayMutOps for ArrayValueMutRef<'a> {
    fn words_mut(&mut self) -> &mut [Word] {
        self.words
    }
}
