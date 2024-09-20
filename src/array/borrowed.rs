// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::array::owned::ArrayValue;
use crate::{WidthInt, Word};

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
