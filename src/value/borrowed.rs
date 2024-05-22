// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Borrowed bit-vector values.

use crate::{BitVecMutOps, BitVecOps, WidthInt, Word};

/// Bit-vector value that does not own its storage.
pub struct BitVecValueRef<'a> {
    pub(crate) width: WidthInt,
    pub(crate) words: &'a [Word],
}

impl<'a> std::fmt::Debug for BitVecValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueRef({})", self.to_bit_str())
    }
}

pub struct BitVecValueMutRef<'a> {
    pub(crate) width: WidthInt,
    pub(crate) words: &'a mut [Word],
}

impl<'a> std::fmt::Debug for BitVecValueMutRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueMutRef({})", self.to_bit_str())
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
