// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Borrowed bit-vector and array values.

use crate::{BitVecMutOps, BitVecOps, BitVecValue, WidthInt, Word};
use std::borrow::Borrow;

/// Bit-vector value that does not own its storage.
#[derive(Clone, Copy, Hash)]
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

impl Borrow<BitVecValueRef> for BitVecValue {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVecMutOps, BitVecValue};
    use std::borrow::Borrow;
    use std::hash::{DefaultHasher, Hash, Hasher};

    /// Signature is copied from HashTable::get
    fn get_hash<Q: ?Sized>(key: &Q) -> u64
    where
        BitVecValue: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut hasher = DefaultHasher::new();
        key.borrow().hash(&mut hasher);
        hasher.finish()
    }

    fn check_hash(value: BitVecValue) {
        let value_hash = get_hash(&value);
        let re = BitVecValueRef::from(&value);
        let re_hash = get_hash(re);
        assert_eq!(value, re);
        assert_eq!(value_hash, re_hash);
    }

    #[test]
    fn borrowed_hash() {}
}
