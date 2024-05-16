// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};
use smallvec::{smallvec, SmallVec};

type ValueVec = SmallVec<[Word; 1]>;

/// Owned value.
pub struct ValueOwned {
    width: WidthInt,
    words: ValueVec,
}

impl ValueOwned {
    /// Parse a string of 1s and 0s. The width of the resulting value is the number of digits.
    pub fn from_bit_str(value: &str) -> Self {
        let bits = value.len();
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS as usize)];
        crate::io::strings::from_bit_str(value, &mut words);
        Self {
            width: bits as WidthInt,
            words,
        }
    }

    pub fn zero(width: WidthInt) -> Self {
        let words = smallvec![0; width.div_ceil(WidthInt::BITS) as usize];
        Self { width, words }
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_int(value: &num_bigint::BigInt, bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bigint::from_big_int(value, bits, &mut words);
        Self { width: bits, words }
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_uint(value: &num_bigint::BigUint, bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bigint::from_big_uint(value, bits, &mut words);
        Self { width: bits, words }
    }
}

impl std::fmt::Debug for ValueOwned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueOwned({})", self.to_bit_str())
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigInt> for ValueOwned {
    fn from(value: &num_bigint::BigInt) -> Self {
        let bits = crate::io::bigint::count_big_int_bits(value);
        Self::from_big_int(value, bits)
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigUint> for ValueOwned {
    fn from(value: &num_bigint::BigUint) -> Self {
        let bits = crate::io::bigint::count_big_uint_bits(value);
        Self::from_big_uint(value, bits)
    }
}

pub struct ValueRef<'a> {
    width: WidthInt,
    words: &'a [Word],
}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueRef({})", self.to_bit_str())
    }
}

pub struct ValueMutRef<'a> {
    width: WidthInt,
    words: &'a mut [Word],
}

impl<'a> std::fmt::Debug for ValueMutRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueMutRef({})", self.to_bit_str())
    }
}

type WordIndex = u32;

#[derive(Debug)]
pub struct ValueIndexed {
    width: WidthInt,
    index: WordIndex,
}

pub trait ValueStorage {
    fn words(&self, index: WordIndex) -> &[Word];
    fn words_mut(&mut self, index: WordIndex) -> &mut [Word];
}

impl ValueIndexed {
    pub fn as_ref<'a>(&self, storage: &'a impl ValueStorage) -> ValueRef<'a> {
        ValueRef {
            width: self.width,
            words: storage.words(self.index),
        }
    }

    pub fn as_mut<'a>(&self, storage: &'a mut impl ValueStorage) -> ValueMutRef<'a> {
        ValueMutRef {
            width: self.width,
            words: storage.words_mut(self.index),
        }
    }
}

/// Abstracts over values no matter how they are stored.
pub trait Value {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];

    /// Convert to a string of 1s and 0s.
    fn to_bit_str(&self) -> String {
        crate::io::strings::to_bit_str(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_int(&self) -> num_bigint::BigInt {
        crate::io::bigint::to_big_int(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_uint(&self) -> num_bigint::BigUint {
        crate::io::bigint::to_big_uint(self.words())
    }
}

/// Abstracts over mutabkle values no matter how they are stored.
pub trait ValueMut: Value {
    fn words_mut(&mut self) -> &mut [Word];

    fn set_from_word(&mut self, value: Word) {
        if value > 0 {
            self.words_mut()[0] = value;
            crate::arithmetic::clear(&mut self.words_mut()[1..]);
        } else {
            crate::arithmetic::clear(self.words_mut());
        }
    }

    fn set_from_bit_str(&mut self, value: &str) {
        debug_assert_eq!(self.width() as usize, value.len());
        crate::io::strings::from_bit_str(value, self.words_mut());
    }

    #[cfg(feature = "bigint")]
    fn set_from_big_int(&mut self, value: &num_bigint::BigInt) {
        crate::io::bigint::from_big_int(value, self.width(), self.words_mut());
    }

    #[cfg(feature = "bigint")]
    fn set_from_big_uint(&mut self, value: &num_bigint::BigUint) {
        crate::io::bigint::from_big_uint(value, self.width(), self.words_mut());
    }
}

impl Value for ValueOwned {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}

impl ValueMut for ValueOwned {
    fn words_mut(&mut self) -> &mut [Word] {
        &mut self.words
    }
}

impl<'a> Value for ValueRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> Value for ValueMutRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> ValueMut for ValueMutRef<'a> {
    fn words_mut(&mut self) -> &mut [Word] {
        self.words
    }
}
