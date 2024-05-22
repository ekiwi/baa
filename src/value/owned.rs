// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{BitVecMutOps, BitVecOps, WidthInt, Word};
use smallvec::{smallvec, SmallVec};

type ValueVec = SmallVec<[Word; 2]>;

/// Owned bit-vector value.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct BitVecValue {
    pub(crate) width: WidthInt,
    pub(crate) words: ValueVec,
}

const OWNED_TRUE: BitVecValue = BitVecValue {
    width: 1,
    words: SmallVec::from_const([1, 0]),
};
const OWNED_FALSE: BitVecValue = BitVecValue {
    width: 1,
    words: SmallVec::from_const([0, 0]),
};

impl BitVecValue {
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

    pub fn from_u64(value: u64, bits: WidthInt) -> Self {
        debug_assert_eq!(Word::BITS, 64);
        Self {
            width: bits as WidthInt,
            words: smallvec![value],
        }
    }

    pub fn from_bool(value: bool) -> Self {
        if value {
            Self::tru()
        } else {
            Self::fals()
        }
    }

    pub fn from_bytes_le(bytes: &[u8], bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bytes::from_bytes_le(bytes, bits, words.as_mut());
        Self { width: bits, words }
    }

    pub fn zero(width: WidthInt) -> Self {
        let words = smallvec![0; width.div_ceil(WidthInt::BITS) as usize];
        Self { width, words }
    }

    pub fn tru() -> Self {
        OWNED_TRUE
    }
    pub fn fals() -> Self {
        OWNED_FALSE
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

    #[cfg(feature = "fraction1")]
    pub fn from_fixed_point(
        value: &fraction::Fraction,
        bits: WidthInt,
        fraction_width: WidthInt,
    ) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::fraction::from_fixed_point(value, bits, fraction_width, &mut words);
        Self { width: bits, words }
    }
}

impl<V: BitVecOps> PartialEq<V> for BitVecValue {
    fn eq(&self, other: &V) -> bool {
        debug_assert!(!(other.width() == self.width) || other.words().len() == self.words.len());
        other.width() == self.width && other.words() == self.words.as_slice()
    }
}

impl Eq for BitVecValue {}

impl<V: BitVecOps> std::ops::Add<&V> for &BitVecValue {
    type Output = BitVecValue;

    fn add(self, rhs: &V) -> Self::Output {
        BitVecOps::add(self, rhs)
    }
}

impl<V: BitVecOps> std::ops::Sub<&V> for &BitVecValue {
    type Output = BitVecValue;

    fn sub(self, rhs: &V) -> Self::Output {
        BitVecOps::sub(self, rhs)
    }
}

impl std::fmt::Debug for BitVecValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueOwned({})", self.to_bit_str())
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigInt> for BitVecValue {
    fn from(value: &num_bigint::BigInt) -> Self {
        let bits = crate::io::bigint::count_big_int_bits(value);
        Self::from_big_int(value, bits)
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigUint> for BitVecValue {
    fn from(value: &num_bigint::BigUint) -> Self {
        let bits = crate::io::bigint::count_big_uint_bits(value);
        Self::from_big_uint(value, bits)
    }
}

impl BitVecOps for BitVecValue {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}

impl BitVecMutOps for BitVecValue {
    fn words_mut(&mut self) -> &mut [Word] {
        &mut self.words
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // by default we use 32 bits to represent the width
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // we use a 64-bit word size
        assert_eq!(std::mem::size_of::<Word>(), 8);
        assert_eq!(std::mem::size_of::<[Word; 2]>(), 16);
        // 8 bytes (usize) for the capacity, 8 byte pointer + 8 byte allocation size
        assert_eq!(std::mem::size_of::<ValueVec>(), 8 + 8 + 8);
        assert_eq!(
            std::mem::size_of::<ValueVec>(),
            std::mem::size_of::<Vec<Word>>()
        );
        // width + value + padding
        assert_eq!(std::mem::size_of::<BitVecValue>(), 4 * 8);
        assert_eq!(
            std::mem::size_of::<BitVecValue>(),
            std::mem::size_of::<ValueVec>() + std::mem::size_of::<WidthInt>() + 4
        );
    }

    #[test]
    fn test_tru_fals() {
        assert!(BitVecValue::tru().to_bool().unwrap());
        assert!(!BitVecValue::fals().to_bool().unwrap());
    }
}
