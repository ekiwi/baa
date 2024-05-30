// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Traits for operations on bit-vectors.

use crate::value::owned::value_vec;
use crate::{BitVecValue, BitVecValueMutRef, BitVecValueRef, WidthInt, Word};

/// Declares an arithmetic function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
            debug_assert_eq!(self.width(), rhs.width());
            debug_assert_eq!(self.words().len(), rhs.words().len());
            let mut out = value_vec(self.width());
            if self.words().len() == 1 {
                // specialized for 1-word case
                crate::arithmetic::$name(
                    &mut out[0..1],
                    &self.words()[0..1],
                    &rhs.words()[0..1],
                    self.width(),
                );
            } else {
                crate::arithmetic::$name(&mut out, self.words(), rhs.words(), self.width());
            }
            BitVecValue::new(self.width(), out)
        }
    };
}

/// Declares a bitwise function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_bit_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
            debug_assert_eq!(self.width(), rhs.width());
            debug_assert_eq!(self.words().len(), rhs.words().len());
            let mut out = value_vec(self.width());
            if self.words().len() == 1 {
                // specialized for 1-word case
                crate::arithmetic::$name(&mut out[0..1], &self.words()[0..1], &rhs.words()[0..1]);
            } else {
                crate::arithmetic::$name(&mut out, self.words(), rhs.words());
            }
            BitVecValue::new(self.width(), out)
        }
    };
}

/// Operations over immutable bit-vector values.
pub trait BitVecOps {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];

    /// Convert to a string of 1s and 0s.
    fn to_bit_str(&self) -> String {
        crate::io::strings::to_bit_str(self.words(), self.width())
    }

    fn to_bytes_le(&self) -> Vec<u8> {
        crate::io::bytes::to_bytes_le(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_int(&self) -> num_bigint::BigInt {
        crate::io::bigint::to_big_int(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_uint(&self) -> num_bigint::BigUint {
        crate::io::bigint::to_big_uint(self.words())
    }

    #[cfg(feature = "fraction1")]
    fn to_signed_fixed_point(&self, fraction_width: WidthInt) -> fraction::Fraction {
        crate::io::fraction::to_signed_fixed_point(self.words(), self.width(), fraction_width)
    }

    #[cfg(feature = "fraction1")]
    fn to_unsigned_fixed_point(&self, fraction_width: WidthInt) -> fraction::Fraction {
        crate::io::fraction::to_unsigned_fixed_point(self.words(), self.width(), fraction_width)
    }

    /// Returns value as a bool iff the value is a 1-bit value.
    fn to_bool(&self) -> Option<bool> {
        if self.width() == 1 {
            Some(crate::arithmetic::word_to_bool(self.words()[0]))
        } else {
            None
        }
    }

    /// Returns the value as a 64-bit unsigned integer iff the width is 64-bit or less.
    fn to_u64(&self) -> Option<u64> {
        // TODO: allow conversion of bit-vectors over 64 bits if the value can fit into 64 bits
        if self.width() <= 64 {
            if self.width() == 0 {
                Some(0)
            } else {
                debug_assert_eq!(Word::BITS, 64);
                debug_assert_eq!(self.words().len(), 0);
                Some(self.words()[0] as u64)
            }
        } else {
            None
        }
    }

    /// Returns the value as a 64-bit signed integer iff the width is 64-bit or less.
    fn to_i64(&self) -> Option<i64> {
        // TODO: allow conversion of bit-vectors over 64 bits if the value can fit into 64 bits
        if self.width() <= 64 {
            if self.width() == 0 {
                Some(0)
            } else {
                debug_assert_eq!(Word::BITS, 64);
                debug_assert_eq!(self.words().len(), 0);
                if crate::arithmetic::is_neg(self.words(), self.width()) {
                    todo!()
                } else {
                    Some(self.words()[0] as i64)
                }
            }
        } else {
            None
        }
    }

    fn is_zero(&self) -> bool {
        self.words().iter().all(|w| *w == 0)
    }

    declare_arith_bin_fn!(add);
    declare_arith_bin_fn!(sub);
    declare_arith_bin_fn!(shift_left);
    declare_arith_bin_fn!(shift_right);
    declare_arith_bin_fn!(arithmetic_shift_right);
    declare_arith_bin_fn!(mul);
    declare_bit_arith_bin_fn!(and);
    declare_bit_arith_bin_fn!(or);
    declare_bit_arith_bin_fn!(xor);

    fn is_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_equal(self.words(), rhs.words())
        } else {
            crate::arithmetic::cmp_equal(self.words(), rhs.words())
        }
    }

    fn is_not_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        !self.is_equal(rhs)
    }

    fn is_greater<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater(&self.words()[0..1], &rhs.words()[0..1])
        } else {
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_greater_or_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal(&self.words()[0..1], &rhs.words()[0..1])
        } else {
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_less<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater(self)
    }

    fn is_less_or_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal(self)
    }

    fn is_greater_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_signed(
                &self.words()[0..1],
                &rhs.words()[0..1],
                self.width(),
            )
        } else {
            crate::arithmetic::cmp_greater_signed(self.words(), rhs.words(), self.width())
        }
    }

    fn is_greater_or_equal_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal_signed(
                &self.words()[0..1],
                &rhs.words()[0..1],
                self.width(),
            )
        } else {
            crate::arithmetic::cmp_greater_equal_signed(self.words(), rhs.words(), self.width())
        }
    }

    fn is_less_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater_signed(self)
    }

    fn is_less_or_equal_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal_signed(self)
    }

    fn slice(&self, msb: WidthInt, lsb: WidthInt) -> BitVecValue {
        debug_assert!(msb <= self.width());
        debug_assert!(msb >= lsb);
        let out_width = msb - lsb + 1;
        let mut out = value_vec(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::arithmetic::slice(&mut out[0..1], self.words(), msb, lsb);
        } else {
            crate::arithmetic::slice(&mut out, self.words(), msb, lsb);
        }
        BitVecValue::new(out_width, out)
    }

    fn sign_extend(&self, by: WidthInt) -> BitVecValue {
        let out_width = self.width() + by;
        let mut out = value_vec(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::arithmetic::sign_extend(
                &mut out[0..1],
                &self.words()[0..1],
                self.width(),
                out_width,
            );
        } else {
            crate::arithmetic::sign_extend(&mut out, self.words(), self.width(), out_width);
        }
        BitVecValue::new(out_width, out)
    }

    fn zero_extend(&self, by: WidthInt) -> BitVecValue {
        let out_width = self.width() + by;
        let mut out = value_vec(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::arithmetic::zero_extend(&mut out[0..1], &self.words()[0..1]);
        } else {
            crate::arithmetic::zero_extend(&mut out, self.words());
        }
        BitVecValue::new(out_width, out)
    }

    fn not(&self) -> BitVecValue {
        let mut out = value_vec(self.width());
        if self.words().len() <= 1 {
            // specialized for 1-word case
            crate::arithmetic::not(&mut out[0..1], &self.words()[0..1], self.width());
        } else {
            crate::arithmetic::not(&mut out, self.words(), self.width());
        }
        BitVecValue::new(self.width(), out)
    }

    fn negate(&self) -> BitVecValue {
        let mut out = value_vec(self.width());
        if self.words().len() <= 1 {
            // specialized for 1-word case
            crate::arithmetic::negate(&mut out[0..1], &self.words()[0..1], self.width());
        } else {
            crate::arithmetic::negate(&mut out, self.words(), self.width());
        }
        BitVecValue::new(self.width(), out)
    }

    fn concat<R: BitVecOps + ?Sized>(&self, rhs: &R) -> BitVecValue {
        let out_width = self.width() + rhs.width();
        let mut out = value_vec(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::arithmetic::concat(
                &mut out[0..1],
                &self.words()[0..1],
                &rhs.words()[0..1],
                rhs.width(),
            );
        } else {
            crate::arithmetic::concat(&mut out, self.words(), rhs.words(), rhs.width());
        }
        BitVecValue::new(out_width, out)
    }
}

/// Operations over mutable bit-vector values.
pub trait BitVecMutOps: BitVecOps {
    fn words_mut(&mut self) -> &mut [Word];

    fn assign<V: BitVecOps>(&mut self, value: V) {
        debug_assert_eq!(self.width(), value.width());
        debug_assert_eq!(self.words_mut().len(), value.words().len());
        self.words_mut().copy_from_slice(value.words());
    }
}

pub const DENSE_ARRAY_MAX_INDEX_WIDTH: WidthInt = 48;

/// Operations implemented by read-only array values with a dense representation.
pub trait ArrayOps {
    fn index_width(&self) -> WidthInt;
    fn data_width(&self) -> WidthInt;
    fn words(&self) -> &[Word];
    fn words_per_element(&self) -> usize {
        self.data_width().div_ceil(Word::BITS) as usize
    }
    fn select<I: BitVecOps>(&self, index: I) -> BitVecValueRef {
        debug_assert!(self.index_width() <= DENSE_ARRAY_MAX_INDEX_WIDTH);
        debug_assert_eq!(self.index_width(), index.width());
        debug_assert_eq!(index.words().len(), 1);
        let start = self.words_per_element() * index.words()[0] as usize;
        let end = start + self.words_per_element();
        BitVecValueRef::new(self.data_width(), &self.words()[start..end])
    }
    fn is_equal<R: ArrayOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.index_width(), rhs.index_width());
        debug_assert_eq!(self.data_width(), rhs.data_width());
        self.words() == rhs.words()
    }
}

/// Operations implemented by mutable array values with a dense representation.
pub trait ArrayMutOps: ArrayOps {
    fn words_mut(&mut self) -> &mut [Word];
    fn store<I: BitVecOps, D: BitVecOps>(&mut self, index: I, data: D) {
        debug_assert!(self.index_width() <= DENSE_ARRAY_MAX_INDEX_WIDTH);
        debug_assert_eq!(self.index_width(), index.width());
        debug_assert_eq!(index.words().len(), 1);
        let start = self.words_per_element() * index.words()[0] as usize;
        let end = start + self.words_per_element();
        let mut element =
            BitVecValueMutRef::new(self.data_width(), &mut self.words_mut()[start..end]);
        element.assign(data);
    }
}
