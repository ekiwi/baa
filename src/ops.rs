// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Traits for operations on bit-vectors.

use crate::{BitVecValue, BitVecValueRef, WidthInt, Word};
use smallvec::{smallvec, SmallVec};

/// Declares an arithmetic function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            let mut out = [0; 2];
            crate::arithmetic::$name(
                &mut out[0..1],
                self.words(),
                rhs.words(),
                self.width(),
            );
            BitVecValue {
                width: self.width(),
                words: SmallVec::from_buf(out),
            }
        } else {
            let mut out = smallvec![0; self.words().len()];
            crate::arithmetic::$name(
                out.as_mut(),
                self.words(),
                rhs.words(),
                self.width(),
            );
            BitVecValue {
                width: self.width(),
                words: out,
            }
        }
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
        if self.words().len() == 1 {
            // specialized for 1-word case
            let mut out = [0; 2];
            crate::arithmetic::$name(
                &mut out[0..1],
                self.words(),
                rhs.words(),
            );
            BitVecValue {
                width: self.width(),
                words: SmallVec::from_buf(out),
            }
        } else {
            let mut out = smallvec![0; self.words().len()];
            crate::arithmetic::$name(
                out.as_mut(),
                self.words(),
                rhs.words(),
            );
            BitVecValue {
                width: self.width(),
                words: out,
            }
        }
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
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        } else {
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_greater_or_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal(self.words(), rhs.words())
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
            crate::arithmetic::cmp_greater_signed(self.words(), rhs.words(), self.width())
        } else {
            crate::arithmetic::cmp_greater_signed(self.words(), rhs.words(), self.width())
        }
    }

    fn is_greater_or_equal_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal_signed(self.words(), rhs.words(), self.width())
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
        let out_words = out_width.div_ceil(Word::BITS);
        if out_words == 1 {
            // specialized for 1-word case
            let mut out = [0; 2];
            crate::arithmetic::slice(&mut out[0..1], self.words(), msb, lsb);
            BitVecValue {
                width: out_width,
                words: SmallVec::from_buf(out),
            }
        } else {
            let mut out = smallvec![0; out_words as usize];
            crate::arithmetic::slice(out.as_mut(), self.words(), msb, lsb);
            BitVecValue {
                width: out_width,
                words: out,
            }
        }
    }
}

/// Operations over mutable bit-vector values.
pub trait BitVecMutOps: BitVecOps {
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

pub trait ArrayOps {
    fn index_width(&self) -> WidthInt;
    fn data_width(&self) -> WidthInt;
    fn select<I>(&self, index: I) -> BitVecValueRef
    where
        I: for<'a> Into<BitVecValueRef<'a>>;
    fn is_equal<R: ArrayOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.index_width(), rhs.index_width());
        debug_assert_eq!(self.data_width(), rhs.data_width());
        todo!()
    }
}

pub trait ArrayMutOps: ArrayOps {
    fn store<I, D>(&mut self, index: I, data: D)
    where
        I: for<'a> Into<BitVecValueRef<'a>>,
        D: for<'a> Into<BitVecValueRef<'a>>;
}
