// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//

use crate::{WidthInt, Word};
use std::cmp::Ordering;

pub(crate) fn to_big_uint(words: &[Word]) -> num_bigint::BigUint {
    let words32 = words_to_u32(words);
    num_bigint::BigUint::from_slice(&words32)
}

fn words_to_u32(words: &[Word]) -> Vec<u32> {
    let mut words32 = Vec::with_capacity(words.len() * 2);
    let mask32 = crate::arithmetic::mask(32);
    for w in words.iter() {
        let word = *w;
        let lsb = (word & mask32) as u32;
        let msb = ((word >> 32) & mask32) as u32;
        words32.push(lsb);
        words32.push(msb);
    }
    words32
}

pub(crate) fn from_big_uint(
    value: &num_bigint::BigUint,
    width: WidthInt,
    out: &mut [Word],
) {
    iter_to_word(value.iter_u64_digits(), width, out);
}

fn get_sign(value: &[Word], width: WidthInt) -> num_bigint::Sign {
    let sign_bit = (width - 1) % Word::BITS;
    let sign_value = (value.last().unwrap() >> sign_bit) & 1;
    if sign_value == 1 {
        num_bigint::Sign::Minus
    } else {
        num_bigint::Sign::Plus
    }
}

pub(crate) fn to_big_int(
    words: &[Word],
    width: WidthInt,
) -> num_bigint::BigInt {
    if width == 0 {
        return num_bigint::BigInt::ZERO;
    }
    let sign = get_sign(words, width);
    // calculate the magnitude
    let words64 = if sign == num_bigint::Sign::Minus {
        let mut negated = vec![0; words.len()];
        crate::arithmetic::negate(&mut negated, words, width);
        negated
    } else {
        Vec::from(words)
    };

    let words32 = words_to_u32(&words64);
    num_bigint::BigInt::from_slice(sign, &words32)
}

pub(crate) fn from_big_int(
    value: &num_bigint::BigInt,
    width: WidthInt,
    out: &mut [Word],
) {
    iter_to_word(value.iter_u64_digits(), width, out);
    // negate if sign is minus
    if value.sign() == num_bigint::Sign::Minus {
        let out_copy = Vec::from_iter(out.iter().cloned());
        crate::arithmetic::negate(out, &out_copy, width);
    }
}

#[inline]
fn iter_to_word(
    iter: impl Iterator<Item = Word>,
    width: WidthInt,
    out: &mut [Word],
) {
    if width == 0 {
        return;
    }
    let num_words = width.div_ceil(Word::BITS);
    debug_assert!(num_words as usize <= out.len());
    let mut word_count = 0u32;
    for (dst, src) in out.iter_mut().zip(iter) {
        *dst = src;
        word_count += 1;
    }
    match num_words.cmp(&word_count) {
        Ordering::Less => unreachable!(),
        Ordering::Equal => {
            crate::arithmetic::mask_msb(out, width);
        }
        Ordering::Greater => {
            // zero out remaining words
            for dst in out.iter_mut().skip(word_count as usize) {
                *dst = 0;
            }
        }
    }
}

pub(crate) fn count_big_uint_bits(value: &num_bigint::BigUint) -> WidthInt {
    let words = value.iter_u64_digits().count() as u32;
    if words == 0 {
        0
    } else {
        let msb = value.iter_u64_digits().last().unwrap();
        words * Word::BITS - msb.leading_zeros()
    }
}

pub(crate) fn count_big_int_bits(value: &num_bigint::BigInt) -> WidthInt {
    let words = value.iter_u64_digits().count() as u32;
    // +1 for the sign bit
    if words == 0 {
        1
    } else {
        let msb = value.iter_u64_digits().last().unwrap();
        words * Word::BITS - msb.leading_zeros() + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint, Sign};
    use proptest::proptest;
    use std::str::FromStr;

    fn do_test_from_to_big_int(value: &BigInt) {
        let bits = count_big_int_bits(value);
        let mut out = vec![0; bits.div_ceil(Word::BITS) as usize];
        from_big_int(value, bits as WidthInt, &mut out);
        let value_out = to_big_int(&out, bits as WidthInt);
        assert_eq!(value, &value_out);
    }

    fn do_test_from_to_big_uint(value: &BigUint) {
        let bits = count_big_uint_bits(value);
        let mut out = vec![0; bits.div_ceil(Word::BITS) as usize];
        from_big_uint(value, bits as WidthInt, &mut out);
        let value_out = to_big_uint(&out);
        assert_eq!(value, &value_out);
    }

    proptest! {
        #[test]
        fn test_from_to_big_int(m in "[0-9]+", neg: bool) {
            let u_value = BigUint::from_str(&m).unwrap();
            let sign = if neg { Sign::Minus } else { Sign::Plus };
            let value = BigInt::from_biguint(sign, u_value);
            do_test_from_to_big_int(&value);
        }

        #[test]
        fn test_from_to_big_uint(s in "[0-9]+") {
            let value = BigUint::from_str(&s).unwrap();
            do_test_from_to_big_uint(&value);
        }
    }
}
