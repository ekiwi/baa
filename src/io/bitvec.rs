// Copyright 2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::io::strings::{from_bit_str, to_bit_str};
use crate::{WidthInt, Word};
use bitvec::macros::internal::funty::Fundamental;
use bitvec::prelude::*;

pub(crate) fn to_bitvec(values: &[Word], width: WidthInt) -> BitVec {
    if width == 0 {
        return bitvec![];
    }

    let mut out = BitVec::with_capacity(width as usize);
    for (word_ii, word) in values.iter().enumerate() {
        let msb_word = word_ii == values.len() - 1;
        let uneven_bits = width % Word::BITS != 0;
        let bits = if msb_word && uneven_bits {
            width % Word::BITS
        } else {
            Word::BITS
        };
        for bit in 0..bits {
            let value = (*word >> bit) & 1;
            out.push(value == 1);
        }
    }
    debug_assert_eq!(out.len(), width as usize);
    out
}

pub(crate) fn from_bitvec<T, O>(
    bits: &BitVec<T, O>,
    out: &mut [Word],
) -> WidthInt
where
    T: BitStore,
    O: BitOrder,
{
    if bits.is_empty() {
        return 0;
    }
    let width = bits.len() as WidthInt;
    let words = width.div_ceil(Word::BITS);
    let mut word = 0 as Word;
    let mut out_ii = (words - 1) as usize;

    for (ii, cc) in bits.iter().rev().enumerate() {
        let ii_rev = width as usize - ii - 1;
        if ii > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
            out[out_ii] = word;
            out_ii -= 1;
            word = 0;
        }
        let value: Word = cc.as_u8().into();
        word = (word << 1) | value;
    }
    debug_assert_eq!(out_ii, 0);
    out[0] = word;

    width
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::proptest;

    fn str_to_bitvec(s: &str) -> BitVec {
        let mut out = BitVec::with_capacity(s.len());
        for cc in s.chars().rev() {
            match cc {
                '0' => out.push(false),
                '1' => out.push(true),
                _ => unreachable!(),
            }
        }
        out
    }

    fn do_test_from_to_bitvec(s: &str) {
        let vec_in = str_to_bitvec(s);
        let words = vec_in.len().div_ceil(Word::BITS as usize);
        let mut out = vec![0; words];
        let width = from_bitvec(&vec_in, &mut out);
        assert_eq!(width as usize, vec_in.len());
        let vec_out = to_bitvec(&out, width);
        assert_eq!(vec_in, vec_out);
    }

    proptest! {
        #[test]
        fn test_from_to_bitvec(s in "[01]*") {
            do_test_from_to_bitvec(&s);
        }
    }
}
