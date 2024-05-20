// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};

pub(crate) fn to_bit_str(values: &[Word], width: WidthInt) -> String {
    if width == 0 {
        return "".to_string();
    }
    let start_bit = (width - 1) % Word::BITS;
    let mut out = String::with_capacity(width as usize);
    let msb = values.last().unwrap();
    for ii in (0..(start_bit + 1)).rev() {
        let value = (msb >> ii) & 1;
        if value == 1 {
            out.push('1');
        } else {
            out.push('0');
        }
    }
    for word in values.iter().rev().skip(1) {
        for ii in (0..Word::BITS).rev() {
            let value = (word >> ii) & 1;
            if value == 1 {
                out.push('1');
            } else {
                out.push('0');
            }
        }
    }
    out
}

pub(crate) fn from_bit_str(bits: &str, out: &mut [Word]) -> WidthInt {
    if bits.is_empty() {
        return 0;
    }
    let width = bits.len() as WidthInt;
    let words = width.div_ceil(Word::BITS);
    let mut word = 0 as Word;
    let mut out_ii = (words - 1) as usize;

    for (ii, cc) in bits.chars().enumerate() {
        let ii_rev = width as usize - ii - 1;
        if ii > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
            out[out_ii] = word;
            out_ii -= 1;
            word = 0;
        }

        let value = match cc {
            '1' => 1,
            '0' => 0,
            other => unreachable!("Unexpected character: {other}"),
        };
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

    fn do_test_from_to_bit_str(s: String) {
        let words = s.len().div_ceil(Word::BITS as usize);
        let mut out = vec![0; words];
        let width = from_bit_str(&s, &mut out);
        assert_eq!(width as usize, s.len());
        crate::arithmetic::assert_unused_bits_zero(&out, width);
        let s_out = to_bit_str(&out, width);
        assert_eq!(s, s_out);
    }

    proptest! {
        #[test]
        fn test_from_to_bit_str(s in "[01]*") {
            do_test_from_to_bit_str(s);
        }
    }
}
