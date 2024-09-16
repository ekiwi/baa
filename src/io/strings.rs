// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    pub kind: IntErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntErrorKind {
    /// An invalid digit was encountered.
    InvalidDigit,
    /// The integer does not fit into the size of the bitvector.
    ExceedsWidth,
}

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

/// 4 bits fit into a single hex digit
const BITS_PER_HEX_DIGIT: u32 = 4;
const WORD_HEX_DIGITS: u32 = Word::BITS / BITS_PER_HEX_DIGIT;
const WORD_HEX_MASK: Word = ((1 as Word) << BITS_PER_HEX_DIGIT) - 1;

pub(crate) fn to_hex_str(values: &[Word], width: WidthInt) -> String {
    if width == 0 {
        return "".to_string();
    }
    let bits_in_msb = width % Word::BITS;
    let digits_in_msb = bits_in_msb.div_ceil(BITS_PER_HEX_DIGIT);
    let mut out = String::with_capacity(width.div_ceil(BITS_PER_HEX_DIGIT) as usize);
    let msb = values.last().unwrap();
    for ii in (0..digits_in_msb).rev() {
        let value = (msb >> (ii * BITS_PER_HEX_DIGIT)) & WORD_HEX_MASK;
        out.push(char::from_digit(value as u32, 16).unwrap());
    }
    let skip_num = if digits_in_msb > 0 { 1 } else { 0 };
    for word in values.iter().rev().skip(skip_num) {
        for ii in (0..WORD_HEX_DIGITS).rev() {
            let value = (word >> (ii * BITS_PER_HEX_DIGIT)) & WORD_HEX_MASK;
            out.push(char::from_digit(value as u32, 16).unwrap());
        }
    }
    out
}

pub(crate) fn determine_width_from_str_radix(value: &str, radix: u32) -> WidthInt {
    let num_digits = match value.as_bytes() {
        [] => 0,
        [b'+' | b'-'] => 0,
        [b'+' | b'-', digits @ ..] => digits.len() as WidthInt,
        digits => digits.len() as WidthInt,
    };

    match radix {
        2 => num_digits,
        16 => num_digits * 4,
        _ => todo!(),
    }
}

#[inline]
fn hex_digit_value(digit: u8) -> Result<u8, ParseIntError> {
    let value = match digit {
        b'0'..=b'9' => digit - b'0',
        b'a'..=b'f' => digit - b'a' + 10,
        b'A'..=b'F' => digit - b'A' + 10,
        _ => {
            return Err(ParseIntError {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    };
    Ok(value)
}

/// Converts number string into bit vector value. Similar to `from_str_radix` in the Rust standard library.
pub(crate) fn from_str_radix(
    value: &str,
    radix: u32,
    out: &mut [Word],
    max_width: WidthInt,
) -> Result<WidthInt, ParseIntError> {
    if !(radix == 2 || radix == 16) {
        panic!("from_str_radix: only the following radii are supported: 2. Got {radix}.");
    }

    // The empty string becomes a 0-bit vector.
    if value.is_empty() {
        return Ok(0);
    }

    // treat string as bytes
    let digits = value.as_bytes();

    // check whether the string is negative
    let (is_negative, digits) = match digits {
        [b'+' | b'-'] => {
            return Err(ParseIntError {
                kind: IntErrorKind::InvalidDigit,
            });
        }
        [b'+', rest @ ..] => (false, rest),
        [b'-', rest @ ..] => (true, rest),
        _ => (false, digits),
    };

    let width = if radix == 2 {
        let width = digits.len() as WidthInt;
        // TODO: ignore zeros
        if width > max_width {
            return Err(ParseIntError {
                kind: IntErrorKind::ExceedsWidth,
            });
        }

        let words = width.div_ceil(Word::BITS);
        let mut word = 0 as Word;
        let mut out_ii = (words - 1) as usize;

        for (ii, cc) in digits.into_iter().enumerate() {
            let ii_rev = width as usize - ii - 1;
            if ii > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
                out[out_ii] = word;
                out_ii -= 1;
                word = 0;
            }

            let value = match cc {
                b'1' => 1,
                b'0' => 0,
                _ => {
                    return Err(ParseIntError {
                        kind: IntErrorKind::InvalidDigit,
                    })
                }
            };
            word = (word << 1) | value;
        }
        debug_assert_eq!(out_ii, 0);
        out[0] = word;
        width
    } else if radix == 16 {
        let num_digits = digits.len();
        let words = (num_digits as u32 * BITS_PER_HEX_DIGIT).div_ceil(Word::BITS);
        let mut word = 0 as Word;
        let mut out_ii = (words - 1) as usize;

        // read from right to left
        for (ii, cc) in digits.into_iter().enumerate() {
            let ii_rev = num_digits - ii - 1;
            if ii > 0 && ((ii_rev + 1) % WORD_HEX_DIGITS as usize) == 0 {
                out[out_ii] = word;
                out_ii -= 1;
                word = 0;
            }
            let value = hex_digit_value(*cc)?;
            word = (word << BITS_PER_HEX_DIGIT) | (value as Word);
        }
        debug_assert_eq!(out_ii, 0);
        out[0] = word;
        num_digits as u32 * BITS_PER_HEX_DIGIT
    } else {
        todo!()
    };
    if is_negative {
        crate::arithmetic::negate_in_place(out, width)
    }
    Ok(width)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::owned::value_vec_zeros;
    use proptest::proptest;

    fn do_test_from_to_bit_str(s: String) {
        let words = s.len().div_ceil(Word::BITS as usize);
        let mut out = vec![0; words];
        let width = determine_width_from_str_radix(&s, 2);
        assert_eq!(width as usize, s.len());
        from_str_radix(&s, 2, &mut out, width).unwrap();
        crate::arithmetic::assert_unused_bits_zero(&out, width);
        let s_out = to_bit_str(&out, width);
        assert_eq!(s, s_out);
    }

    #[test]
    fn test_to_bit_str_with_extra_words() {
        let input = value_vec_zeros(7);
        assert_eq!(to_bit_str(&input, 7), "0000000");
        assert_eq!(to_bit_str(&input, 33), "0".repeat(33));
    }

    fn do_test_from_to_hex_str(s: String) {
        let words = (s.len() * 4).div_ceil(Word::BITS as usize);
        let mut out = vec![0; words];
        let width = determine_width_from_str_radix(&s, 16);
        assert_eq!(width as usize, s.len() * 4);
        from_str_radix(&s, 16, &mut out, width).unwrap();
        crate::arithmetic::assert_unused_bits_zero(&out, width);
        let s_out = to_hex_str(&out, width);
        assert_eq!(s.to_ascii_lowercase(), s_out);
    }

    #[test]
    fn test_from_to_hex_str_regression() {
        assert_eq!(hex_digit_value(b'a').unwrap(), 10);
        assert_eq!(hex_digit_value(b'A').unwrap(), 10);
        do_test_from_to_hex_str("a".to_string());
        do_test_from_to_hex_str("A".to_string());
        do_test_from_to_hex_str("0aaaA0a0aAA0aaaA".to_string());
    }

    #[test]
    fn test_to_hex_str() {
        let mut input = value_vec_zeros(64);
        assert_eq!(to_hex_str(&input, 7), "00");
        assert_eq!(to_hex_str(&input, 33), "0".repeat(9));
        input[0] = 0xa4aa78;
        assert_eq!(to_hex_str(&input, 6 * 4), "a4aa78");
        let mut input = value_vec_zeros(128);
        input[0] = 0xaaaaaaaaaaaaaaaa;
        assert_eq!(to_hex_str(&input, 7 + Word::BITS), "00aaaaaaaaaaaaaaaa");
        assert_eq!(
            to_hex_str(&input, 33 + Word::BITS),
            format!("{}aaaaaaaaaaaaaaaa", "0".repeat(9))
        );
        input[1] = 0xa4aa78;
        assert_eq!(to_hex_str(&input, 6 * 4), "a4aa78aaaaaaaaaaaaaaaa");
        // regressions test
        let mut input = value_vec_zeros(64);
        input[0] = 768603298337958570;
        assert_eq!(to_hex_str(&input, 64), "0aaaa0a0aaa0aaaa");
    }

    proptest! {
        #[test]
        fn test_from_to_bit_str(s in "[01]*") {
            do_test_from_to_bit_str(s);
        }
        #[test]
        fn test_from_to_hex_str(s in "[01a-fA-F]*") {
            do_test_from_to_hex_str(s);
        }
    }
}
