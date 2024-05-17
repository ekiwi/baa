// Copyright 2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};

const BYTES_PER_WORD: u32 = Word::BITS.div_ceil(8);
const BYTE_MASK: Word = (1 << u8::BITS) - 1;

pub(crate) fn to_bytes_le(values: &[Word], width: WidthInt) -> Vec<u8> {
    let byte_count = width.div_ceil(u8::BITS) as usize;
    let mut out = Vec::with_capacity(byte_count);
    for word in values.iter() {
        let mut value = *word;
        for _ in 0..BYTES_PER_WORD {
            if out.len() == byte_count {
                break;
            }
            out.push((value & BYTE_MASK) as u8);
            value = value >> u8::BITS;
        }
    }
    out
}

pub(crate) fn from_bytes_le(bytes: &[u8], width: WidthInt, out: &mut [Word]) {
    let word_count = width.div_ceil(Word::BITS) as usize;
    debug_assert!(out.len() >= word_count);
    if width == 0 {
        return;
    }
    crate::arithmetic::clear(out);
    for (ii, bb) in bytes.iter().enumerate() {
        let word_ii = ii / BYTES_PER_WORD as usize;
        let shift_by = u8::BITS * (ii as u32 % BYTES_PER_WORD);
        out[word_ii] |= (*bb as Word) << shift_by;
    }
    crate::arithmetic::mask_msb(out, width);
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::proptest;

    #[test]
    fn test_to_bytes_le() {
        let out0 = to_bytes_le(&[0x1234], 16);
        assert_eq!(out0, [0x34, 0x12]);
        let out1 = to_bytes_le(&[0x1234, 0xf], 64 + 8);
        assert_eq!(out1, [0x34, 0x12, 0, 0, 0, 0, 0, 0, 0xf]);
    }

    #[test]
    fn test_from_bytes_le() {
        let mut out0 = vec![0; 1];
        from_bytes_le(&[0x34, 0x12], 16, &mut out0);
        assert_eq!(out0, [0x1234]);
    }

    fn find_first_one(b: &[u8]) -> WidthInt {
        for (ii, bb) in b.iter().enumerate().rev() {
            if *bb > 0 {
                let offset = bb.leading_zeros();
                return ii as WidthInt * 8 + 8 - offset;
            }
        }
        return 0;
    }

    fn do_test_from_to_bytes_le(b: &[u8]) {
        let width = if b.is_empty() {
            0
        } else {
            (b.len() - 1) * u8::BITS as usize
                + std::cmp::max(
                    8 - b.last().unwrap().leading_zeros() as usize,
                    1,
                )
        } as u32;
        let words = width.div_ceil(Word::BITS) as usize;
        let mut out = vec![0; words];
        from_bytes_le(b, width, &mut out);
        let b_out = to_bytes_le(&out, width);
        assert_eq!(b.as_ref(), b_out);
    }

    #[test]
    fn test_empty() {
        do_test_from_to_bytes_le(&[]);
    }

    #[test]
    fn test_zero() {
        do_test_from_to_bytes_le(&[0]);
    }

    proptest! {
        #[test]
        fn test_from_to_bytes_le(b: Vec<u8>) {
            do_test_from_to_bytes_le(&b);
        }
    }
}
