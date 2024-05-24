// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// basic arithmetic implementations

use crate::{WidthInt, Word};
use std::cmp::Ordering;

// TODO: make sure this is updated together with the Word type
type DoubleWord = u128;

#[inline]
pub(crate) fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS || bits == 0 {
        Word::MAX
    } else {
        assert!(bits < Word::BITS);
        ((1 as Word) << bits) - 1
    }
}

#[inline]
pub(crate) fn clear(dst: &mut [Word]) {
    for w in dst.iter_mut() {
        *w = 0;
    }
}

#[inline]
fn set(dst: &mut [Word]) {
    for w in dst.iter_mut() {
        *w = Word::MAX;
    }
}

#[inline]
pub(crate) fn assign(dst: &mut [Word], source: &[Word]) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = *s;
    }
}

#[inline]
pub(crate) fn read_bool(source: &[Word]) -> bool {
    word_to_bool(source[0])
}

#[inline]
pub(crate) fn assign_word(dst: &mut [Word], value: Word) {
    // assign the lsb
    dst[0] = value;

    // zero extend
    for other in dst.iter_mut().skip(1) {
        *other = 0;
    }
}

#[inline]
pub(crate) fn zero_extend(dst: &mut [Word], source: &[Word]) {
    // copy source to dst
    assign(dst, source);
    // zero out remaining words
    clear(&mut dst[source.len()..]);
}

#[inline]
pub(crate) fn sign_extend(
    dst: &mut [Word],
    source: &[Word],
    src_width: WidthInt,
    dst_width: WidthInt,
) {
    // copy source to dst
    assign(dst, source);
    if is_neg(source, src_width) {
        // set source msbs in destination
        let lsbs_in_msb = src_width % Word::BITS;
        if lsbs_in_msb > 0 {
            let msbs_in_msb = Word::BITS - lsbs_in_msb;
            dst[source.len() - 1] |= mask(msbs_in_msb) << lsbs_in_msb;
        }
        // set other dst bytes to all 1s
        set(&mut dst[source.len()..]);
        // clear destination msbs
        mask_msb(dst, dst_width);
    } else {
        clear(&mut dst[source.len()..]);
    }
}

#[inline]
pub(crate) fn mask_msb(dst: &mut [Word], width: WidthInt) {
    let m = mask(width % Word::BITS);
    *dst.last_mut().unwrap() &= m;
}

#[inline]
pub(crate) fn slice(dst: &mut [Word], source: &[Word], hi: WidthInt, lo: WidthInt) {
    let lo_offset = lo % Word::BITS;
    let hi_word = (hi / Word::BITS) as usize;
    let lo_word = (lo / Word::BITS) as usize;
    let src = &source[lo_word..(hi_word + 1)];

    let shift_right = lo_offset;
    if shift_right == 0 {
        assign(dst, src);
    } else {
        // assign with a shift
        let shift_left = Word::BITS - shift_right;
        let m = mask(shift_right);
        let mut prev = src[0] >> shift_right;
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            *d = prev | ((*s) & m) << shift_left;
            prev = (*s) >> shift_right;
        }
    }
    // mask the result msb
    mask_msb(dst, hi - lo + 1);
}

#[inline]
pub(crate) fn concat(dst: &mut [Word], msb: &[Word], lsb: &[Word], lsb_width: WidthInt) {
    // copy lsb to dst
    assign(dst, lsb);

    let lsb_offset = lsb_width % Word::BITS;
    if lsb_offset == 0 {
        // copy msb to dst
        for (d, m) in dst.iter_mut().skip(lsb.len()).zip(msb.iter()) {
            *d = *m;
        }
    } else {
        // copy a shifted version of the msb to dst
        let shift_right = Word::BITS - lsb_offset;
        let m = mask(shift_right);
        let mut prev = dst[lsb.len() - 1]; // the msb of the lsb
        for (d, s) in dst
            .iter_mut()
            .skip(lsb.len() - 1)
            .zip(msb.iter().chain([0].iter()))
        {
            *d = prev | ((*s) & m) << lsb_offset;
            prev = (*s) >> shift_right;
        }
    }
}

#[inline]
pub(crate) fn not(dst: &mut [Word], source: &[Word], width: WidthInt) {
    bitwise_un_op(dst, source, |e| !e);
    mask_msb(dst, width);
}

#[inline]
fn bitwise_un_op(dst: &mut [Word], source: &[Word], op: fn(Word) -> Word) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = (op)(*s);
    }
}

#[inline]
pub(crate) fn and(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a & b)
}

#[inline]
pub(crate) fn or(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a | b)
}

#[inline]
pub(crate) fn xor(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a ^ b)
}

#[inline]
fn bitwise_bin_op(dst: &mut [Word], a: &[Word], b: &[Word], op: fn(Word, Word) -> Word) {
    for (d, (a, b)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        *d = (op)(*a, *b);
    }
}

#[inline]
fn adc(dst: &mut Word, carry: u8, a: Word, b: Word) -> u8 {
    let sum = carry as DoubleWord + a as DoubleWord + b as DoubleWord;
    let new_carry = (sum >> Word::BITS) as u8;
    *dst = sum as Word;
    new_carry
}

/// Add function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/addition.rs.html
#[inline]
pub(crate) fn add(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    let mut carry = 0;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        carry = adc(dd, carry, *aa, *bb);
    }
    mask_msb(dst, width);
}

/// Sub function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/subtraction.rs.html
#[inline]
pub(crate) fn sub(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        // we invert b which in addition to adding 1 turns it into `-b`
        carry = adc(dd, carry, *aa, !(*bb));
    }
    mask_msb(dst, width);
}

/// Mul function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/multiplication.rs.html
#[inline]
pub(crate) fn mul(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    if width <= Word::BITS {
        let (res, _) = a[0].overflowing_mul(b[0]);
        dst[0] = res & mask(width);
    } else {
        todo!(
            "implement multiplication for bit vectors larger {}",
            Word::BITS
        );
    }
}

#[inline]
pub(crate) fn shift_right(
    dst: &mut [Word],
    a: &[Word],
    b: &[Word],
    width: WidthInt,
) -> Option<WidthInt> {
    // clear the destination
    clear(dst);

    // check to see if we are shifting for more than our width
    let shift_amount = match get_shift_amount(b, width) {
        None => return None,
        Some(value) => value,
    };

    // otherwise we actually perform the shift by converting it to a slice
    let hi = width - 1;
    let lo = shift_amount;
    let result_width = hi - lo + 1;
    let result_words = result_width.div_ceil(Word::BITS) as usize;
    slice(&mut dst[..result_words], a, hi, lo);
    Some(shift_amount)
}

#[inline]
pub(crate) fn arithmetic_shift_right(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // perform shift
    let shift_amount = shift_right(dst, a, b, width);

    // pad with sign bit if necessary
    if is_neg(a, width) {
        match shift_amount {
            None => {
                // over shift => we just need to set everything to 1
                for d in dst.iter_mut() {
                    *d = Word::MAX;
                }
                mask_msb(dst, width);
            }
            Some(amount) => {
                if amount > 0 {
                    let res_width = width - amount;
                    let local_msb = (res_width - 1) % Word::BITS;
                    let msb_word = ((res_width - 1) / Word::BITS) as usize;
                    if local_msb < (Word::BITS - 1) {
                        let msb_word_mask = mask(Word::BITS - (local_msb + 1));
                        dst[msb_word] |= msb_word_mask << (local_msb + 1);
                    }
                    for d in dst[(msb_word + 1)..].iter_mut() {
                        *d = Word::MAX;
                    }
                    mask_msb(dst, width);
                }
            }
        }
    }
}

#[inline]
pub(crate) fn shift_left(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // check to see if we are shifting for more than our width
    let shift_amount = match get_shift_amount(b, width) {
        None => {
            clear(dst);
            return;
        }
        Some(value) => value,
    };

    // otherwise we actually perform the shift
    let shift_left = shift_amount % Word::BITS;
    let shift_words = shift_amount / Word::BITS;
    let shift_right = Word::BITS - shift_left;
    let zeros = std::iter::repeat(&(0 as Word)).take(shift_words as usize);
    let mut prev = 0;
    for (d, s) in dst.iter_mut().zip(zeros.chain(a.iter())) {
        if shift_left == 0 {
            *d = *s;
        } else {
            *d = (*s << shift_left) | prev;
            prev = *s >> shift_right;
        }
    }
    if shift_left > 0 {
        mask_msb(dst, width);
    }
}

#[inline]
fn get_shift_amount(b: &[Word], width: WidthInt) -> Option<WidthInt> {
    let msb_set = b.iter().skip(1).any(|w| *w != 0);
    let shift_amount = b[0];
    if msb_set || shift_amount >= width as Word {
        None // result is just zero or the sign bit
    } else {
        Some(shift_amount as WidthInt)
    }
}

#[inline]
pub(crate) fn negate(dst: &mut [Word], b: &[Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for (dd, bb) in dst.iter_mut().zip(b.iter()) {
        // we invert b which in addition to adding 1 turns it into `-b`
        carry = adc(dd, carry, 0, !(*bb));
    }
    mask_msb(dst, width);
}

#[inline]
pub(crate) fn cmp_equal(a: &[Word], b: &[Word]) -> bool {
    a.iter().zip(b.iter()).all(|(a, b)| a == b)
}

#[inline]
pub(crate) fn cmp_greater(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(false)
}

#[inline]
pub(crate) fn is_neg(src: &[Word], width: WidthInt) -> bool {
    let msb_bit_id = (width - 1) % WidthInt::BITS;
    let msb_bit_value = (src.last().unwrap() >> msb_bit_id) & 1;
    msb_bit_value == 1
}

#[inline]
pub(crate) fn cmp_greater_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    match (is_neg(a, width), is_neg(b, width)) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater(a, b),
        (true, true) => cmp_greater(a, b), // TODO: does this actually work?
    }
}

/// `Some(true)` if `a > b`, `Some(false)` if `a < b`, None if `a == b`
#[inline]
fn is_greater_and_not_less(a: &[Word], b: &[Word]) -> Option<bool> {
    for (a, b) in a.iter().rev().zip(b.iter().rev()) {
        match a.cmp(b) {
            Ordering::Less => return Some(false),
            Ordering::Equal => {} // continue
            Ordering::Greater => return Some(true),
        }
    }
    None
}

#[inline]
pub(crate) fn cmp_greater_equal(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(true)
}

#[inline]
pub(crate) fn cmp_greater_equal_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    match (is_neg(a, width), is_neg(b, width)) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater_equal(a, b),
        (true, true) => cmp_greater_equal(a, b), // TODO: does this actually work?
    }
}

#[inline]
pub(crate) fn bool_to_word(value: bool) -> Word {
    if value {
        1
    } else {
        0
    }
}

#[inline]
pub(crate) fn word_to_bool(value: Word) -> bool {
    (value & 1) == 1
}

#[cfg(test)]
pub(crate) fn assert_unused_bits_zero(value: &[Word], width: WidthInt) {
    let offset = width % Word::BITS;
    if offset > 0 {
        let msb = *value.last().unwrap();
        let m = !mask(offset);
        let unused = msb & m;
        assert_eq!(unused, 0, "unused msb bits need to be zero!")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::strings::to_bit_str;
    use crate::value::owned::{value_vec, ValueVec};
    use proptest::prelude::*;

    fn from_bit_str(s: &str) -> (ValueVec, WidthInt) {
        let width = s.len() as WidthInt;
        let mut out = value_vec(width);
        crate::io::strings::from_bit_str(s, &mut out);
        (out, width)
    }

    fn bit_str_arg() -> impl Strategy<Value = String> {
        "[01]+"
    }

    fn do_test_concat(a: &str, b: &str) {
        let (a_vec, a_width) = from_bit_str(a);
        let (b_vec, b_width) = from_bit_str(b);
        let c_init = "1".repeat(a.len() + b.len());
        let (mut c_vec, c_width) = from_bit_str(&c_init);
        assert_eq!(c_width, a_width + b_width);
        concat(&mut c_vec, &a_vec, &b_vec, b_width);
        assert_unused_bits_zero(&c_vec, c_width);
        let expected = format!("{a}{b}");
        assert_eq!(to_bit_str(&c_vec, c_width), expected);
    }

    fn do_test_slice(src: &str, hi: WidthInt, lo: WidthInt) {
        assert!(
            !src.is_empty(),
            "slice only works with vectors that are at least 1-bit!"
        );
        let (src_vec, src_width) = from_bit_str(src);
        assert!(hi >= lo);
        assert!(hi < src_width);
        let res_width = hi - lo + 1;
        let mut res_vec = vec![0 as Word; res_width.div_ceil(Word::BITS) as usize];
        slice(&mut res_vec, &src_vec, hi, lo);
        assert_unused_bits_zero(&res_vec, res_width);
        let expected: String = src
            .chars()
            .skip((src_width - 1 - hi) as usize)
            .take(res_width as usize)
            .collect();
        assert_eq!(to_bit_str(&res_vec, res_width), expected);
    }

    fn slice_args() -> impl Strategy<Value = (String, WidthInt, WidthInt)> {
        bit_str_arg()
            .prop_flat_map(|bits: String| {
                let len = std::cmp::max(bits.len(), 1);
                (Just(bits), 0..(len as WidthInt))
            })
            .prop_flat_map(|(bits, msb)| (Just(bits), Just(msb), 0..(msb + 1)))
    }

    fn width_int_to_bit_str(value: WidthInt, width: WidthInt) -> String {
        let mut words = value_vec(width);
        // make sure the shift amount fits into the width
        if width < WidthInt::BITS {
            assert_eq!(
                (value as Word) & mask(width),
                value as Word,
                "shift amount is too large: {value} > {}",
                mask(width)
            );
        }
        words[0] = value as Word;
        to_bit_str(&words, width)
    }

    fn do_test_shift(src: &str, by: WidthInt, right: bool, signed: bool) {
        assert!(!(!right && signed), "left shift is always unsigned!");
        let (a_vec, a_width) = from_bit_str(src);
        let b = width_int_to_bit_str(by, a_width);
        let (b_vec, b_width) = from_bit_str(&b);
        assert_eq!(a_width, b_width);
        let mut res_vec = vec![0 as Word; a_vec.len()];
        if right {
            if signed {
                arithmetic_shift_right(&mut res_vec, &a_vec, &b_vec, a_width);
            } else {
                shift_right(&mut res_vec, &a_vec, &b_vec, a_width);
            }
        } else {
            shift_left(&mut res_vec, &a_vec, &b_vec, a_width);
        }
        assert_unused_bits_zero(&res_vec, a_width);
        let padding_len = std::cmp::min(by, a_width) as usize;
        let pad_char = if signed {
            src.chars().next().unwrap()
        } else {
            '0'
        };

        let mut expected: String = pad_char.to_string().repeat(padding_len);
        if right {
            let msb: String = src.chars().take(a_width as usize - padding_len).collect();
            expected.push_str(&msb);
        } else {
            let mut msb: String = src.chars().skip(padding_len).collect();
            msb.push_str(&expected);
            expected = msb;
        }
        assert_eq!(to_bit_str(&res_vec, a_width), expected);
    }

    fn do_test_shift_right(src: &str, by: WidthInt) {
        do_test_shift(src, by, true, false);
    }
    fn do_test_shift_left(src: &str, by: WidthInt) {
        do_test_shift(src, by, false, false);
    }

    fn do_test_arithmetic_shift_right(src: &str, by: WidthInt) {
        do_test_shift(src, by, true, true);
    }

    #[test]
    fn test_arithmetic_shift_right_regression() {
        do_test_arithmetic_shift_right("1", 0);
        do_test_arithmetic_shift_right("10", 1);
        do_test_arithmetic_shift_right(&format!("1{}", "0".repeat(Word::BITS as usize)), 1);
        do_test_arithmetic_shift_right(&format!("1{}", "0".repeat((Word::BITS * 2) as usize)), 1);
        do_test_arithmetic_shift_right(
            &format!("1{}", "0".repeat((Word::BITS * 2) as usize)),
            Word::BITS,
        );
        do_test_arithmetic_shift_right(
            &format!("1{}", "0".repeat((Word::BITS * 2) as usize)),
            Word::BITS * 2,
        );
    }

    /// biases `by` value to be more interesting
    fn shift_args() -> impl Strategy<Value = (String, WidthInt)> {
        bit_str_arg().prop_flat_map(|bits: String| {
            let len = std::cmp::max(bits.len(), 1);
            let max_shift =
                std::cmp::min(mask(bits.len() as WidthInt) + 1, WidthInt::MAX as Word) as WidthInt;
            let by = prop_oneof![0..(len as WidthInt), 0..(max_shift)];
            (Just(bits), by)
        })
    }

    fn do_test_zero_ext(src: &str, by: WidthInt) {
        let (src_vec, src_width) = from_bit_str(src);
        let res_width = src_width + by;
        let mut res_vec = value_vec(res_width);
        zero_extend(&mut res_vec, &src_vec);
        assert_unused_bits_zero(&res_vec, res_width);
        let expected: String = format!("{}{}", "0".repeat(by as usize), src);
        let actual = to_bit_str(&res_vec, res_width);
        assert_eq!(actual, expected, "{res_vec:?}");
    }

    fn do_test_sign_ext(src: &str, by: WidthInt) {
        assert!(!src.is_empty(), "sign extend only works for non zero bits");
        let (src_vec, src_width) = from_bit_str(src);
        let res_width = src_width + by;
        let mut res_vec = value_vec(res_width);
        sign_extend(&mut res_vec, &src_vec, src_width, res_width);
        assert_unused_bits_zero(&res_vec, res_width);
        let sign_bit = src.chars().next().unwrap().to_string();
        let expected: String = format!("{}{}", sign_bit.repeat(by as usize), src);
        let actual = to_bit_str(&res_vec, res_width);
        assert_eq!(actual, expected, "{res_vec:?}");
    }

    use num_bigint::*;
    fn gen_big_uint(bits: WidthInt) -> impl Strategy<Value = BigUint> {
        let byte_count = bits.div_ceil(u8::BITS);
        let words = prop::collection::vec(any::<u8>(), byte_count as usize);
        words.prop_map(move |mut words| {
            // first we mask the msbs
            if bits % u8::BITS > 0 {
                let mask = (1u8 << (bits % u8::BITS)) - 1;
                *words.last_mut().unwrap() &= mask;
            }
            BigUint::from_bytes_le(&words)
        })
    }

    fn gen_big_int(bits: WidthInt) -> impl Strategy<Value = BigInt> {
        gen_big_uint(bits - 1)
            .prop_flat_map(|unsigned| (any::<bool>(), Just(unsigned)))
            .prop_map(|(negative, unsigned)| {
                let sign = if negative { Sign::Minus } else { Sign::Plus };
                BigInt::from_biguint(sign, unsigned)
            })
    }

    // generates two big ints of equal bit width
    fn gen_big_int_pair() -> impl Strategy<Value = (BigInt, BigInt, WidthInt)> {
        let max_bits = 16 * Word::BITS;
        (1..max_bits).prop_flat_map(|bits| (gen_big_int(bits), gen_big_int(bits), Just(bits)))
    }

    fn from_big_int(value: &BigInt, width: WidthInt) -> ValueVec {
        let mut out = value_vec(width);
        crate::io::bigint::from_big_int(&value, width, &mut out);
        out
    }

    fn do_test_arith(
        a: BigInt,
        b: BigInt,
        width: WidthInt,
        our: fn(&mut [Word], &[Word], &[Word], WidthInt),
        big: fn(BigInt, BigInt) -> BigInt,
    ) {
        let a_vec = from_big_int(&a, width);
        let b_vec = from_big_int(&b, width);
        let mut res_vec: ValueVec = value_vec(width);
        our(&mut res_vec, &a_vec, &b_vec, width);
        assert_unused_bits_zero(&res_vec, width);

        // check result
        let expected_num = (big)(a.clone(), b.clone());
        let expected = from_big_int(&expected_num, width);
        assert_eq!(expected, res_vec, "{a} {b} {expected_num}");
    }

    fn do_test_add(a: BigInt, b: BigInt, width: WidthInt) {
        do_test_arith(a, b, width, add, |a, b| a + b)
    }

    fn do_test_sub(a: BigInt, b: BigInt, width: WidthInt) {
        do_test_arith(a, b, width, sub, |a, b| a - b)
    }

    fn do_test_mul(a: BigInt, b: BigInt, width: WidthInt) {
        do_test_arith(a, b, width, mul, |a, b| a * b)
    }

    #[test]
    fn test_mul_regressions() {
        do_test_mul(
            BigInt::from(1099511627776i64),
            BigInt::from(1099511627776i64),
            50,
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]
        #[test]
        fn test_concat(a in bit_str_arg(), b in bit_str_arg()) {
            do_test_concat(&a, &b);
        }

        #[test]
        fn test_slice((s, msb, lsb) in slice_args()) {
            do_test_slice(&s, msb, lsb);
        }

        #[test]
        fn test_shift_right((s, by) in shift_args()) {
            do_test_shift_right(&s, by);
        }

        #[test]
        fn test_shift_left((s, by) in shift_args()) {
            do_test_shift_left(&s, by);
        }

        #[test]
        fn test_arithmetic_shift_right((s, by) in shift_args()) {
            do_test_arithmetic_shift_right(&s, by);
        }

        #[test]
        fn test_zero_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
            do_test_zero_ext(&s, by);
        }

        #[test]
        fn test_sign_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
            do_test_sign_ext(&s, by);
        }

        #[test]
        fn test_add((a, b, width) in gen_big_int_pair()) {
            do_test_add(a, b, width);
        }

        #[test]
        fn test_sub((a, b, width) in gen_big_int_pair()) {
            do_test_sub(a, b, width);
        }

        #[ignore] // TODO: implement mul for bitwidths > 64
        #[test]
        fn test_mul((a, b, width) in gen_big_int_pair()) {
            do_test_mul(a, b, width);
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::ir::value::tests::*;
//     use crate::ir::value::*;
//     use num_bigint::{BigInt, BigUint, Sign};
//     use rand::{Rng, SeedableRng};
//     use smallvec::smallvec;
//
//     #[test]
//     fn test_split_borrow() {
//         let data: &mut [Word] = &mut [0, 1, 2, 3];
//         let (dst, src) = split_borrow_1(data, 0..1, 2..4);
//         assert_eq!(dst, &[0]);
//         assert_eq!(src, &[2, 3]);
//         let (dst2, src2) = split_borrow_1(data, 2..4, 0..2);
//         assert_eq!(dst2, &[2, 3]);
//         assert_eq!(src2, &[0, 1]);
//
//         let (dst3, src_a_3, src_b_3) = split_borrow_2(data, 2..4, 1..2, 0..2);
//         assert_eq!(dst3, &[2, 3]);
//         assert_eq!(src_a_3, &[1]);
//         assert_eq!(src_b_3, &[0, 1]);
//     }
//
//
//
//     fn do_test_cmp(
//         a: BigInt,
//         b: BigInt,
//         width: WidthInt,
//         our: fn(&[Word], &[Word], WidthInt) -> bool,
//         big: fn(BigInt, BigInt) -> bool,
//     ) {
//         let a_vec = from_big_int(&a, width);
//         let b_vec = from_big_int(&b, width);
//         let res_bool = (our)(&a_vec, &b_vec, width);
//         let expected_bool = (big)(a.clone(), b.clone());
//         assert_eq!(expected_bool, res_bool, "{a} {b} {expected_bool}");
//     }
//
//     fn do_test_cmp_greater(a: BigUint, b: BigUint, width: WidthInt) {
//         let a_signed = BigInt::from_biguint(Sign::Plus, a);
//         let b_signed = BigInt::from_biguint(Sign::Plus, b);
//         do_test_cmp(
//             a_signed,
//             b_signed,
//             width,
//             |a, b, _| cmp_greater(a, b),
//             |a, b| a > b,
//         )
//     }
//     fn do_test_cmp_greater_signed(a: BigInt, b: BigInt, width: WidthInt) {
//         do_test_cmp(a, b, width, cmp_greater_signed, |a, b| a > b)
//     }
//
//     fn do_test_cmp_greater_equal_signed(a: BigInt, b: BigInt, width: WidthInt) {
//         do_test_cmp(a, b, width, cmp_greater_equal_signed, |a, b| a >= b)
//     }
//
//     #[test]
//     fn test_cmp_greater() {
//         do_test_cmp_greater(BigUint::from(4u32), BigUint::from(3u32), 8);
//     }
//
//     #[test]
//     fn test_cmp_greater_signed() {
//         do_test_cmp_greater_signed(BigInt::from(-4), BigInt::from(3), 8);
//         do_test_cmp_greater_signed(BigInt::from(4), BigInt::from(-3), 8);
//         do_test_cmp_greater_signed(BigInt::from(4), BigInt::from(3), 8);
//         do_test_cmp_greater_signed(BigInt::from(3), BigInt::from(4), 8);
//         do_test_cmp_greater_signed(BigInt::from(-4), BigInt::from(-3), 8);
//         do_test_cmp_greater_signed(BigInt::from(-3), BigInt::from(-4), 8);
//     }
//
//     #[test]
//     fn test_cmp_greater_equal_signed() {
//         do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(3), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(-3), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(3), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(3), BigInt::from(4), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(-3), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(-3), BigInt::from(-4), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(-4), 8);
//         do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(4), 8);
//     }
// }
