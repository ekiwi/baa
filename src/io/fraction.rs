// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{WidthInt, Word};
use smallvec::smallvec;

/// Tries to convert to a unsigned Fraction. Returns `None` if value won't fit into u64 fraction.
pub(crate) fn to_unsigned_fixed_point(
    words: &[Word],
    width: WidthInt,
    fraction_width: WidthInt,
) -> Option<fraction::Fraction> {
    debug_assert_eq!(
        Word::BITS,
        u64::BITS,
        "basic assumption of our implementation"
    );
    debug_assert!(fraction_width <= width);
    let denominator_width = fraction_width;
    let numerator_width = width - denominator_width;
    if denominator_width > u64::BITS || numerator_width > u64::BITS {
        return None;
    }
    todo!()
}

/// Tries to convert to a unsigned Fraction. Returns `None` if value won't fit into i64 fraction.
pub(crate) fn to_signed_fixed_point(
    words: &[Word],
    width: WidthInt,
    fraction_width: WidthInt,
) -> Option<fraction::Fraction> {
    debug_assert!(fraction_width <= width);
    if crate::arithmetic::is_neg(words, width) {
        let mut negated = smallvec![0;words.len()];
        crate::arithmetic::negate(&mut negated, words, width);
        to_unsigned_fixed_point(&negated, width, fraction_width).map(|f| -f)
    } else {
        to_unsigned_fixed_point(words, width, fraction_width)
    }
}

pub(crate) fn from_fixed_point(
    fraction: &fraction::Fraction,
    width: WidthInt,
    fraction_width: WidthInt,
    out: &mut [Word],
) {
    debug_assert!(fraction_width <= width);
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {}
}
