// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//

use crate::{WidthInt, Word};

pub(crate) fn to_unsigned_fixed_point(
    words: &[Word],
    width: WidthInt,
    fraction_width: WidthInt,
) -> fraction::Fraction {
    debug_assert!(fraction_width <= width);
    todo!()
}
pub(crate) fn to_signed_fixed_point(
    words: &[Word],
    width: WidthInt,
    fraction_width: WidthInt,
) -> fraction::Fraction {
    debug_assert!(fraction_width <= width);
    todo!()
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
