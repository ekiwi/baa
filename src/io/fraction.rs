// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{WidthInt, Word};

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
