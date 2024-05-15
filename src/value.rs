// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};
use smallvec::SmallVec;

type ValueVec = SmallVec<[Word; 1]>;

/// Owned value.
pub struct Value {
    width: WidthInt,
    words: ValueVec,
}

/// Abstracts over values no matter how they are stored.
trait ValueKind {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];
}

impl ValueKind for Value {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}
