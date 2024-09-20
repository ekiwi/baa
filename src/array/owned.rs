// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::{WidthInt, Word};

/// Owned dense bit-vector array.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct ArrayValue {
    pub(crate) index_width: WidthInt,
    pub(crate) data_width: WidthInt,
    pub(crate) words: Vec<Word>,
}

impl ArrayOps for ArrayValue {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }

    fn data_width(&self) -> WidthInt {
        self.data_width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}

impl ArrayMutOps for ArrayValue {
    fn words_mut(&mut self) -> &mut [Word] {
        &mut self.words
    }
}
