// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};
use smallvec::SmallVec;

type ValueVec = SmallVec<[Word; 1]>;

/// Owned value.
pub struct ValueOwned {
    width: WidthInt,
    words: ValueVec,
}

pub struct ValueRef<'a> {
    width: WidthInt,
    words: &'a [Word],
}

pub struct ValueMutRef<'a> {
    width: WidthInt,
    words: &'a mut [Word],
}

type WordIndex = u32;

pub struct ValueIndexed {
    width: WidthInt,
    index: WordIndex,
}

pub trait ValueStorage {
    fn words(&self, index: WordIndex) -> &[Word];
    fn words_mut(&mut self, index: WordIndex) -> &mut [Word];
}

impl ValueIndexed {
    pub fn as_ref<'a>(&self, storage: &'a impl ValueStorage) -> ValueRef<'a> {
        ValueRef {
            width: self.width,
            words: storage.words(self.index),
        }
    }

    pub fn as_mut<'a>(&self, storage: &'a mut impl ValueStorage) -> ValueMutRef<'a> {
        ValueMutRef {
            width: self.width,
            words: storage.words_mut(self.index),
        }
    }
}

/// Abstracts over values no matter how they are stored.
pub trait Value {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];
}

impl Value for ValueOwned {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}
