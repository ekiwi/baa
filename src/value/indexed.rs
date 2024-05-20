// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Access a slice of `Word` as a bit-vector.

use super::borrowed::{BitVecValueMutRef, BitVecValueRef};
use crate::{WidthInt, Word};

type WordIndex = u32;

#[derive(Debug)]
pub struct ValueIndexed {
    width: WidthInt,
    index: WordIndex,
}

pub trait ValueStorage {
    fn words(&self, index: WordIndex) -> &[Word];
    fn words_mut(&mut self, index: WordIndex) -> &mut [Word];
}

impl ValueIndexed {
    pub fn as_ref<'a>(&self, storage: &'a impl ValueStorage) -> BitVecValueRef<'a> {
        todo!()
        // BitVecValueRef {
        //     width: self.width,
        //     words: storage.words(self.index),
        // }
    }

    pub fn as_mut<'a>(&self, storage: &'a mut impl ValueStorage) -> BitVecValueMutRef<'a> {
        todo!()
        // BitVecValueMutRef {
        //     width: self.width,
        //     words: storage.words_mut(self.index),
        // }
    }
}
