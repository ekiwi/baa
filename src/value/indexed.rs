// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Access a slice of `Word` as a bit-vector.

use super::borrowed::{BitVecValueMutRef, BitVecValueRef};
use crate::{WidthInt, Word};

type WordIndex = u32;

#[derive(Debug)]
pub struct BitVecValueIndex {
    width: WidthInt,
    index: WordIndex,
}

impl BitVecValueIndex {
    fn new(index: WordIndex, width: WidthInt) -> Self {
        Self { index, width }
    }

    #[inline]
    fn words(&self) -> usize {
        self.width.div_ceil(Word::BITS) as usize
    }

    #[inline]
    fn to_range(&self) -> std::ops::Range<usize> {
        let start = self.index as usize;
        let end = start + self.words();
        start..end
    }
}

pub struct ValueStorage<'a> {
    values: &'a mut [Word],
}

impl<'a, T: AsMut<[Word]>> From<&'a mut T> for ValueStorage<'a> {
    #[inline]
    fn from(value: &'a mut T) -> Self {
        Self {
            values: value.as_mut(),
        }
    }
}

pub trait GetOneRef {
    fn get_ref(&self, index: &BitVecValueIndex) -> BitVecValueRef;
    fn get_mut(&mut self, index: &BitVecValueIndex) -> BitVecValueMutRef;
}

impl<'a> GetOneRef for ValueStorage<'a> {
    fn get_ref(&self, index: &BitVecValueIndex) -> BitVecValueRef {
        BitVecValueRef {
            width: index.width,
            words: &self.values[index.to_range()],
        }
    }
    fn get_mut(&mut self, index: &BitVecValueIndex) -> BitVecValueMutRef {
        BitVecValueMutRef {
            width: index.width,
            words: &mut self.values[index.to_range()],
        }
    }
}

pub trait GetTwoRef {
    fn get_ref(
        &self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
    ) -> (BitVecValueRef, BitVecValueRef);
    fn get_mut(
        &mut self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
    ) -> (BitVecValueMutRef, BitVecValueRef);
}

impl<'a> GetTwoRef for ValueStorage<'a> {
    fn get_ref(
        &self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
    ) -> (BitVecValueRef, BitVecValueRef) {
        todo!()
    }

    fn get_mut(
        &mut self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
    ) -> (BitVecValueMutRef, BitVecValueRef) {
        todo!()
    }
}

pub trait GetThreeRef {
    fn get_ref(
        &self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
        c: &BitVecValueIndex,
    ) -> (BitVecValueRef, BitVecValueRef, BitVecValueRef);
    fn get_mut(
        &mut self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
        c: &BitVecValueIndex,
    ) -> (BitVecValueMutRef, BitVecValueRef, BitVecValueRef);
}

impl<'a> GetThreeRef for ValueStorage<'a> {
    fn get_ref(
        &self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
        c: &BitVecValueIndex,
    ) -> (BitVecValueRef, BitVecValueRef, BitVecValueRef) {
        todo!()
    }

    fn get_mut(
        &mut self,
        a: &BitVecValueIndex,
        b: &BitVecValueIndex,
        c: &BitVecValueIndex,
    ) -> (BitVecValueMutRef, BitVecValueRef, BitVecValueRef) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        assert_eq!(std::mem::size_of::<WordIndex>(), 4);
        assert_eq!(std::mem::size_of::<BitVecValueIndex>(), 8);
    }

    #[test]
    fn test_array_access() {
        {
            let mut backend = [0; 16];
            let storage: ValueStorage = (&mut backend).into();
            // let (a,b) = storage.get_ref(BitVecValueIndex::new(0, 8), BitVecValueIndex::new(1, 8));
            // let c = a.add(b);
        }
    }
}
