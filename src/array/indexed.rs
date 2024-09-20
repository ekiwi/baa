// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::borrowed::{ArrayValueMutRef, ArrayValueRef};
use crate::{BitVecValueIndex, IndexToMutRef, IndexToRef, WidthInt, Word};
use std::borrow::Borrow;

/// Index of an array value in a shared value store.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ArrayValueIndex {
    pub(super) first: BitVecValueIndex,
    pub(super) index_width: WidthInt,
}

impl ArrayValueIndex {
    pub fn new(first: BitVecValueIndex, index_width: WidthInt) -> Self {
        Self { first, index_width }
    }
}

impl ArrayValueIndex {
    #[inline]
    pub fn num_elements(&self) -> usize {
        1usize << self.index_width
    }

    #[inline]
    pub fn words(&self) -> usize {
        self.first.words() * self.num_elements()
    }

    #[inline]
    pub fn to_range(&self) -> std::ops::Range<usize> {
        let start = self.first.index as usize;
        let end = start + self.words();
        start..end
    }

    #[inline]
    pub fn first_element_index(&self) -> BitVecValueIndex {
        self.first
    }
}

impl<'a, I> IndexToRef<I, ArrayValueRef<'a>> for &'a [Word]
where
    I: Borrow<ArrayValueIndex>,
{
    fn get_ref(self, index: I) -> ArrayValueRef<'a> {
        ArrayValueRef {
            index_width: index.borrow().index_width,
            data_width: index.borrow().first.width(),
            words: &self[index.borrow().to_range()],
        }
    }
}

impl<'a, I> IndexToMutRef<I, ArrayValueMutRef<'a>> for &'a mut [Word]
where
    I: Borrow<ArrayValueIndex>,
{
    fn get_mut_ref(self, index: I) -> ArrayValueMutRef<'a> {
        ArrayValueMutRef {
            index_width: index.borrow().index_width,
            data_width: index.borrow().first.width(),
            words: &mut self[index.borrow().to_range()],
        }
    }
}

impl<'a, I1, I2> IndexToMutRef<(I1, I2), (ArrayValueMutRef<'a>, ArrayValueRef<'a>)>
    for &'a mut [Word]
where
    I1: Borrow<ArrayValueIndex>,
    I2: Borrow<ArrayValueIndex>,
{
    fn get_mut_ref(self, (a, b): (I1, I2)) -> (ArrayValueMutRef<'a>, ArrayValueRef<'a>) {
        let (a_words, b_words) =
            crate::bv::split_borrow_1(self, a.borrow().to_range(), b.borrow().to_range());

        (
            ArrayValueMutRef {
                index_width: a.borrow().index_width,
                data_width: a.borrow().first.width(),
                words: a_words,
            },
            ArrayValueRef {
                index_width: b.borrow().index_width,
                data_width: b.borrow().first.width(),
                words: b_words,
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArrayMutOps, BitVecValue};

    #[test]
    fn type_size() {
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        assert_eq!(std::mem::size_of::<ArrayValueIndex>(), 12);
    }

    #[test]
    fn test_array_index() {
        let mut backend = [0; 32];

        // a four element array with 2-word entries
        let a0 = BitVecValueIndex::new(1, 65);
        let a = a0.to_array_index(2);
        assert_eq!(a.num_elements(), 4);
        assert_eq!(a.words(), 8);
        assert_eq!(a.to_range(), 1..9);

        // another array of the same size
        let b = BitVecValueIndex::new(9, 65).to_array_index(2);

        // set some elements
        {
            let mut a = backend.get_mut_ref(a);
            a.store(
                &BitVecValue::from_u64(1, 2),
                &BitVecValue::from_u64(1234, 65),
            );
            a.store(
                &BitVecValue::from_u64(3, 2),
                &BitVecValue::from_u64(555555, 65),
            );
        }
        assert_eq!(backend[2 + 1], 1234);
        assert_eq!(backend[3 + 1], 0);
        assert_eq!(backend[6 + 1], 555555);
        assert_eq!(backend[7 + 1], 0);

        // check b array storage and initialize to magic value
        for ii in 9..(9 + 2 * 4) {
            assert_eq!(backend[ii], 0);
            backend[ii] = 99999;
        }

        // assign b := a
        {
            let (mut b, a) = backend.get_mut_ref((b, a));
            b.assign(a);
        }

        // check new b values
        assert_eq!(backend[2 + 9], 1234);
        assert_eq!(backend[3 + 9], 0);
        assert_eq!(backend[6 + 9], 555555);
        assert_eq!(backend[7 + 9], 0);
    }
}
