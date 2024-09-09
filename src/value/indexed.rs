// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Access a slice of `Word` as a bit-vector.

use super::borrowed::{BitVecValueMutRef, BitVecValueRef};
use crate::{BitVecOps, WidthInt, Word};
use std::borrow::Borrow;
use std::collections::HashMap;

type WordIndex = u32;

#[derive(Debug, Copy, Clone)]
pub struct BitVecValueIndex {
    width: WidthInt,
    index: WordIndex,
}

impl BitVecValueIndex {
    #[inline]
    pub fn new(index: WordIndex, width: WidthInt) -> Self {
        Self { index, width }
    }

    #[inline]
    pub fn words(&self) -> usize {
        self.width.div_ceil(Word::BITS) as usize
    }

    #[inline]
    pub fn to_range(&self) -> std::ops::Range<usize> {
        let start = self.index as usize;
        let end = start + self.words();
        start..end
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ArrayValueIndex {
    first: BitVecValueIndex,
    index_width: WidthInt,
}

pub trait GetBitVecRef<I, O> {
    fn get_ref(self, index: I) -> O;
}

impl<'a, I> GetBitVecRef<I, BitVecValueRef<'a>> for &'a [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, index: I) -> BitVecValueRef<'a> {
        BitVecValueRef {
            width: index.borrow().width,
            words: &self[index.borrow().to_range()],
        }
    }
}

impl<'a, I> GetBitVecRef<(I, I), (BitVecValueRef<'a>, BitVecValueRef<'a>)> for &'a [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, (a, b): (I, I)) -> (BitVecValueRef<'a>, BitVecValueRef<'a>) {
        (
            BitVecValueRef {
                width: a.borrow().width,
                words: &self[a.borrow().to_range()],
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: &self[b.borrow().to_range()],
            },
        )
    }
}

pub trait GetBitVecMutRef<I, O> {
    fn get_mut_ref(self, index: I) -> O;
}

impl<'a, I> GetBitVecMutRef<I, BitVecValueMutRef<'a>> for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(self, index: I) -> BitVecValueMutRef<'a> {
        BitVecValueMutRef {
            width: index.borrow().width,
            words: &mut self[index.borrow().to_range()],
        }
    }
}

impl<'a, I> GetBitVecMutRef<(I, I), (BitVecValueMutRef<'a>, BitVecValueRef<'a>)>
    for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(self, (a, b): (I, I)) -> (BitVecValueMutRef<'a>, BitVecValueRef<'a>) {
        let (a_words, b_words) = split_borrow_1(self, a.borrow().to_range(), b.borrow().to_range());

        (
            BitVecValueMutRef {
                width: a.borrow().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: b_words,
            },
        )
    }
}

impl<'a, I>
    GetBitVecMutRef<
        (I, I, I),
        (
            BitVecValueMutRef<'a>,
            BitVecValueRef<'a>,
            BitVecValueRef<'a>,
        ),
    > for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(
        self,
        (a, b, c): (I, I, I),
    ) -> (
        BitVecValueMutRef<'a>,
        BitVecValueRef<'a>,
        BitVecValueRef<'a>,
    ) {
        let (a_words, b_words, c_words) = split_borrow_2(
            self,
            a.borrow().to_range(),
            b.borrow().to_range(),
            c.borrow().to_range(),
        );

        (
            BitVecValueMutRef {
                width: a.borrow().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: b_words,
            },
            BitVecValueRef {
                width: c.borrow().width,
                words: c_words,
            },
        )
    }
}

#[inline]
fn split_borrow_1(
    data: &mut [Word],
    dst: std::ops::Range<usize>,
    src: std::ops::Range<usize>,
) -> (&mut [Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let src_words = if src.start >= after_dst_offset {
        &after_dst[move_range(src, after_dst_offset)]
    } else {
        &before_dst[src]
    };
    (dst_words, src_words)
}

#[inline]
fn move_range(rng: std::ops::Range<usize>, offset: usize) -> std::ops::Range<usize> {
    std::ops::Range {
        start: rng.start - offset,
        end: rng.end - offset,
    }
}

#[inline]
fn split_borrow_2(
    data: &mut [Word],
    dst: std::ops::Range<usize>,
    src_a: std::ops::Range<usize>,
    src_b: std::ops::Range<usize>,
) -> (&mut [Word], &[Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let a_words = if src_a.start >= after_dst_offset {
        &after_dst[move_range(src_a, after_dst_offset)]
    } else {
        &before_dst[src_a]
    };
    let b_words = if src_b.start >= after_dst_offset {
        &after_dst[move_range(src_b, after_dst_offset)]
    } else {
        &before_dst[src_b]
    };
    (dst_words, a_words, b_words)
}

/// Ensures that each bit vector value gets a unique index. And each combination of value and
/// width will get a unique BitVecValueIndex
pub struct BitVecValueInterner {
    words: Vec<Word>,
    small: HashMap<Word, WordIndex>,
    large: HashMap<Box<[Word]>, WordIndex>,
}

impl Default for BitVecValueInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl BitVecValueInterner {
    pub fn new() -> Self {
        // initialize with some important constants
        let words = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let small = HashMap::new();
        let large = HashMap::new();
        Self {
            words,
            small,
            large,
        }
    }

    pub fn is_zero<I: Borrow<BitVecValueIndex>>(index: I) -> bool {
        index.borrow().index == 0
    }

    pub fn is_one<I: Borrow<BitVecValueIndex>>(index: I) -> bool {
        index.borrow().index == 1
    }

    pub fn get_index<I: BitVecOps>(&mut self, value: I) -> BitVecValueIndex {
        let (words, width) = (value.words(), value.width());
        if let &[word] = words {
            debug_assert!(width <= Word::BITS);
            if word < 8 {
                BitVecValueIndex::new(word as WordIndex, width)
            } else if let Some(index) = self.small.get(&word) {
                BitVecValueIndex::new(*index, width)
            } else {
                let index = self.words.len() as WordIndex;
                self.words.push(word);
                self.small.insert(word, index);
                BitVecValueIndex::new(index, width)
            }
        } else {
            debug_assert!(width > Word::BITS);
            if let Some(index) = self.large.get(words) {
                BitVecValueIndex::new(*index, width)
            } else {
                let index = self.words.len() as WordIndex;
                self.words.extend_from_slice(words);
                self.large.insert(Box::from(words), index);
                BitVecValueIndex::new(index, width)
            }
        }
    }
}

impl<'a, I> GetBitVecRef<I, BitVecValueRef<'a>> for &'a BitVecValueInterner
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, index: I) -> BitVecValueRef<'a> {
        (&self.words).get_ref(index)
    }
}

impl<'a, I> GetBitVecRef<(I, I), (BitVecValueRef<'a>, BitVecValueRef<'a>)>
    for &'a BitVecValueInterner
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, index: (I, I)) -> (BitVecValueRef<'a>, BitVecValueRef<'a>) {
        (&self.words).get_ref(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVecMutOps, BitVecValue};

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
            let (mut a, _b) =
                backend.get_mut_ref((BitVecValueIndex::new(0, 8), BitVecValueIndex::new(1, 8)));
            a.assign(&BitVecValue::from_u64(1234, 8));
            assert_eq!(backend[0], 1234);
        }
    }

    #[test]
    fn test_split_borrow() {
        let data: &mut [Word] = &mut [0, 1, 2, 3];
        let (dst, src) = split_borrow_1(data, 0..1, 2..4);
        assert_eq!(dst, &[0]);
        assert_eq!(src, &[2, 3]);
        let (dst2, src2) = split_borrow_1(data, 2..4, 0..2);
        assert_eq!(dst2, &[2, 3]);
        assert_eq!(src2, &[0, 1]);

        let (dst3, src_a_3, src_b_3) = split_borrow_2(data, 2..4, 1..2, 0..2);
        assert_eq!(dst3, &[2, 3]);
        assert_eq!(src_a_3, &[1]);
        assert_eq!(src_b_3, &[0, 1]);
    }

    #[test]
    fn test_interner() {
        let mut i = BitVecValueInterner::new();
        assert_eq!(i.get_index(BitVecValue::tru()).index, 1);
        assert_eq!(i.get_index(BitVecValue::fals()).index, 0);
        assert_eq!(i.get_index(BitVecValue::from_u64(0, 4)).index, 0);
        assert!(BitVecValueInterner::is_zero(
            i.get_index(BitVecValue::from_u64(0, 4))
        ));
        assert!(!BitVecValueInterner::is_one(
            i.get_index(BitVecValue::from_u64(0, 4))
        ));
        assert!(BitVecValueInterner::is_one(
            i.get_index(BitVecValue::from_u64(1, 4))
        ));
    }

    use num_bigint::*;
    use proptest::prelude::*;

    #[cfg(feature = "bigint")]
    fn interner_should_return_same_value(value: &BigInt, width: WidthInt) {
        let mut intern = BitVecValueInterner::new();
        let i0 = intern.get_index(BitVecValue::from_big_int(value, width));
        let i1 = intern.get_index(BitVecValue::from_big_int(value, width));
        assert_eq!(i0.index, i1.index);
        assert_eq!(i0.width, i1.width);
        let v0 = intern.get_ref(i0);
        assert_eq!(BitVecValue::from_big_int(value, width), v0);
    }

    #[allow(unused)]
    fn gen_big_int_and_width() -> impl Strategy<Value = (BigInt, WidthInt)> {
        let max_bits = 16 * Word::BITS;
        (1..max_bits)
            .prop_flat_map(|width| (crate::arithmetic::tests::gen_big_int(width), Just(width)))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        #[test]
        #[cfg(feature = "bigint")]
        fn prop_test_interner((value, width) in gen_big_int_and_width()) {
            interner_should_return_same_value(&value, width);
        }
    }
}
