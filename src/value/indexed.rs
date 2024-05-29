// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Access a slice of `Word` as a bit-vector.

use super::borrowed::{BitVecValueMutRef, BitVecValueRef};
use crate::{WidthInt, Word};

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

impl AsRef<BitVecValueIndex> for BitVecValueIndex {
    fn as_ref(&self) -> &BitVecValueIndex {
        &self
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
    I: AsRef<BitVecValueIndex>,
{
    fn get_ref(self, index: I) -> BitVecValueRef<'a> {
        BitVecValueRef {
            width: index.as_ref().width,
            words: &self[index.as_ref().to_range()],
        }
    }
}

impl<'a, I> GetBitVecRef<(I, I), (BitVecValueRef<'a>, BitVecValueRef<'a>)> for &'a [Word]
where
    I: AsRef<BitVecValueIndex>,
{
    fn get_ref(self, (a, b): (I, I)) -> (BitVecValueRef<'a>, BitVecValueRef<'a>) {
        (
            BitVecValueRef {
                width: a.as_ref().width,
                words: &self[a.as_ref().to_range()],
            },
            BitVecValueRef {
                width: b.as_ref().width,
                words: &self[b.as_ref().to_range()],
            },
        )
    }
}

pub trait GetBitVecMutRef<I, O> {
    fn get_mut_ref(self, index: I) -> O;
}

impl<'a, I> GetBitVecMutRef<I, BitVecValueMutRef<'a>> for &'a mut [Word]
where
    I: AsRef<BitVecValueIndex>,
{
    fn get_mut_ref(self, index: I) -> BitVecValueMutRef<'a> {
        BitVecValueMutRef {
            width: index.as_ref().width,
            words: &mut self[index.as_ref().to_range()],
        }
    }
}

impl<'a, I> GetBitVecMutRef<(I, I), (BitVecValueMutRef<'a>, BitVecValueRef<'a>)>
    for &'a mut [Word]
where
    I: AsRef<BitVecValueIndex>,
{
    fn get_mut_ref(self, (a, b): (I, I)) -> (BitVecValueMutRef<'a>, BitVecValueRef<'a>) {
        let (a_words, b_words) = split_borrow_1(self, a.as_ref().to_range(), b.as_ref().to_range());

        (
            BitVecValueMutRef {
                width: a.as_ref().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.as_ref().width,
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
    I: AsRef<BitVecValueIndex>,
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
            a.as_ref().to_range(),
            b.as_ref().to_range(),
            c.as_ref().to_range(),
        );

        (
            BitVecValueMutRef {
                width: a.as_ref().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.as_ref().width,
                words: b_words,
            },
            BitVecValueRef {
                width: c.as_ref().width,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BitVecMutOps;

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
            a.set_from_word(1234);
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
}
