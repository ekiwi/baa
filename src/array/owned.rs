// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::{BitVecValue, WidthInt, Word};
use std::collections::HashMap;

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
}

impl ArrayMutOps for ArrayValue {}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct DenseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: DenseArrayImpl,
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum DenseArrayImpl {
    Bit(BitVecValue),
    U8(Vec<u8>),
    U64(Vec<u64>),
    Big(Vec<Word>),
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct SparseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: SparseArrayImpl,
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum SparseArrayImpl {
    U64U64(u64, HashMap<u64, u64>),
    U64Big(BitVecValue, HashMap<u64, BitVecValue>),
    BigBig(BitVecValue, HashMap<BitVecValue, BitVecValue>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // Dense Array Size
        assert_eq!(std::mem::size_of::<Vec<u8>>(), 24);
        assert_eq!(std::mem::size_of::<BitVecValue>(), 32);
        assert_eq!(std::mem::size_of::<DenseArrayImpl>(), 40); // BitVecValue size + tag + padding
        assert_eq!(std::mem::size_of::<DenseArrayValue>(), 48); // Impl + size + padding

        // Sparse Array Size

        // the hash table size is independent of the key/value types
        assert_eq!(std::mem::size_of::<HashMap<u64, u64>>(), 48);
        assert_eq!(std::mem::size_of::<HashMap<u64, BitVecValue>>(), 48);
        assert_eq!(std::mem::size_of::<HashMap<BitVecValue, BitVecValue>>(), 48);

        // HashMap + BitVecValue + tag + padding
        assert_eq!(std::mem::size_of::<SparseArrayImpl>(), 48 + 32 + 8);
        assert_eq!(std::mem::size_of::<SparseArrayValue>(), 88 + 8); // Impl + size + padding
    }
}
