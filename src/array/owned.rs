// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::{BitVecOps, BitVecValue, BitVecValueRef, WidthInt, Word};
use std::collections::HashMap;

/// Owned Array Container.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub enum ArrayValue {
    Sparse(SparseArrayValue),
    Dense(DenseArrayValue),
}

impl From<SparseArrayValue> for ArrayValue {
    fn from(value: SparseArrayValue) -> Self {
        ArrayValue::Sparse(value)
    }
}

impl From<DenseArrayValue> for ArrayValue {
    fn from(value: DenseArrayValue) -> Self {
        ArrayValue::Dense(value)
    }
}

// impl ArrayOps for ArrayValue {
//     fn index_width(&self) -> WidthInt {
//         self.index_width
//     }
//
//     fn data_width(&self) -> WidthInt {
//         self.data_width
//     }
// }
//
// impl ArrayMutOps for ArrayValue {}

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

impl SparseArrayValue {
    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    fn is_equal(&self, other: &SparseArrayValue) -> Option<bool> {
        if other.index_width != self.index_width || other.data_width != self.data_width {
            return None;
        }
        match (&self.data, &other.data) {
            (
                SparseArrayImpl::U64U64(default_a, map_a),
                SparseArrayImpl::U64U64(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            (
                SparseArrayImpl::U64Big(default_a, map_a),
                SparseArrayImpl::U64Big(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            (
                SparseArrayImpl::BigBig(default_a, map_a),
                SparseArrayImpl::BigBig(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            _ => unreachable!(
                "the representation for two arrays of the same type should always be the same!"
            ),
        }
    }
}

impl ArrayOps for SparseArrayValue {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }
    fn data_width(&self) -> WidthInt {
        self.data_width
    }
    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        match &self.data {
            SparseArrayImpl::U64U64(default, map) => {
                let index = index.to_u64().unwrap();
                let value = map.get(&index).copied().unwrap_or(*default);
                BitVecValue::from_u64(value, self.data_width)
            }
            SparseArrayImpl::U64Big(default, map) => {
                let index = index.to_u64().unwrap();
                let value = map.get(&index).cloned().unwrap_or_else(|| default.clone());
                value
            }
            SparseArrayImpl::BigBig(default, map) => {
                let value = map.get(&index).cloned().unwrap_or_else(|| default.clone());
                value
            }
        }
    }
}

impl ArrayMutOps for SparseArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        let data = data.into();
        debug_assert_eq!(data.width(), self.data_width);
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                let index = index.to_u64().unwrap();
                let data = data.to_u64().unwrap();
                if data == *default {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data);
                }
            }
            SparseArrayImpl::U64Big(default, map) => {
                let index = index.to_u64().unwrap();
                if data.is_equal(default) {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data.into());
                }
            }
            SparseArrayImpl::BigBig(default, map) => {
                if data.is_equal(default) {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index.into(), data.into());
                }
            }
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                *default = 0;
                map.clear();
            }
            SparseArrayImpl::U64Big(default, map) => {
                *default = BitVecValue::zero(self.data_width);
                map.clear();
            }
            SparseArrayImpl::BigBig(default, map) => {
                *default = BitVecValue::zero(self.data_width);
                map.clear();
            }
        }
    }
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
