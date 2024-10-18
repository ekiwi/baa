// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::{
    BitVecMutOps, BitVecOps, BitVecValue, BitVecValueMutRef, BitVecValueRef, WidthInt, Word,
};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

/// Owned Array Container.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct ArrayValue {
    data: ArrayImpl,
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum ArrayImpl {
    Sparse(SparseArrayValue),
    Dense(DenseArrayValue),
}

impl Debug for ArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.data {
            ArrayImpl::Sparse(s) => s.fmt(f),
            ArrayImpl::Dense(d) => d.fmt(f),
        }
    }
}

impl ArrayValue {
    pub fn new_dense<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let data = ArrayImpl::Dense(DenseArrayValue::new(index_width, default));
        Self { data }
    }
    pub fn new_sparse<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let data = ArrayImpl::Sparse(SparseArrayValue::new(index_width, default));
        Self { data }
    }

    pub fn is_dense(&self) -> bool {
        matches!(self.data, ArrayImpl::Dense(_))
    }

    pub fn is_sparse(&self) -> bool {
        matches!(self.data, ArrayImpl::Sparse(_))
    }

    /// Turns the underlying storage into a dense representation if it is not already.
    pub fn make_dense(&mut self) {
        if self.is_dense() {
            // nothing to do
            return;
        }

        let value: DenseArrayValue = match &self.data {
            ArrayImpl::Dense(_) => {
                unreachable!("should have passed the self.is_dense check earlier!");
            }
            ArrayImpl::Sparse(data) => data.into(),
        };
        self.data = ArrayImpl::Dense(value);
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    pub fn is_equal(&self, other: &Self) -> Option<bool> {
        match (&self.data, &other.data) {
            (ArrayImpl::Dense(a), ArrayImpl::Dense(b)) => a.is_equal(b),
            (ArrayImpl::Sparse(a), ArrayImpl::Sparse(b)) => a.is_equal(b),
            (ArrayImpl::Sparse(a), ArrayImpl::Dense(b)) => is_equal_mixed(b, a),
            (ArrayImpl::Dense(a), ArrayImpl::Sparse(b)) => is_equal_mixed(a, b),
        }
    }
}

impl PartialEq<ArrayValue> for ArrayValue {
    fn eq(&self, other: &ArrayValue) -> bool {
        self.is_equal(other).unwrap_or_default()
    }
}

fn is_equal_mixed(dense: &DenseArrayValue, sparse: &SparseArrayValue) -> Option<bool> {
    // check early to avoid costly computations
    if dense.index_width != sparse.index_width || dense.data_width != sparse.data_width {
        return None;
    }

    // TODO: implement more efficient version which does not densify
    DenseArrayValue::from(sparse).is_equal(dense)
}

impl ArrayOps for ArrayValue {
    fn index_width(&self) -> WidthInt {
        match &self.data {
            ArrayImpl::Sparse(v) => v.index_width(),
            ArrayImpl::Dense(v) => v.index_width(),
        }
    }

    fn data_width(&self) -> WidthInt {
        match &self.data {
            ArrayImpl::Sparse(v) => v.data_width(),
            ArrayImpl::Dense(v) => v.data_width(),
        }
    }

    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        match &self.data {
            ArrayImpl::Sparse(v) => v.select(index),
            ArrayImpl::Dense(v) => v.select(index),
        }
    }
}

impl ArrayMutOps for ArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        match &mut self.data {
            ArrayImpl::Sparse(v) => v.store(index, data),
            ArrayImpl::Dense(v) => v.store(index, data),
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            ArrayImpl::Sparse(v) => v.clear(),
            ArrayImpl::Dense(v) => v.clear(),
        }
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
struct DenseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: DenseArrayImpl,
}

impl Debug for DenseArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "DenseArrayValue(..)")
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum DenseArrayImpl {
    Bit(BitVecValue),
    U8(Vec<u8>),
    U64(Vec<u64>),
    Big(Vec<Word>),
}

/// 1 GiB max for a dense array, otherwise something is fishy!
const DENSE_ARRAY_MAX_BYTES: usize = 1 * 1024 * 1024 * 1024;

fn approx_dense_storage_size(index_width: WidthInt, data_width: WidthInt) -> usize {
    let elements = 1usize << index_width;
    if data_width == 1 {
        // using the Bit representation
        elements.div_ceil(u8::BITS as usize)
    } else if data_width <= u8::BITS {
        // using the U8 representation
        elements
    } else if data_width <= u64::BITS {
        // using the U64 representation
        elements * (u64::BITS / u8::BITS) as usize
    } else {
        // using the Big representation
        elements * data_width.div_ceil(Word::BITS) as usize
    }
}

impl DenseArrayValue {
    fn new<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let default = default.into();
        let data_width = default.width;
        let storage_size = approx_dense_storage_size(index_width, data_width);
        debug_assert!(
            storage_size <= DENSE_ARRAY_MAX_BYTES,
            "array would take up too much space: {storage_size} bytes"
        );

        let elements = 1usize << index_width;
        let data = if data_width == 1 {
            if default.is_tru() {
                DenseArrayImpl::Bit(BitVecValue::ones(data_width))
            } else {
                debug_assert!(default.is_fals());
                DenseArrayImpl::Bit(BitVecValue::zero(data_width))
            }
        } else if data_width <= u8::BITS {
            let default = default.to_u64().unwrap() as u8;
            DenseArrayImpl::U8(vec![default; elements])
        } else if data_width <= u64::BITS {
            let default = default.to_u64().unwrap();
            DenseArrayImpl::U64(vec![default; elements])
        } else {
            let mut v = Vec::with_capacity(elements * default.words().len());
            for _ in 0..elements {
                v.extend_from_slice(default.words());
            }
            DenseArrayImpl::Big(v)
        };
        Self {
            index_width,
            data_width,
            data,
        }
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    fn is_equal(&self, other: &Self) -> Option<bool> {
        if other.index_width != self.index_width || other.data_width != self.data_width {
            return None;
        }
        match (&self.data, &other.data) {
            (DenseArrayImpl::Bit(value_a), DenseArrayImpl::Bit(value_b)) => {
                Some(value_a.is_equal(value_b))
            }
            (DenseArrayImpl::U8(values_a), DenseArrayImpl::U8(values_b)) => {
                Some(values_a == values_b)
            }
            (DenseArrayImpl::U64(values_a), DenseArrayImpl::U64(values_b)) => {
                Some(values_a == values_b)
            }
            (DenseArrayImpl::Big(values_a), DenseArrayImpl::Big(values_b)) => {
                Some(values_a == values_b)
            }
            _ => unreachable!(
                "the representation for two arrays of the same type should always be the same!"
            ),
        }
    }
}

impl ArrayOps for DenseArrayValue {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }

    fn data_width(&self) -> WidthInt {
        self.data_width
    }

    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        let index = index.to_u64().unwrap() as usize;
        match &self.data {
            DenseArrayImpl::Bit(value) => value.is_bit_set(index as WidthInt).into(),
            DenseArrayImpl::U8(values) => {
                BitVecValue::from_u64(values[index] as u64, self.data_width)
            }
            DenseArrayImpl::U64(values) => BitVecValue::from_u64(values[index], self.data_width),
            DenseArrayImpl::Big(values) => {
                let start = self.words_per_element() * index;
                let end = start + self.words_per_element();
                let value_ref = BitVecValueRef::new(self.data_width(), &values[start..end]);
                value_ref.into()
            }
        }
    }
}

impl ArrayMutOps for DenseArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        let index = index.to_u64().unwrap() as usize;
        let data = data.into();
        debug_assert_eq!(data.width(), self.data_width);
        let data_width = self.data_width();
        let words_per_element = self.words_per_element();
        match &mut self.data {
            DenseArrayImpl::Bit(value) => {
                if data.is_tru() {
                    value.set_bit(index as WidthInt);
                } else {
                    value.clear_bit(index as WidthInt);
                }
            }
            DenseArrayImpl::U8(values) => {
                values[index] = data.to_u64().unwrap() as u8;
            }
            DenseArrayImpl::U64(values) => {
                values[index] = data.to_u64().unwrap();
            }
            DenseArrayImpl::Big(values) => {
                let start = words_per_element * index;
                let end = start + words_per_element;
                let mut value_ref = BitVecValueMutRef::new(data_width, &mut values[start..end]);
                value_ref.assign(data);
            }
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            DenseArrayImpl::Bit(value) => value.clear(),
            DenseArrayImpl::U8(values) => values.iter_mut().for_each(|v| *v = 0),
            DenseArrayImpl::U64(values) => values.iter_mut().for_each(|v| *v = 0),
            DenseArrayImpl::Big(values) => values.iter_mut().for_each(|v| *v = 0),
        }
    }
}

impl From<&SparseArrayValue> for DenseArrayValue {
    fn from(value: &SparseArrayValue) -> Self {
        let mut dense = Self::new(value.index_width, &value.default());
        debug_assert_eq!(value.data_width, dense.data_width);
        debug_assert_eq!(value.index_width, dense.index_width);
        match &value.data {
            SparseArrayImpl::U64U64(_, m) => {
                for (index, v) in m.iter() {
                    match &mut dense.data {
                        DenseArrayImpl::Bit(value) => {
                            if *v == 1 {
                                value.set_bit(*index as WidthInt);
                            } else {
                                debug_assert_eq!(*v, 0);
                                value.clear_bit(*index as WidthInt);
                            }
                        }
                        DenseArrayImpl::U8(values) => {
                            values[*index as usize] = *v as u8;
                        }
                        DenseArrayImpl::U64(values) => {
                            values[*index as usize] = *v;
                        }
                        DenseArrayImpl::Big(_) => {
                            unreachable!("data_width does not match")
                        }
                    }
                }
            }
            SparseArrayImpl::U64Big(_, m) => {
                let mut index_bv = BitVecValue::zero(value.data_width);
                for (k, v) in m.iter() {
                    index_bv.assign_from_u64(*k);
                    dense.store(&index_bv, v);
                }
            }
            SparseArrayImpl::BigBig(_, _) => {
                unreachable!(
                    "index size is too large, creating the dense array should have failed!"
                )
            }
        }
        dense
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
struct SparseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: SparseArrayImpl,
}

impl Debug for SparseArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SparseArrayValue(..)")
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum SparseArrayImpl {
    U64U64(u64, HashMap<u64, u64>),
    U64Big(BitVecValue, HashMap<u64, BitVecValue>),
    BigBig(BitVecValue, HashMap<BitVecValue, BitVecValue>),
}

impl SparseArrayValue {
    fn new<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let default = default.into();
        let data_width = default.width;
        let data = if index_width > Word::BITS {
            SparseArrayImpl::BigBig(default.into(), HashMap::new())
        } else if data_width > Word::BITS {
            SparseArrayImpl::U64Big(default.into(), HashMap::new())
        } else {
            SparseArrayImpl::U64U64(default.to_u64().unwrap(), HashMap::new())
        };
        Self {
            index_width,
            data_width,
            data,
        }
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    fn is_equal(&self, other: &Self) -> Option<bool> {
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

    fn default(&self) -> BitVecValue {
        match &self.data {
            SparseArrayImpl::U64U64(default, _) => BitVecValue::from_u64(*default, self.data_width),
            SparseArrayImpl::U64Big(default, _) => default.clone(),
            SparseArrayImpl::BigBig(default, _) => default.clone(),
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
