// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{ArrayValueRef, BitVecValueRef};

/// Array or BitVec value reference.
pub enum ValueRef<'a> {
    BitVec(BitVecValueRef<'a>),
    Array(ArrayValueRef<'a>),
}

impl<'a> TryFrom<ValueRef<'a>> for BitVecValueRef<'a> {
    type Error = ();

    fn try_from(value: ValueRef<'a>) -> Result<Self, Self::Error> {
        match value {
            ValueRef::BitVec(bv) => Ok(bv),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<ValueRef<'a>> for ArrayValueRef<'a> {
    type Error = ();

    fn try_from(value: ValueRef<'a>) -> Result<Self, Self::Error> {
        match value {
            ValueRef::Array(a) => Ok(a),
            _ => Err(()),
        }
    }
}

impl<'a> From<BitVecValueRef<'a>> for ValueRef<'a> {
    fn from(value: BitVecValueRef<'a>) -> Self {
        ValueRef::BitVec(value)
    }
}

impl<'a> From<ArrayValueRef<'a>> for ValueRef<'a> {
    fn from(value: ArrayValueRef<'a>) -> Self {
        ValueRef::Array(value)
    }
}
