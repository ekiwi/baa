// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::*;
use proptest::prelude::*;

#[test]
fn i64_roundtrip_regression() {
    assert_eq!(BitVecValue::from_i64(0, 64).to_i64().unwrap(), 0);
    assert_eq!(BitVecValue::from_i64(-1, 64).to_i64().unwrap(), -1);
}

proptest! {

    #[test]
    fn i64_roundtrip(value: i64) {
        let bitvec = BitVecValue::from_i64(value, 64);
        assert_eq!(bitvec.to_i64().unwrap(), value);
    }

    #[test]
    fn u64_roundtrip(value: u64) {
        let bitvec = BitVecValue::from_u64(value, 64);
        assert_eq!(bitvec.to_u64().unwrap(), value);
    }
}
