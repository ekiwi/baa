// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::*;

#[test]
fn test_sparse_array_conversion_and_access() {
    let dense: ArrayValue = [1u8, 0, 2, 0, 3, 0, 5, 0].as_slice().into();
    let sparse: SparseArrayValue = dense.into();
    assert_eq!(sparse.default(), BitVecValue::from_u64(0, 8));
    let mut entries = sparse
        .non_default_entries()
        .map(|(k, v)| (k.to_u64().unwrap(), v.to_u64().unwrap()))
        .collect::<Vec<_>>();
    entries.sort_by_key(|(k, _)| *k);
    assert_eq!(entries, [(0, 1), (2, 2), (4, 3), (6, 5)]);
}
