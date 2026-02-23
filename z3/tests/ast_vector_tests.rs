use std::convert::TryInto;
use z3::ast::{Bool, Dynamic, Int, Real};
use z3::{AstVector, Solver};

// ---------------------------------------------------------------------------
// Iterator trait coverage
// ---------------------------------------------------------------------------

#[test]
fn iter_yields_all_elements() {
    let a = Int::new_const("a");
    let b = Int::new_const("b");
    let c = Int::new_const("c");

    let v = AstVector::from(vec![a.clone(), b.clone(), c.clone()]);
    let items: Vec<Dynamic> = v.iter().collect();

    assert_eq!(items.len(), 3);
    assert_eq!(items[0], Dynamic::from(&a));
    assert_eq!(items[1], Dynamic::from(&b));
    assert_eq!(items[2], Dynamic::from(&c));
}

#[test]
fn iter_exact_size() {
    let a = Int::new_const("x");
    let b = Int::new_const("y");
    let v = AstVector::from(vec![a, b]);
    let mut it = v.iter();

    assert_eq!(it.len(), 2);
    let _ = it.next();
    assert_eq!(it.len(), 1);
    let _ = it.next();
    assert_eq!(it.len(), 0);
    assert!(it.next().is_none());
    // FusedIterator: safe to call next() again after exhaustion
    assert!(it.next().is_none());
}

#[test]
fn into_iter_consuming_yields_all_elements() {
    let a = Bool::new_const("p");
    let b = Bool::new_const("q");
    let v = AstVector::from(vec![a.clone(), b.clone()]);

    let items: Vec<Dynamic> = v.into_iter().collect();
    assert_eq!(items.len(), 2);
    assert_eq!(items[0], Dynamic::from(&a));
    assert_eq!(items[1], Dynamic::from(&b));
}

#[test]
fn into_iter_exact_size() {
    let a = Int::new_const("u");
    let b = Int::new_const("v");
    let c = Int::new_const("w");
    let v = AstVector::from(vec![a, b, c]);
    let mut it = v.into_iter();

    assert_eq!(it.len(), 3);
    let _ = it.next();
    assert_eq!(it.len(), 2);
    let _ = it.next();
    assert_eq!(it.len(), 1);
    let _ = it.next();
    assert_eq!(it.len(), 0);
    assert!(it.next().is_none());
    assert!(it.next().is_none());
}

#[test]
fn ref_into_iter_borrows() {
    let a = Int::new_const("i1");
    let b = Int::new_const("i2");
    let v = AstVector::from(vec![a.clone(), b.clone()]);

    // &v is still usable after the loop
    let count = (&v).into_iter().count();
    assert_eq!(count, 2);
    assert_eq!(v.len(), 2);
}

// ---------------------------------------------------------------------------
// FromIterator / From conversions
// ---------------------------------------------------------------------------

#[test]
fn from_iterator_of_ast() {
    let bools: Vec<Bool> = (0..4).map(|i| Bool::new_const(format!("b{i}"))).collect();
    let v: AstVector = bools.iter().cloned().collect();
    assert_eq!(v.len(), 4);
}

#[test]
fn from_vec_of_ast() {
    let ints: Vec<Int> = (0..3).map(|i| Int::new_const(format!("n{i}"))).collect();
    let v = AstVector::from(ints.clone());
    assert_eq!(v.len(), 3);
    for (i, item) in v.iter().enumerate() {
        assert_eq!(item, Dynamic::from(&ints[i]));
    }
}

#[test]
fn from_slice_of_ast() {
    let reals: Vec<Real> = (0..2).map(|i| Real::new_const(format!("r{i}"))).collect();
    let v = AstVector::from(reals.as_slice());
    assert_eq!(v.len(), 2);
}

#[test]
fn from_empty_vec() {
    let v = AstVector::from(Vec::<Bool>::new());
    assert!(v.is_empty());
}

#[test]
fn collect_after_map() {
    let ints: Vec<Int> = (0..5).map(|i| Int::new_const(format!("m{i}"))).collect();
    let v: AstVector = ints.into_iter().collect();
    assert_eq!(v.len(), 5);
}

// ---------------------------------------------------------------------------
// try_into_typed_vec / TryFrom<AstVector>
// ---------------------------------------------------------------------------

#[test]
fn try_into_typed_vec_bool_success() {
    let bools: Vec<Bool> = (0..3).map(|i| Bool::new_const(format!("t{i}"))).collect();
    let v = AstVector::from(bools.clone());
    let result: Result<Vec<Bool>, _> = v.try_into();
    assert!(result.is_ok());
    let got = result.unwrap();
    assert_eq!(got.len(), 3);
    for (a, b) in got.iter().zip(bools.iter()) {
        assert_eq!(a, b);
    }
}

#[test]
fn try_into_typed_vec_wrong_type_fails() {
    let ints: Vec<Int> = (0..2).map(|i| Int::new_const(format!("w{i}"))).collect();
    let v = AstVector::from(ints);
    let result: Result<Vec<Bool>, _> = v.try_into();
    assert!(result.is_err());
}

#[test]
fn try_from_ast_vector_for_vec_bool() {
    let bools: Vec<Bool> = (0..2).map(|i| Bool::new_const(format!("f{i}"))).collect();
    let v = AstVector::from(bools.clone());
    let result: Result<Vec<Bool>, _> = v.try_into();
    assert!(result.is_ok());
    assert_eq!(result.unwrap().len(), 2);
}

#[test]
fn try_from_ast_vector_for_vec_int() {
    let ints: Vec<Int> = (0..3).map(|i| Int::new_const(format!("g{i}"))).collect();
    let v = AstVector::from(ints);
    let result: Result<Vec<Int>, _> = v.try_into();
    assert!(result.is_ok());
    assert_eq!(result.unwrap().len(), 3);
}

#[test]
fn try_from_ast_vector_type_mismatch_error() {
    let ints: Vec<Int> = (0..2).map(|i| Int::new_const(format!("e{i}"))).collect();
    let v = AstVector::from(ints);
    let result: Result<Vec<Bool>, _> = v.try_into();
    assert!(result.is_err());
}

#[test]
fn try_into_typed_vec_empty() {
    let v = AstVector::new();
    let result: Result<Vec<Bool>, _> = v.try_into();
    assert!(result.is_ok());
    assert!(result.unwrap().is_empty());
}

// ---------------------------------------------------------------------------
// Integration: solver APIs that use the new conversion paths
// ---------------------------------------------------------------------------

#[test]
fn solver_get_assertions_returns_correct_count() {
    let a = Bool::new_const("sa");
    let b = Bool::new_const("sb");
    let solver = Solver::new();
    solver.assert(&a);
    solver.assert(&b);
    let assertions = solver.get_assertions();
    assert_eq!(assertions.len(), 2);
}

#[test]
fn solver_get_consequences_roundtrip() {
    use z3::SatResult;

    let x = Bool::new_const("cx");
    let y = Bool::new_const("cy");
    let solver = Solver::new();
    solver.assert(&x);
    solver.assert(&y);
    assert_eq!(solver.check(), SatResult::Sat);

    // x, y as both assumptions and variables
    let consequences = solver.get_consequences(std::slice::from_ref(&x), std::slice::from_ref(&y));
    // Z3 may return an implication (x => y) or nothing; just verify no panic
    let _ = consequences;
}

#[test]
fn from_slice_idiomatic_replaces_push_loop() {
    // Previously: manual push loop; now: AstVector::from(slice)
    let bools: Vec<Bool> = (0..4).map(|i| Bool::new_const(format!("s{i}"))).collect();
    let v1 = AstVector::from(bools.as_slice());

    let v2 = AstVector::new();
    for b in &bools {
        v2.push(b);
    }

    assert_eq!(v1.len(), v2.len());
    for (a, b) in v1.iter().zip(v2.iter()) {
        assert_eq!(a, b);
    }
}
