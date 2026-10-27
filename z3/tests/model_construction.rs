//! Tests for building models by hand with `Model::new`, `Model::add_const_interp` and
//! `Model::add_func_interp`, and for querying them with `Model::has_interp`.

use z3::ast::{Array, Ast, Bool, Int};
use z3::*;

fn int_fn(name: &str, arity: usize) -> FuncDecl {
    let int = Sort::int();
    let domain = vec![&int; arity];
    FuncDecl::new(name, &domain, &int)
}

#[test]
fn new_model_is_empty() {
    let x = Int::new_const("x");
    let f = int_fn("f", 1);
    let model = Model::new();

    assert_eq!(model.iter().count(), 0);
    assert!(!model.has_interp(&x.decl()));
    assert!(!model.has_interp(&f));
    assert!(model.get_interp(&x.decl()).is_none());
    assert!(model.get_interp(&f).is_none());
    assert_eq!(Model::default().iter().count(), 0);
}

#[test]
fn add_const_interp() {
    let x = Int::new_const("x");
    let model = Model::new();
    model.add_const_interp(&x.decl(), &Int::from_i64(3));

    assert!(model.has_interp(&x.decl()));
    assert_eq!(model.iter().count(), 1);
    let interp = model.get_interp(&x.decl()).unwrap();
    assert_eq!(
        interp.as_const().unwrap().as_int().unwrap().as_i64(),
        Some(3)
    );
    assert_eq!(model.get_const_interp(&x).unwrap().as_i64(), Some(3));
    assert_eq!(model.eval(&(&x + 1), false).unwrap().as_i64(), Some(4));

    // Adding again replaces the existing interpretation.
    model.add_const_interp(&x.decl(), &Int::from_i64(7));
    assert_eq!(model.iter().count(), 1);
    assert_eq!(model.get_const_interp(&x).unwrap().as_i64(), Some(7));
}

#[test]
fn add_func_interp() {
    let f = int_fn("f", 1);
    let model = Model::new();
    let f_i = model.add_func_interp(&f, &Int::from_i64(0));

    assert!(model.has_interp(&f));
    assert_eq!(f_i.get_arity(), 1);
    assert_eq!(f_i.get_num_entries(), 0);
    assert_eq!(f_i.get_else().unwrap().as_int().unwrap().as_i64(), Some(0));

    // Entries added to the returned `FuncInterp` are reflected in the model.
    f_i.add_entry(&[Int::from_i64(1).into()], &Int::from_i64(10).into());
    f_i.add_entry(&[Int::from_i64(2).into()], &Int::from_i64(20).into());
    let from_model = model.get_func_interp(&f).unwrap();
    assert_eq!(from_model.get_num_entries(), 2);
    assert_eq!(from_model.to_string(), f_i.to_string());

    let at = |k: i64| {
        let app = f.apply(&[&Int::from_i64(k)]);
        model.eval(&app, false).unwrap().as_int().unwrap().as_i64()
    };
    assert_eq!(at(1), Some(10));
    assert_eq!(at(2), Some(20));
    assert_eq!(at(3), Some(0));
}

#[test]
fn add_func_interp_multi_arg() {
    let g = int_fn("g", 2);
    let model = Model::new();
    let g_i = model.add_func_interp(&g, &Int::from_i64(-1));
    g_i.add_entry(
        &[Int::from_i64(1).into(), Int::from_i64(2).into()],
        &Int::from_i64(3).into(),
    );

    assert_eq!(g_i.get_arity(), 2);
    let entry = &g_i.get_entries()[0];
    assert_eq!(entry.get_num_args(), 2);
    assert_eq!(entry.get_value().as_int().unwrap().as_i64(), Some(3));

    let at = |a: i64, b: i64| {
        let app = g.apply(&[&Int::from_i64(a), &Int::from_i64(b)]);
        model.eval(&app, false).unwrap().as_int().unwrap().as_i64()
    };
    assert_eq!(at(1, 2), Some(3));
    assert_eq!(at(2, 1), Some(-1));
}

#[test]
fn constructed_model_satisfies_formula() {
    let x = Int::new_const("x");
    let f = int_fn("f", 1);
    let model = Model::new();
    model.add_const_interp(&x.decl(), &Int::from_i64(5));
    model
        .add_func_interp(&f, &Int::from_i64(0))
        .add_entry(&[Int::from_i64(5).into()], &Int::from_i64(6).into());

    // f(x) == x + 1
    let fml = f.apply(&[&x]).as_int().unwrap().eq(&x + 1);
    assert_eq!(model.eval(&fml, false).unwrap().as_bool(), Some(true));
    let fml = f.apply(&[&(&x + 1)]).as_int().unwrap().eq(&x + 2);
    assert_eq!(model.eval(&fml, false).unwrap().as_bool(), Some(false));
}

#[test]
fn has_interp_on_solver_model() {
    let x = Int::new_const("x");
    let y = Int::new_const("y");
    let f = int_fn("f", 1);
    let g = int_fn("g", 1);
    let solver = Solver::new();
    solver.assert(x.eq(1));
    solver.assert(f.apply(&[&x]).as_int().unwrap().eq(2));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    assert!(model.has_interp(&x.decl()));
    assert!(model.has_interp(&f));
    assert!(!model.has_interp(&y.decl()));
    assert!(!model.has_interp(&g));
}

#[test]
/// A deterministic version of `tests/model_as_array.rs`, which relies on Z3 choosing to keep
/// an as-array value in a solver-produced model.
fn as_array_const_interp_resolves_to_func_interp() {
    let f = int_fn("f", 1);
    let a = Array::new_const("a", &Sort::int(), &Sort::int());
    let model = Model::new();
    model
        .add_func_interp(&f, &Int::from_i64(0))
        .add_entry(&[Int::from_i64(1).into()], &Int::from_i64(10).into());
    model.add_const_interp(&a.decl(), &f.as_array());

    // `get_interp` returns the as-array value itself...
    let a_value = model.get_interp(&a.decl()).unwrap();
    let a_value = a_value.as_const().unwrap().as_array().unwrap();
    assert!(a_value.is_as_array());
    assert_eq!(a_value.as_array_func_decl().unwrap().name(), "f");

    // ...`get_func_interp` resolves it to `f`'s interpretation...
    let a_fi = model.get_func_interp(&a.decl()).unwrap();
    assert_eq!(
        a_fi.to_string(),
        model.get_func_interp(&f).unwrap().to_string()
    );

    // ...and it is still usable as an array value.
    let sel = |k: i64| {
        let v = model.eval(&a.select(&Int::from_i64(k)), false).unwrap();
        v.as_int().unwrap().as_i64()
    };
    assert_eq!(sel(1), Some(10));
    assert_eq!(sel(2), Some(0));
}

#[test]
fn as_array_func_decl_is_none_for_other_arrays() {
    let model = Model::new();
    let a = Array::new_const("a", &Sort::int(), &Sort::int());
    let k = Array::const_array(&Sort::int(), &Int::from_i64(1));
    model.add_const_interp(&a.decl(), &k);

    assert!(!a.is_as_array());
    assert!(a.as_array_func_decl().is_none());
    assert!(!k.is_as_array());
    assert!(model.get_interp(&a.decl()).unwrap().as_const().is_some());
    assert!(model.get_func_interp(&a.decl()).is_none());
}

#[test]
#[should_panic(expected = "arity-0")]
fn add_const_interp_rejects_function() {
    Model::new().add_const_interp(&int_fn("f", 1), &Int::from_i64(0));
}

#[test]
#[should_panic(expected = "sort does not match")]
fn add_const_interp_rejects_wrong_sort() {
    let x = Int::new_const("x");
    Model::new().add_const_interp(&x.decl(), &Bool::from_bool(true));
}

#[test]
#[should_panic(expected = "arity > 0")]
fn add_func_interp_rejects_constant() {
    let x = Int::new_const("x");
    Model::new().add_func_interp(&x.decl(), &Int::from_i64(0));
}

#[test]
#[should_panic(expected = "sort does not match")]
fn add_func_interp_rejects_wrong_sort() {
    Model::new().add_func_interp(&int_fn("f", 1), &Bool::from_bool(true));
}
