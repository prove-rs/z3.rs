//! Tests for building models by hand with `Model::new` and `Model::add_const_interp`, and
//! for querying them with `Model::has_interp`.

use z3::ast::{self, Array, Ast, Bool, Int};
use z3::*;

fn int_fn(name: &str, arity: usize) -> FuncDecl {
    FuncDecl::new(
        name,
        vec![Sort::int().as_dyn(); arity],
        Sort::int().as_dyn(),
    )
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
fn has_interp_on_solver_model() {
    let x = Int::new_const("x");
    let y = Int::new_const("y");
    let f = int_fn("f", 1);
    let g = int_fn("g", 1);
    let solver = Solver::new();
    solver.assert(x.eq(1));
    solver.assert(
        f.apply(vec![ast::Dynamic::from_ast(&x)])
            .as_int()
            .unwrap()
            .eq(2),
    );
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    assert!(model.has_interp(&x.decl()));
    assert!(model.has_interp(&f));
    assert!(!model.has_interp(&y.decl()));
    assert!(!model.has_interp(&g));
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
