//! Tests for partial function interpretations, i.e. ones without an `else` value.
//!
//! Z3 only produces these when the global `model.partial` parameter is enabled. Global
//! parameters affect every context in the process, so these tests live in their own test
//! binary to avoid leaking the setting into other tests.

use z3::ast::{self, Int};
use z3::*;

/// Returns a model with `f(0) = 1` and `f(1) = 2` and no `else` value for `f`.
fn partial_model(f: &FuncDecl) -> Model {
    set_global_param("model.partial", "true");
    let solver = Solver::new();
    solver.assert(
        f.apply(vec![ast::Dynamic::from_ast(&Int::from_i64(0))])
            .as_int()
            .unwrap()
            .eq(1),
    );
    solver.assert(
        f.apply(vec![ast::Dynamic::from_ast(&Int::from_i64(1))])
            .as_int()
            .unwrap()
            .eq(2),
    );
    assert_eq!(solver.check(), SatResult::Sat);
    solver.get_model().unwrap()
}

fn int_fn(name: &str) -> FuncDecl {
    FuncDecl::new(name, vec![Sort::int().as_dyn()], Sort::int().as_dyn())
}

#[test]
/// <https://github.com/prove-rs/z3.rs/issues/460>
fn partial_func_interp_has_no_else() {
    let f = int_fn("f");
    let model = partial_model(&f);
    let f_i = model.get_func_interp(&f).unwrap();

    assert!(f_i.get_else().is_none());
    assert!(f_i.to_string().ends_with("else -> <partial>]"));

    let mut entries: Vec<(i64, i64)> = f_i
        .get_entries()
        .iter()
        .map(|e| {
            let args = e.get_args();
            assert_eq!(args.len(), 1);
            (
                args[0].as_int().unwrap().as_i64().unwrap(),
                e.get_value().as_int().unwrap().as_i64().unwrap(),
            )
        })
        .collect();
    entries.sort();
    assert_eq!(entries, vec![(0, 1), (1, 2)]);
}

#[test]
fn partial_func_interp_eval_without_completion_is_symbolic() {
    let f = int_fn("f");
    let model = partial_model(&f);
    let at_5 = f
        .apply(vec![ast::Dynamic::from_ast(&Int::from_i64(5))])
        .as_int()
        .unwrap();

    // Covered by an entry: evaluates to a value either way.
    let at_0 = f
        .apply(vec![ast::Dynamic::from_ast(&Int::from_i64(0))])
        .as_int()
        .unwrap();
    assert_eq!(model.eval(&at_0, false).unwrap().as_i64(), Some(1));

    // Not covered and no `else`: stays symbolic without completion...
    let v = model.eval(&at_5, false).unwrap();
    assert_eq!(v.as_i64(), None);
    assert_eq!(v, at_5);

    // ...and gets a concrete value with completion.
    let v = model.eval(&at_5, true).unwrap();
    assert!(v.as_i64().is_some());
}

#[test]
fn set_else_completes_partial_func_interp() {
    let f = int_fn("f");
    let model = partial_model(&f);
    let f_i = model.get_func_interp(&f).unwrap();
    assert!(f_i.get_else().is_none());

    f_i.set_else(&Int::from_i64(42).into());

    assert_eq!(f_i.get_else().unwrap().as_int().unwrap().as_i64(), Some(42));
    // `set_else` mutates the interpretation held by the model.
    let at_5 = f
        .apply(vec![ast::Dynamic::from_ast(&Int::from_i64(5))])
        .as_int()
        .unwrap();
    assert_eq!(model.eval(&at_5, false).unwrap().as_i64(), Some(42));
    assert!(
        model
            .get_func_interp(&f)
            .unwrap()
            .to_string()
            .ends_with("else -> 42]")
    );
}
