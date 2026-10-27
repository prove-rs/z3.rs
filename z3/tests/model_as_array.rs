//! Tests for array constants whose model value is an "as-array" alias for another
//! function's interpretation, e.g. `(_ as-array k!0)`.
//!
//! Z3 usually compacts these away; disabling the global `model.compact` parameter makes it
//! keep them. Global parameters affect every context in the process, so these tests live in
//! their own test binary to avoid leaking the setting into other tests.

use z3::ast::{Array, Ast, Int};
use z3::*;

#[test]
fn as_array_const_is_const_interp_and_resolves_to_func_interp() {
    set_global_param("model.compact", "false");
    let a = Array::new_const("a", &Sort::int(), &Sort::int());
    let b = Array::new_const("b", &Sort::int(), &Sort::int());
    let solver = Solver::new();
    for k in 0..3 {
        solver.assert(a.select(&Int::from_i64(k)).as_int().unwrap().eq(k * 10 + 1));
    }
    solver.assert(a.eq(&b).not());
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    // Both array constants are `Interp::Const`, however Z3 chose to represent their value.
    let a_interp = model.get_interp(&a.decl()).unwrap();
    let b_interp = model.get_interp(&b.decl()).unwrap();
    let a_value = a_interp.as_const().unwrap();
    assert!(b_interp.as_const().is_some());

    // `a`'s value is an as-array alias, which `get_func_interp` resolves to a function table.
    assert!(a_value.to_string().starts_with("(_ as-array"));
    let a_fi = model.get_func_interp(&a.decl()).unwrap();
    assert_eq!(a_fi.get_arity(), 1);
    assert!(a_fi.get_else().is_some());

    // The const value is still usable as an array value.
    let a_value = a_value.as_array().unwrap();
    for k in 0..3 {
        let v = model
            .eval(&a_value.select(&Int::from_i64(k)), true)
            .unwrap();
        assert_eq!(v.as_int().unwrap().as_i64(), Some(k * 10 + 1));
    }
}
