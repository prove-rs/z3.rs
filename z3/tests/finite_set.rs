// Requires Z3 >= 5.0.0 (auto-detected; see z3/build.rs).
#![cfg(z3_5_0_0)]

use z3::ast::{self, Ast};
use z3::{SatResult, Solver, Sort};

#[test]
fn test_finite_set_membership() {
    let _ = env_logger::try_init();

    let solver = Solver::new();
    let one = ast::Int::from_u64(1);
    let two = ast::Int::from_u64(2);

    let empty = ast::FiniteSet::empty(&Sort::int());
    solver.push();
    solver.assert(empty.member(&one));
    // An empty set never contains 1
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);

    let singleton_one = ast::FiniteSet::singleton(&one);
    solver.push();
    solver.assert(singleton_one.member(&one));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    solver.push();
    solver.assert(singleton_one.member(&two).not());
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    let unioned = singleton_one.union(ast::FiniteSet::singleton(&two));
    solver.push();
    solver.assert(unioned.member(&one));
    solver.assert(unioned.member(&two));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    solver.push();
    solver.assert(singleton_one.subset(&unioned));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    let intersected = singleton_one.intersect(ast::FiniteSet::singleton(&two));
    solver.push();
    solver.assert(intersected.eq(ast::FiniteSet::empty(&Sort::int())));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    let diffed = unioned.difference(&singleton_one);
    solver.push();
    solver.assert(diffed.eq(ast::FiniteSet::singleton(&two)));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);
}

#[test]
fn test_finite_set_size_and_range() {
    let _ = env_logger::try_init();

    let solver = Solver::new();
    let zero = ast::Int::from_u64(0);
    let two = ast::Int::from_u64(2);

    solver.push();
    solver.assert(ast::FiniteSet::empty(&Sort::int()).size().eq(&zero));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    let one = ast::Int::from_u64(1);
    solver.push();
    solver.assert(
        ast::FiniteSet::singleton(&one)
            .size()
            .eq(ast::Int::from_u64(1)),
    );
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    let range = ast::FiniteSet::range(&zero, &two);
    solver.push();
    solver.assert(range.member(&zero));
    solver.assert(range.member(&ast::Int::from_u64(1)));
    solver.assert(range.member(&two));
    solver.assert(range.size().eq(ast::Int::from_u64(3)));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    solver.push();
    solver.assert(range.member(&ast::Int::from_i64(-1)));
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);
}

#[test]
fn test_finite_set_map_filter() {
    let _ = env_logger::try_init();

    let one = ast::Int::from_u64(1);
    let two = ast::Int::from_u64(2);
    let range = ast::FiniteSet::range(&one, &two);

    // `f` must be an Array (Z3 represents function values structurally as
    // arrays); a constant array is the simplest one.
    //
    // This only checks construction/sort correctness, not satisfiability:
    // as of Z3 5.1.0, asking the solver to reason about the *contents* of a
    // `set.map`/`set.filter` result (e.g. via membership or equality) hangs
    // indefinitely, even with a `timeout` param set (verified independently
    // via raw SMT-LIB2 against the `z3` CLI, so this isn't a bindings bug).
    let const_42 = ast::Array::const_array(&Sort::int(), &ast::Int::from_u64(42));
    let mapped = range.map(&const_42);
    assert_eq!(mapped.get_sort(), Sort::finite_set(&Sort::int()));

    let always_true = ast::Array::const_array(&Sort::int(), &ast::Bool::from_bool(true));
    let filtered = range.filter(&always_true);
    assert_eq!(filtered.get_sort(), Sort::finite_set(&Sort::int()));
}

#[test]
fn test_dynamic_as_finite_set() {
    let _ = env_logger::try_init();

    let finite_set_sort = Sort::finite_set(&Sort::int());
    let array_of_finite_sets =
        ast::Array::new_const("array_of_finite_sets", &Sort::int(), &finite_set_sort);
    let array_of_sets = ast::Array::new_const(
        "array_of_sets",
        &Sort::int(),
        &Sort::array(&Sort::int(), &Sort::bool()),
    );
    assert!(
        array_of_finite_sets
            .select(&ast::Int::from_u64(0))
            .as_finite_set()
            .is_some()
    );
    assert!(
        array_of_sets
            .select(&ast::Int::from_u64(0))
            .as_finite_set()
            .is_none()
    );
}

#[test]
fn test_sort_finite_set() {
    let int_sort = Sort::int();
    let finite_set_sort = Sort::finite_set(&int_sort);
    assert!(finite_set_sort.is_finite_set());
    assert!(!int_sort.is_finite_set());
    assert_eq!(finite_set_sort.finite_set_basis().unwrap(), int_sort);
    assert!(int_sort.finite_set_basis().is_none());
}
