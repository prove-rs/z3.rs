// Requires Z3 >= 5.0.0 (auto-detected; see z3/build.rs).
#![cfg(z3_5_0_0)]

use z3::ast::{self, Ast, SortMarker};
use z3::{AstVector, SatResult, Solver, Sort};

fn int(n: i64) -> ast::Int {
    ast::Int::from_i64(n)
}

/// Narrow an untyped value (e.g. the `Array` built by `lambda_const`) to the statically-typed `T`.
fn typed<T: SortMarker>(a: &impl Ast) -> T {
    ast::Dynamic::from_ast(a).narrow().unwrap()
}

/// Build the finite set `{elems...}` out of singletons and unions.
fn set_of(elems: &[i64]) -> ast::FiniteSet<ast::Int> {
    elems
        .iter()
        .fold(ast::FiniteSet::empty(&Sort::int()), |acc, &e| {
            acc.union(ast::FiniteSet::singleton(&int(e)))
        })
}

/// Assert that `claim` holds in every model, i.e. its negation is unsat.
#[track_caller]
fn prove(claim: &ast::Bool) {
    let solver = Solver::new();
    solver.assert(claim.not());
    assert_eq!(solver.check(), SatResult::Unsat, "failed to prove {claim}");
}

#[test]
fn test_finite_set_membership() {
    let _ = env_logger::try_init();

    let empty = ast::FiniteSet::empty(&Sort::int());
    prove(&empty.member(&int(1)).not());

    let singleton_one = ast::FiniteSet::singleton(&int(1));
    prove(&singleton_one.member(&int(1)));
    prove(&singleton_one.member(&int(2)).not());

    let one_two = set_of(&[1, 2]);
    prove(&one_two.member(&int(1)));
    prove(&one_two.member(&int(2)));
    prove(&one_two.member(&int(3)).not());
}

#[test]
fn test_finite_set_operations() {
    let _ = env_logger::try_init();

    let r = |lo, hi| ast::FiniteSet::range(&int(lo), &int(hi));

    prove(&r(0, 1).union(r(2, 3)).eq(r(0, 3)));

    prove(&r(0, 3).intersect(r(2, 5)).eq(r(2, 3)));
    prove(
        &set_of(&[1])
            .intersect(set_of(&[2]))
            .eq(ast::FiniteSet::empty(&Sort::int())),
    );

    // Difference is not symmetric; check both directions so swapped
    // arguments would be caught.
    prove(&r(0, 3).difference(r(2, 5)).eq(r(0, 1)));
    prove(&r(2, 5).difference(r(0, 3)).eq(r(4, 5)));

    prove(&set_of(&[1]).subset(set_of(&[1, 2])));
    prove(&set_of(&[1, 2]).subset(set_of(&[1])).not());
    prove(&ast::FiniteSet::empty(&Sort::int()).subset(set_of(&[1])));
}

#[test]
fn test_finite_set_size_and_range() {
    let _ = env_logger::try_init();

    prove(&ast::FiniteSet::empty(&Sort::int()).size().eq(int(0)));
    prove(&set_of(&[1]).size().eq(int(1)));
    // Duplicates collapse.
    prove(&set_of(&[1, 1]).size().eq(int(1)));
    // Note: as of Z3 5.3.1, `set.size` of a union of distinct singletons
    // (e.g. `{1, 2}`) returns unknown (the `z3` CLI hits an internal
    // assertion), so sizes of larger sets are only checked via `range`.

    // `range` is inclusive on both ends.
    let range = ast::FiniteSet::range(&int(0), &int(2));
    prove(&range.size().eq(int(3)));
    prove(&range.eq(set_of(&[0, 1, 2])));
    prove(&range.member(&int(-1)).not());
    prove(&range.member(&int(3)).not());

    // An inverted range is empty.
    prove(&ast::FiniteSet::range(&int(2), &int(0)).eq(ast::FiniteSet::empty(&Sort::int())));
}

#[test]
fn test_finite_set_map() {
    let _ = env_logger::try_init();

    // Note: as of Z3 5.3.1 the solver cannot decide queries about `set.map`
    // applied to a `set.range` (the check does not return), so these tests map
    // over sets built from singletons instead. This reproduces with raw
    // SMT-LIB2 against the `z3` CLI, so it isn't a bindings bug.
    let one_two = set_of(&[1, 2]);

    let x = ast::Int::new_const("x");
    let plus_ten: ast::Array<ast::Int, ast::Int> = typed(&ast::lambda_const(
        &[&x],
        &ast::Dynamic::from_ast(&(&x + int(10))),
    ));
    let mapped = one_two.map(&plus_ten);
    prove(&mapped.eq(set_of(&[11, 12])));
    prove(&mapped.member(&int(1)).not());

    // A non-injective function collapses the image.
    let const_42 = ast::Array::const_array(&Sort::int(), &int(42));
    prove(&one_two.map(&const_42).eq(set_of(&[42])));

    // The result element sort is the function's range, not `eltype`.
    let gt_one: ast::Array<ast::Int, ast::Bool> = typed(&ast::lambda_const(
        &[&x],
        &ast::Dynamic::from_ast(&x.gt(int(1))),
    ));
    let bools = one_two.map(&gt_one);
    assert_eq!(bools.get_sort(), Sort::finite_set(&Sort::bool()));
    let expected = ast::FiniteSet::singleton(&ast::Bool::from_bool(false))
        .union(ast::FiniteSet::singleton(&ast::Bool::from_bool(true)));
    prove(&bools.eq(expected));
}

#[test]
fn test_finite_set_filter() {
    let _ = env_logger::try_init();

    let range = ast::FiniteSet::range(&int(1), &int(3));

    let x = ast::Int::new_const("x");
    let gt_one: ast::Array<ast::Int, ast::Bool> = typed(&ast::lambda_const(
        &[&x],
        &ast::Dynamic::from_ast(&x.gt(int(1))),
    ));
    let filtered = range.filter(&gt_one);
    prove(&filtered.eq(ast::FiniteSet::range(&int(2), &int(3))));
    prove(&filtered.member(&int(1)).not());

    let always_true = ast::Array::const_array(&Sort::int(), &ast::Bool::from_bool(true));
    prove(&range.filter(&always_true).eq(&range));

    let always_false = ast::Array::const_array(&Sort::int(), &ast::Bool::from_bool(false));
    prove(
        &range
            .filter(&always_false)
            .eq(ast::FiniteSet::empty(&Sort::int())),
    );
}

#[test]
fn test_finite_set_constants() {
    let _ = env_logger::try_init();

    let s = ast::FiniteSet::new_const("s", &Sort::int());
    let t = ast::FiniteSet::new_const("t", &Sort::int());
    assert_eq!(s.get_sort(), Sort::finite_set(&Sort::int()));

    // A subset of {1} that contains 1 must be {1}.
    prove(
        &ast::Bool::and(&[s.subset(set_of(&[1])), s.member(&int(1))]).implies(s.eq(set_of(&[1]))),
    );

    // Membership in a subset propagates to the superset.
    prove(&s.member(&int(5)).implies(s.union(&t).member(&int(5))));
    // ...and is excluded by an incompatible subset constraint.
    prove(&ast::Bool::and(&[s.member(&int(5)), s.subset(set_of(&[1]))]).not());

    // Membership constraints alone are satisfiable. We don't inspect the
    // model: as of Z3 5.3.1 the model evaluator does not reduce finite set
    // operations, and the reported model for `s` can violate the constraints.
    let solver = Solver::new();
    solver.assert(s.member(&int(5)));
    solver.assert(s.member(&int(6)).not());
    assert_eq!(solver.check(), SatResult::Sat);

    let a = ast::FiniteSet::fresh_const("s", &Sort::int());
    let b = ast::FiniteSet::fresh_const("s", &Sort::int());
    assert_ne!(a, b);
    assert_eq!(a.get_sort(), Sort::finite_set(&Sort::int()));
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
    let elem = ast::Dynamic::from_ast(&array_of_finite_sets.select(&int(0)));
    let as_set = elem.as_finite_set().unwrap();
    assert_eq!(ast::Dynamic::from_ast(&as_set), elem);
    assert!(elem.narrow::<ast::FiniteSet<ast::Int>>().is_some());
    assert!(elem.narrow::<ast::FiniteSet<ast::Bool>>().is_none());
    assert!(
        ast::Dynamic::from_ast(&array_of_sets.select(&int(0)))
            .as_finite_set()
            .is_none()
    );
    assert!(ast::Dynamic::from_ast(&int(0)).as_finite_set().is_none());
}

#[test]
fn test_sort_finite_set() {
    let int_sort = Sort::int();
    let finite_set_sort = Sort::finite_set(&int_sort);
    assert!(finite_set_sort.narrow::<ast::FiniteSet>().is_some());
    assert!(int_sort.narrow::<ast::FiniteSet>().is_none());
    // Array-backed sets are not finite sets.
    assert!(Sort::set(&int_sort).narrow::<ast::FiniteSet>().is_none());
    assert!(
        finite_set_sort
            .narrow::<ast::FiniteSet<ast::Int>>()
            .is_some()
    );
    assert!(
        finite_set_sort
            .narrow::<ast::FiniteSet<ast::Bool>>()
            .is_none()
    );
    assert_eq!(finite_set_sort.basis(), int_sort);
    assert_eq!(Sort::finite_set(&Sort::bool()).basis(), Sort::bool());
}

#[test]
fn test_finite_set_try_from_ast_vector() {
    let a = ast::FiniteSet::new_const("a", &Sort::int());
    let b = ast::FiniteSet::new_const("b", &Sort::int());
    let v: AstVector = [a.clone(), b.clone()].into_iter().collect();
    let sets: Vec<ast::FiniteSet<ast::Int>> = Vec::<ast::FiniteSet>::try_from(v)
        .unwrap()
        .iter()
        .map(typed)
        .collect();
    assert_eq!(sets, vec![a, b]);

    let mixed: AstVector = [ast::Dynamic::from_ast(&int(1))].into_iter().collect();
    assert!(Vec::<ast::FiniteSet>::try_from(mixed).is_err());
}
