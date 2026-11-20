//! Z3 reports failures only through an error code; these tests check that the safe API
//! surfaces them instead of continuing with garbage or silently dropped input.

use z3::ast::Int;
use z3::{
    DatatypeAccessor, DatatypeBuilder, Error, ErrorCode, Fixedpoint, Optimize, Params, SatResult,
    Solver, Tactic,
};

const BAD_SMTLIB: &str = "(declare-const x Int) (assert (= x 5)) (assert (= x 6)) (assert (bogus))";

fn invalid_params() -> Params {
    let mut p = Params::new();
    p.set_bool("no_such_param", true);
    p
}

/// `n` mutually recursive datatypes with no base case, which Z3 rejects.
fn non_well_founded_builders(n: usize) -> Vec<DatatypeBuilder> {
    (0..n)
        .map(|i| {
            DatatypeBuilder::new(format!("T{i}")).variant(
                &format!("c{i}"),
                vec![("f", DatatypeAccessor::datatype(format!("T{}", (i + 1) % n)))],
            )
        })
        .collect()
}

#[test]
fn test_non_well_founded_datatype_finish_is_error() {
    let err = non_well_founded_builders(1)
        .pop()
        .unwrap()
        .finish()
        .unwrap_err();
    assert!(matches!(err, Error::Z3 { .. }));
}

#[test]
fn test_solver_invalid_params_are_rejected_without_dropping_assertions() {
    let s = Solver::new();
    assert!(s.set_params(&invalid_params()).is_err());
    let x = Int::new_const("x");
    s.assert(x.eq(5));
    s.assert(x.eq(6));
    assert_eq!(s.check(), SatResult::Unsat);
}

#[test]
fn test_solver_valid_params_are_accepted() {
    let s = Solver::new();
    let mut p = Params::new();
    p.set_u32("timeout", 10_000);
    s.set_params(&p).unwrap();
    s.assert(Int::new_const("x").eq(5));
    assert_eq!(s.check(), SatResult::Sat);
}

#[test]
fn test_solver_load_smtlib2_parse_error_is_reported() {
    let s = Solver::new();
    assert!(matches!(
        s.load_smtlib2(BAD_SMTLIB),
        Err(Error::Z3 {
            code: ErrorCode::ParserError,
            ..
        })
    ));
    assert!(matches!(
        s.load_smtlib2("(assert true)\0"),
        Err(Error::InteriorNul(_))
    ));
    s.load_smtlib2("(declare-const x Int) (assert (= x 5))")
        .unwrap();
    assert_eq!(s.get_assertions().len(), 1);
}

#[test]
fn test_solver_pop_beyond_scopes_is_error() {
    let s = Solver::new();
    s.push();
    assert!(s.pop(2).is_err());
    s.pop(1).unwrap();
}

#[test]
fn test_optimize_load_smtlib2_parse_error_is_reported() {
    let o = Optimize::new();
    assert!(o.load_smtlib2(BAD_SMTLIB).is_err());
    o.load_smtlib2("(declare-const x Int) (assert (= x 5))")
        .unwrap();
    assert_eq!(o.check(&[]), SatResult::Sat);
}

#[test]
fn test_optimize_invalid_params_are_rejected() {
    assert!(Optimize::new().set_params(&invalid_params()).is_err());
}

#[test]
fn test_fixedpoint_invalid_params_are_rejected() {
    assert!(Fixedpoint::new().set_params(&invalid_params()).is_err());
}

#[test]
fn test_fixedpoint_load_smtlib2_parse_error_is_reported() {
    let fp = Fixedpoint::new();
    assert!(
        fp.load_smtlib2("(declare-rel p ()) (rule (bogus))")
            .is_err()
    );
    let queries = fp
        .load_smtlib2("(declare-rel p ()) (rule p) (query p)")
        .unwrap();
    assert_eq!(queries.len(), 1);
}

#[test]
fn test_tactic_with_invalid_param_is_error() {
    assert!(Tactic::new("simplify").with(&invalid_params()).is_err());
    let mut p = Params::new();
    p.set_bool("elim_and", true);
    Tactic::new("simplify").with(&p).unwrap();
}
