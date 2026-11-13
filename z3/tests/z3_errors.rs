//! Z3 reports failures only through an error code; these tests check that the safe API
//! surfaces them instead of continuing with garbage or silently dropped input.

use std::process::Command;
use z3::ast::Int;
use z3::datatype_builder::create_datatypes;
use z3::{
    DatatypeAccessor, DatatypeBuilder, ErrorCode, Fixedpoint, Optimize, Params, SatResult, Solver,
    Tactic, Z3Error,
};

const BAD_SMTLIB: &str = "(declare-const x Int) (assert (= x 5)) (assert (= x 6)) (assert (bogus))";

/// Runs `body` in a child process so that memory corruption shows up as a failed
/// test instead of taking down the whole test binary.
fn run_isolated(name: &str, body: fn()) {
    if std::env::var("Z3_ISOLATED_TEST").as_deref() == Ok(name) {
        body();
        return;
    }
    let out = Command::new(std::env::current_exe().unwrap())
        .args([name, "--exact", "--nocapture", "--test-threads=1"])
        .env("Z3_ISOLATED_TEST", name)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "child process failed: {}\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
}

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
fn test_non_well_founded_datatypes_do_not_read_uninitialized_sorts() {
    run_isolated(
        "test_non_well_founded_datatypes_do_not_read_uninitialized_sorts",
        || {
            const N: usize = 6;
            let builders = non_well_founded_builders(N);
            // Leave non-null garbage in freed allocations of the size `create_datatypes`
            // uses for its output buffer, so reading it uninitialized fails loudly.
            drop(
                (0..256)
                    .map(|_| vec![0x4141_4141_4141_4140usize; N])
                    .collect::<Vec<_>>(),
            );
            assert!(create_datatypes(builders).is_err());
        },
    );
}

#[test]
fn test_non_well_founded_datatype_finish_is_error() {
    let err = non_well_founded_builders(1)
        .pop()
        .unwrap()
        .finish()
        .unwrap_err();
    assert!(matches!(err, Z3Error::Z3 { .. }));
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
fn test_solver_from_string_parse_error_is_reported() {
    let s = Solver::new();
    assert!(matches!(
        s.from_string(BAD_SMTLIB),
        Err(Z3Error::Z3 {
            code: ErrorCode::ParserError,
            ..
        })
    ));
    assert!(matches!(
        s.from_string("(assert true)\0"),
        Err(Z3Error::InteriorNul(_))
    ));
    s.from_string("(declare-const x Int) (assert (= x 5))")
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
fn test_optimize_from_string_parse_error_is_reported() {
    let o = Optimize::new();
    assert!(o.from_string(BAD_SMTLIB).is_err());
    o.from_string("(declare-const x Int) (assert (= x 5))")
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
fn test_fixedpoint_from_string_parse_error_is_reported() {
    let fp = Fixedpoint::new();
    assert!(fp.from_string("(declare-rel p ()) (rule (bogus))").is_err());
    fp.from_string("(declare-rel p ()) (rule p)").unwrap();
}

#[test]
fn test_tactic_with_invalid_param_is_error() {
    assert!(Tactic::new("simplify").with(&invalid_params()).is_err());
    let mut p = Params::new();
    p.set_bool("elim_and", true);
    Tactic::new("simplify").with(&p).unwrap();
}
