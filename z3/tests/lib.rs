extern crate env_logger;
#[macro_use]
extern crate log;

extern crate z3;
use std::convert::TryInto;
use z3::ast::Ast;
use z3::*;

#[cfg(feature = "arbitrary-size-numeral")]
extern crate num;
#[cfg(feature = "arbitrary-size-numeral")]
use num::bigint::BigInt;
#[cfg(feature = "arbitrary-size-numeral")]
use num::rational::BigRational;
#[cfg(feature = "arbitrary-size-numeral")]
use std::str::FromStr;

#[test]
fn test_config() {
    let _ = env_logger::try_init();
    let mut c = Config::new();
    c.set_proof_generation(true);
}

#[test]
fn test_context() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    cfg.set_proof_generation(true);
    let _ = Context::new(&cfg);
}

#[test]
fn test_sorts_and_symbols() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let _ = ast::Int::new_const(&ctx, "x");
    let _ = ast::Int::new_const(&ctx, "y");
}

#[test]
fn test_solving() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_solving_for_model() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let zero = ast::Int::from_i64(&ctx, 0);
    let two = ast::Int::from_i64(&ctx, 2);
    let seven = ast::Int::from_i64(&ctx, 7);

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    solver.assert(&y.gt(&zero));
    solver.assert(&y.rem(&seven)._eq(&two));
    let x_plus_two = x.add(&[&two]);
    solver.assert(&x_plus_two.gt(&seven));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model();
    let xv = model.eval(&x).unwrap().as_i64().unwrap();
    let yv = model.eval(&y).unwrap().as_i64().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv > yv);
    assert!(yv % 7 == 2);
    assert!(xv + 2 > 7);
}

#[test]
fn test_cloning_ast() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = x.clone();
    let zero = ast::Int::from_i64(&ctx, 0);

    let solver = Solver::new(&ctx);
    solver.assert(&x._eq(&zero));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model();
    let xv = model.eval(&x).unwrap().as_i64().unwrap();
    let yv = model.eval(&y).unwrap().as_i64().unwrap();
    assert_eq!(xv, 0);
    assert_eq!(yv, 0);
}

#[test]
fn test_format() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let ast = ast::Int::new_const(&ctx, "x");
    assert_eq!("x", format!("{}", ast));
}

#[test]
fn test_bitvectors() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let a = ast::BV::new_const(&ctx, "a", 64);
    let b = ast::BV::new_const(&ctx, "b", 64);
    let two = ast::BV::from_i64(&ctx, 2, 64);

    let solver = Solver::new(&ctx);
    solver.assert(&a.bvsgt(&b));
    solver.assert(&b.bvsgt(&two));
    let b_plus_two = b.bvadd(&two);
    solver.assert(&b_plus_two.bvsgt(&a));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model();
    let av = model.eval(&a).unwrap().as_i64().unwrap();
    let bv = model.eval(&b).unwrap().as_i64().unwrap();
    assert!(av > bv);
    assert!(bv > 2);
    assert!(bv + 2 > av);
}

#[test]
fn test_ast_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&destination);
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert_eq!(slv.check(), SatResult::Unsat);
}

#[test]
fn test_solver_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&destination);
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    let translated_slv = slv.translate(&source);
    // Add a new constraint, make the old one unsatisfiable, while the copy remains satisfiable.
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert_eq!(slv.check(), SatResult::Unsat);
    assert_eq!(translated_slv.check(), SatResult::Sat);
}

#[test]
fn test_pb_ops_model() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Bool::new_const(&ctx, "x");
    let y = ast::Bool::new_const(&ctx, "y");

    let coeffs = vec![1, 1];
    let other_args = vec![&y];
    let solver = Solver::new(&ctx);
    solver.assert(&x.pb_eq(&other_args[..], coeffs, 1));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!((xv && !yv) || (!xv && yv));
}

#[test]
fn function_ref_count() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let _f = FuncDecl::new(&ctx, "f", &[Sort::Int], Sort::Int);
    let _g = FuncDecl::new(&ctx, "g", &[Sort::Int], Sort::Int);

    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_params() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let mut params = Params::new(&ctx);
    params.set_bool("smt.mbqi", false);
    params.set_f64("smt.qi.eager_threshold", 5.0);
    params.set_u32("smt.qi.max_instances", 999);

    let solver = Solver::new(&ctx);
    solver.set_params(&params);
    solver.assert(&x.gt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_substitution() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::Real::new_const(&ctx, "x");
    let y = ast::Real::new_const(&ctx, "y");
    let z = ast::Real::new_const(&ctx, "z");

    let x_plus_y = x.add(&[&y]);
    let x_plus_z = x.add(&[&z]);

    let substitutions = &[(&y, &z)];

    assert!(x_plus_y.substitute(substitutions) == x_plus_z);
}

#[test]
fn test_real_cmp() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::new_const(&ctx, "x");
    let x_plus_1 = x.add(&[&ast::Real::from_real(&ctx, 1, 1)]);
    // forall x, x < x + 1
    let forall = ast::forall_const(&ctx, &[&x.clone().into()], &[], &x.lt(&x_plus_1).into());

    solver.assert(&forall.try_into().unwrap());
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_arbitrary_size_real() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::from_real_str(&ctx, "99999999999999999999998", "99999999999999999999999")
        .unwrap();
    let y = ast::Real::from_real(&ctx, 1, 1);

    solver.assert(&x.lt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_arbitrary_size_int() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Int::from_str(&ctx, "99999999999999999999998").unwrap();
    let one = ast::Int::from_i64(&ctx, 1);
    let y = ast::Int::from_str(&ctx, "99999999999999999999999").unwrap();

    solver.assert(&x.add(&[&one])._eq(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[cfg(feature = "arbitrary-size-numeral")]
#[test]
fn test_arbitrary_size_real_from_bigrational() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::from_real_str(&ctx, "99999999999999999999998", "99999999999999999999999")
        .unwrap();
    let num = BigInt::from_str("99999999999999999999998").unwrap();
    let den = BigInt::from_str("99999999999999999999999").unwrap();
    let ratio = BigRational::new(num, den);
    let y = ast::Real::from_big_rational(&ctx, &ratio);

    solver.assert(&x._eq(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[cfg(feature = "arbitrary-size-numeral")]
#[test]
fn test_arbitrary_size_int_from_bigint() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let num1 = BigInt::from_str("99999999999999999999998").unwrap();
    let x = ast::Int::from_big_int(&ctx, &num1);
    let y = ast::Int::from_i64(&ctx, 1);

    let num2 = BigInt::from_str("99999999999999999999999").unwrap();
    let z = ast::Int::from_big_int(&ctx, &num2);

    solver.assert(&x.add(&[&y])._eq(&z));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_solver_unknown() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    // Use a very short timeout to quickly return "unknown"
    cfg.set_timeout_msec(1);
    let ctx = Context::new(&cfg);

    // An open problem: find a model for x^3 + y^3 + z^3 == 42
    // See: https://en.wikipedia.org/wiki/Sums_of_three_cubes
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let z = ast::Int::new_const(&ctx, "z");
    let x_cube = x.mul(&[&x, &x]);
    let y_cube = y.mul(&[&y, &y]);
    let z_cube = z.mul(&[&z, &z]);
    let sum_of_cubes = x_cube.add(&[&y_cube, &z_cube]);
    let sum_of_cubes_is_42 = sum_of_cubes._eq(&ast::Int::from_i64(&ctx, 42));

    let solver = Solver::new(&ctx);
    solver.assert(&sum_of_cubes_is_42);

    assert_eq!(solver.check(), SatResult::Unknown);
    assert!(solver.get_reason_unknown().is_some());
}

#[test]
fn test_optimize_unknown() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    // Use a very short timeout to quickly return "unknown"
    cfg.set_timeout_msec(1);
    let ctx = Context::new(&cfg);

    // An open problem: find a model for x^3 + y^3 + z^3 == 42
    // See: https://en.wikipedia.org/wiki/Sums_of_three_cubes
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let z = ast::Int::new_const(&ctx, "z");
    let x_cube = x.mul(&[&x, &x]);
    let y_cube = y.mul(&[&y, &y]);
    let z_cube = z.mul(&[&z, &z]);
    let sum_of_cubes = x_cube.add(&[&y_cube, &z_cube]);
    let sum_of_cubes_is_42 = sum_of_cubes._eq(&ast::Int::from_i64(&ctx, 42));

    let optimize = Optimize::new(&ctx);
    optimize.assert(&sum_of_cubes_is_42);

    assert_eq!(optimize.check(&[]), SatResult::Unknown);
    assert!(optimize.get_reason_unknown().is_some());
}
