extern crate env_logger;
#[macro_use]
extern crate log;

extern crate z3;
use std::convert::TryInto;
use std::ops::Add;
use std::time::Duration;
use z3::ast::{Array, Ast, Bool, Int, BV};
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
    let x_plus_two = ast::Int::add(&ctx, &[&x, &two]);
    solver.assert(&x_plus_two.gt(&seven));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
    let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv > yv);
    assert!(yv % 7 == 2);
    assert!(xv + 2 > 7);
}

#[test]
fn test_solving_for_model_cloned() {
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
    let x_plus_two = ast::Int::add(&ctx, &[&x, &two]);
    solver.assert(&x_plus_two.gt(&seven));
    let cloned = solver.clone();
    assert_eq!(cloned.check(), SatResult::Sat);

    let model = cloned.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
    let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
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

    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
    let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
    assert_eq!(xv, 0);
    assert_eq!(yv, 0);
}

#[test]
fn test_format() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let ast = ast::Int::new_const(&ctx, "x");
    assert_eq!("x", format!("{}", ast));

    let int = Sort::int(&ctx);
    assert_eq!("Int", format!("{}", int));
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

    let model = solver.get_model().unwrap();
    let av = model.eval(&a, true).unwrap().as_i64().unwrap();
    let bv = model.eval(&b, true).unwrap().as_i64().unwrap();
    assert!(av > bv);
    assert!(bv > 2);
    assert!(bv + 2 > av);
}

#[test]
fn test_bitvector_from_str() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::BV::new_const(&ctx, "a", 129);
    // 2 ** 128
    let b = ast::BV::from_str(&ctx, 129, "340282366920938463463374607431768211456").unwrap();

    let solver = Solver::new(&ctx);
    solver.assert(&a._eq(&b));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let av = model.eval(&a, true).unwrap().to_string();
    assert_eq!(av, "#b100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".to_string());
}

#[test]
fn test_floating_point_bits() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let float32 = ast::Float::new_const_float32(&ctx, "float32");
    let float64 = ast::Float::new_const_double(&ctx, "float64");
    let float128 = ast::Float::new_const(&ctx, "float128", 15, 113);
    let i = ast::Int::new_const(&ctx, "int");

    let exp32 = Sort::float_exponent_size(&float32.get_sort());
    let sig32 = Sort::float_significand_size(&float32.get_sort());
    let exp64 = Sort::float_exponent_size(&float64.get_sort());
    let sig64 = Sort::float_significand_size(&float64.get_sort());
    let exp128 = Sort::float_exponent_size(&float128.get_sort());
    let sig128 = Sort::float_significand_size(&float128.get_sort());
    let expi = Sort::float_exponent_size(&i.get_sort());
    let sigi = Sort::float_significand_size(&i.get_sort());

    assert!(exp32 == Some(8));
    assert!(sig32 == Some(24));
    assert!(exp64 == Some(11));
    assert!(sig64 == Some(53));
    assert!(exp128 == Some(15));
    assert!(sig128 == Some(113));
    assert!(expi.is_none());
    assert!(sigi.is_none());
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
fn test_solver_new_from_smtlib2() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let problem = r#"
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (=( -(+(* 3 x) (* 2 y)) z) 1))
(assert (=(+( -(* 2 x) (* 2 y)) (* 4 z)) -2))
"#;
    let solver = Solver::new(&ctx);
    solver.from_string(problem);
    assert_eq!(solver.check(), SatResult::Sat);
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
fn test_model_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&source);
    slv.assert(&a._eq(&ast::Int::from_u64(&source, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    let model = slv.get_model().unwrap();
    assert_eq!(2, model.eval(&a, true).unwrap().as_i64().unwrap());
    let translated_model = model.translate(&destination);
    assert_eq!(
        2,
        translated_model
            .eval(&translated_a, true)
            .unwrap()
            .as_i64()
            .unwrap()
    );
}

#[test]
fn test_pb_ops_model() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Bool::new_const(&ctx, "x");
    let y = ast::Bool::new_const(&ctx, "y");
    let solver = Solver::new(&ctx);
    solver.push();

    solver.assert(&ast::Bool::pb_eq(&ctx, &[(&x, 1), (&y, 1)], 1));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_bool().unwrap();
    let yv = model.eval(&y, true).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!((xv && !yv) || (!xv && yv));

    solver.pop(1);
    solver.push();
    solver.assert(&ast::Bool::pb_ge(&ctx, &[(&x, 1), (&y, 1)], 2));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_bool().unwrap();
    let yv = model.eval(&y, true).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv && yv);

    solver.pop(1);
    solver.assert(&ast::Bool::pb_le(&ctx, &[(&x, 1), (&y, 1)], 0));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_bool().unwrap();
    let yv = model.eval(&y, true).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(!xv && !yv);
}

#[test]
fn function_ref_count() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let int_sort = Sort::int(&ctx);

    let _f = FuncDecl::new(&ctx, "f", &[&int_sort], &int_sort);
    let _g = FuncDecl::new(&ctx, "g", &[&int_sort], &int_sort);

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
fn test_global_params() {
    let _ = env_logger::try_init();
    // could interfere with other tests if they use global params
    reset_all_global_params();
    let val = get_global_param("iDontExist");
    assert_eq!(val, None);
    let val = get_global_param("verbose");
    assert_eq!(val, Some("0".into()));
    set_global_param("verbose", "1");
    let val = get_global_param("verbose");
    assert_eq!(val, Some("1".into()));
    reset_all_global_params();
    let val = get_global_param("verbose");
    assert_eq!(val, Some("0".into()));
}

#[test]
fn test_substitution() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::Real::new_const(&ctx, "x");
    let y = ast::Real::new_const(&ctx, "y");
    let z = ast::Real::new_const(&ctx, "z");

    let x_plus_y = ast::Real::add(&ctx, &[&x, &y]);
    let x_plus_z = ast::Real::add(&ctx, &[&x, &z]);

    let substitutions = &[(&y, &z)];

    assert!(x_plus_y.substitute(substitutions) == x_plus_z);
}

#[test]
fn test_real_cmp() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::new_const(&ctx, "x");
    let x_plus_1 = ast::Real::add(&ctx, &[&x, &ast::Real::from_real(&ctx, 1, 1)]);
    // forall x, x < x + 1
    let forall = ast::forall_const(&ctx, &[&x], &[], &x.lt(&x_plus_1));

    solver.assert(&forall);
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_float_add() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Float::new_const_float32(&ctx, "x");
    let x_plus_one = ast::Float::round_towards_zero(&ctx).add(&x, &ast::Float::from_f32(&ctx, 1.0));
    let y = ast::Float::from_f32(&ctx, std::f32::consts::PI);

    solver.assert(&x_plus_one._eq(&y));
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

    solver.assert(&ast::Int::add(&ctx, &[&x, &one])._eq(&y));
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

    solver.assert(&ast::Int::add(&ctx, &[&x, &y])._eq(&z));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_string_eq() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "foo").unwrap();
    let z = ast::String::from_str(&ctx, "bar").unwrap();
    let h = ast::String::new_const(&ctx, "h");

    solver.assert(&x._eq(&y));
    solver.assert(&x._eq(&z).not());
    solver.assert(&h._eq(&x));
    assert_eq!(solver.check(), SatResult::Sat);

    solver.assert(&h._eq(&z));
    assert_eq!(solver.check(), SatResult::Unsat)
}

#[test]
fn test_string_concat() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "bar").unwrap();
    let z = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&ast::String::concat(&ctx, &[&x, &y])._eq(&z));
    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_string_prefix() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&x.prefix(&y));
    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_string_suffix() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "bar").unwrap();
    let y = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&x.suffix(&y));
    assert_eq!(solver.check(), SatResult::Sat)
}

fn assert_string_roundtrip(source: &str) {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let expr = ast::String::from_str(&ctx, source).unwrap();
    assert_eq!(&expr.as_string().unwrap(), source);
}

#[test]
fn test_string_as_string() {
    assert_string_roundtrip("x");
    assert_string_roundtrip("'x'");
    assert_string_roundtrip(r#""x""#);
    assert_string_roundtrip(r#"\\"x\\""#);
}

#[test]
fn test_rec_func_def() {
    let _ = env_logger::try_init();
    let cfg = Config::new();

    let ctx = Context::new(&cfg);

    let fac = RecFuncDecl::new(&ctx, "fac", &[&Sort::int(&ctx)], &Sort::int(&ctx));
    let n = ast::Int::new_const(&ctx, "n");
    let n_minus_1 = ast::Int::sub(&ctx, &[&n, &ast::Int::from_i64(&ctx, 1)]);
    let fac_of_n_minus_1 = fac.apply(&[&n_minus_1]);
    let cond: ast::Bool = n.le(&ast::Int::from_i64(&ctx, 0));
    let body = cond.ite(
        &ast::Int::from_i64(&ctx, 1),
        &ast::Int::mul(&ctx, &[&n, &fac_of_n_minus_1.as_int().unwrap()]),
    );

    fac.add_def(&[&n], &body);

    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let solver = Solver::new(&ctx);

    solver.assert(&x._eq(&fac.apply(&[&ast::Int::from_i64(&ctx, 4)]).as_int().unwrap()));
    solver.assert(&y._eq(&ast::Int::mul(&ctx, &[&ast::Int::from_i64(&ctx, 5), &x])));
    solver.assert(&y._eq(&fac.apply(&[&ast::Int::from_i64(&ctx, 5)]).as_int().unwrap()));
    solver.assert(&y._eq(&ast::Int::from_i64(&ctx, 120)));

    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_rec_func_def_unsat() {
    let _ = env_logger::try_init();
    let cfg = Config::new();

    let ctx = Context::new(&cfg);

    let fac = RecFuncDecl::new(&ctx, "fac", &[&Sort::int(&ctx)], &Sort::int(&ctx));
    let n = ast::Int::new_const(&ctx, "n");
    let n_minus_1 = ast::Int::sub(&ctx, &[&n, &ast::Int::from_i64(&ctx, 1)]);
    let fac_of_n_minus_1 = fac.apply(&[&n_minus_1]);
    let cond: ast::Bool = n.le(&ast::Int::from_i64(&ctx, 0));
    let body = cond.ite(
        &ast::Int::from_i64(&ctx, 1),
        &ast::Int::mul(&ctx, &[&n, &fac_of_n_minus_1.as_int().unwrap()]),
    );

    fac.add_def(&[&n], &body);

    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let solver = Solver::new(&ctx);

    solver.assert(&x._eq(&fac.apply(&[&ast::Int::from_i64(&ctx, 4)]).as_int().unwrap()));
    solver.assert(&y._eq(&ast::Int::mul(&ctx, &[&ast::Int::from_i64(&ctx, 5), &x])));
    solver.assert(&y._eq(&fac.apply(&[&ast::Int::from_i64(&ctx, 5)]).as_int().unwrap()));

    // If fac was an uninterpreted function, this assertion would work.
    // To see this, comment out `fac.add_def(&[&n.into()], &body);`
    solver.assert(&y._eq(&ast::Int::from_i64(&ctx, 25)));

    assert_eq!(solver.check(), SatResult::Unsat)
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
    let x_cube = ast::Int::mul(&ctx, &[&x, &x, &x]);
    let y_cube = ast::Int::mul(&ctx, &[&y, &y, &y]);
    let z_cube = ast::Int::mul(&ctx, &[&z, &z, &z]);
    let sum_of_cubes = &ast::Int::add(&ctx, &[&x_cube, &y_cube, &z_cube]);
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
    let x_cube = ast::Int::mul(&ctx, &[&x, &x, &x]);
    let y_cube = ast::Int::mul(&ctx, &[&y, &y, &y]);
    let z_cube = ast::Int::mul(&ctx, &[&z, &z, &z]);
    let sum_of_cubes = &ast::Int::add(&ctx, &[&x_cube, &y_cube, &z_cube]);
    let sum_of_cubes_is_42 = sum_of_cubes._eq(&ast::Int::from_i64(&ctx, 42));

    let optimize = Optimize::new(&ctx);
    optimize.assert(&sum_of_cubes_is_42);

    assert_eq!(optimize.check(&[]), SatResult::Unknown);
    assert!(optimize.get_reason_unknown().is_some());
}

#[test]
fn test_optimize_new_from_smtlib2() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let problem = r#"
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (=( -(+(* 3 x) (* 2 y)) z) 1))
(assert (=(+( -(* 2 x) (* 2 y)) (* 4 z)) -2))
"#;
    let optimize = Optimize::new(&ctx);
    optimize.from_string(problem);
    assert_eq!(optimize.check(&[]), SatResult::Sat);
}

#[test]
fn test_get_unsat_core() {
    let _ = env_logger::try_init();

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    assert!(
        solver.get_unsat_core().is_empty(),
        "no unsat core before assertions"
    );

    let x = ast::Int::new_const(&ctx, "x");

    let x_is_three = ast::Bool::new_const(&ctx, "x-is-three");
    solver.assert_and_track(&x._eq(&ast::Int::from_i64(&ctx, 3)), &x_is_three);

    let x_is_five = ast::Bool::new_const(&ctx, "x-is-five");
    solver.assert_and_track(&x._eq(&ast::Int::from_i64(&ctx, 5)), &x_is_five);

    assert!(
        solver.get_unsat_core().is_empty(),
        "no unsat core before checking"
    );

    let result = solver.check();
    assert_eq!(result, SatResult::Unsat);

    let unsat_core = solver.get_unsat_core();
    assert_eq!(unsat_core.len(), 2);
    assert!(unsat_core.contains(&x_is_three));
    assert!(unsat_core.contains(&x_is_five));
}

#[test]
fn test_datatype_builder() {
    let _ = env_logger::try_init();

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let maybe_int = DatatypeBuilder::new(&ctx, "MaybeInt")
        .variant("Nothing", vec![])
        .variant(
            "Just",
            vec![("int", DatatypeAccessor::Sort(Sort::int(&ctx)))],
        )
        .finish();

    let nothing = maybe_int.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let just_five = maybe_int.variants[1].constructor.apply(&[&five]);

    let nothing_is_nothing = maybe_int.variants[0]
        .tester
        .apply(&[&nothing])
        .as_bool()
        .unwrap();
    solver.assert(&nothing_is_nothing);

    let nothing_is_just = maybe_int.variants[1]
        .tester
        .apply(&[&nothing])
        .as_bool()
        .unwrap();
    solver.assert(&nothing_is_just.not());

    let just_five_is_nothing = maybe_int.variants[0]
        .tester
        .apply(&[&just_five])
        .as_bool()
        .unwrap();
    solver.assert(&just_five_is_nothing.not());

    let just_five_is_just = maybe_int.variants[1]
        .tester
        .apply(&[&just_five])
        .as_bool()
        .unwrap();
    solver.assert(&just_five_is_just);

    let five_two = maybe_int.variants[1].accessors[0]
        .apply(&[&just_five])
        .as_int()
        .unwrap();
    solver.assert(&five._eq(&five_two));

    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_recursive_datatype() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let list_sort = DatatypeBuilder::new(&ctx, "List")
        .variant("nil", vec![])
        .variant(
            "cons",
            vec![
                ("car", DatatypeAccessor::Sort(Sort::int(&ctx))),
                ("cdr", DatatypeAccessor::Datatype("List".into())),
            ],
        )
        .finish();

    assert_eq!(list_sort.variants.len(), 2);
    let nil = list_sort.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let cons_five_nil = list_sort.variants[1].constructor.apply(&[&five, &nil]);

    let nil_is_nil = list_sort.variants[0]
        .tester
        .apply(&[&nil])
        .as_bool()
        .unwrap();
    solver.assert(&nil_is_nil);

    let nil_is_cons = list_sort.variants[1]
        .tester
        .apply(&[&nil])
        .as_bool()
        .unwrap();
    solver.assert(&nil_is_cons.not());

    let cons_five_nil_is_nil = list_sort.variants[0]
        .tester
        .apply(&[&cons_five_nil])
        .as_bool()
        .unwrap();
    solver.assert(&cons_five_nil_is_nil.not());

    let cons_five_nil_is_cons = list_sort.variants[1]
        .tester
        .apply(&[&cons_five_nil])
        .as_bool()
        .unwrap();
    solver.assert(&cons_five_nil_is_cons);

    let car_cons_five_is_five = list_sort.variants[1].accessors[0]
        .apply(&[&cons_five_nil])
        .as_int()
        .unwrap();
    solver.assert(&car_cons_five_is_five._eq(&five));
    assert_eq!(solver.check(), SatResult::Sat);

    let cdr_cons_five_is_nil = list_sort.variants[1].accessors[1]
        .apply(&[&cons_five_nil])
        .as_datatype()
        .unwrap();
    solver.assert(&cdr_cons_five_is_nil._eq(&nil.as_datatype().unwrap()));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_mutually_recursive_datatype() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let tree_builder = DatatypeBuilder::new(&ctx, "Tree")
        .variant(
            "leaf",
            vec![("val", DatatypeAccessor::Sort(Sort::int(&ctx)))],
        )
        .variant(
            "node",
            vec![("children", DatatypeAccessor::Datatype("TreeList".into()))],
        );

    let tree_list_builder = DatatypeBuilder::new(&ctx, "TreeList")
        .variant("nil", vec![])
        .variant(
            "cons",
            vec![
                ("car", DatatypeAccessor::Datatype("Tree".into())),
                ("cdr", DatatypeAccessor::Datatype("TreeList".into())),
            ],
        );

    let sorts = z3::datatype_builder::create_datatypes(vec![tree_builder, tree_list_builder]);
    assert_eq!(sorts.len(), 2);
    let tree_sort = &sorts[0];
    assert_eq!(tree_sort.variants.len(), 2);
    assert_eq!(tree_sort.variants[0].accessors.len(), 1);
    assert_eq!(tree_sort.variants[1].accessors.len(), 1);

    let tree_list_sort = &sorts[1];
    assert_eq!(tree_list_sort.variants.len(), 2);
    assert_eq!(tree_list_sort.variants[0].accessors.len(), 0);
    assert_eq!(tree_list_sort.variants[1].accessors.len(), 2);

    let ten = ast::Int::from_i64(&ctx, 10);
    let leaf_ten = tree_sort.variants[0].constructor.apply(&[&ten]);
    let leaf_ten_val_is_ten = tree_sort.variants[0].accessors[0]
        .apply(&[&leaf_ten])
        .as_int()
        .unwrap();
    solver.assert(&leaf_ten_val_is_ten._eq(&ten.clone()));
    assert_eq!(solver.check(), SatResult::Sat);

    let nil = tree_list_sort.variants[0].constructor.apply(&[]);
    let twenty = ast::Int::from_i64(&ctx, 20);
    let leaf_twenty = tree_sort.variants[0].constructor.apply(&[&twenty]);
    let cons_leaf_twenty_nil = tree_list_sort.variants[1]
        .constructor
        .apply(&[&leaf_twenty, &nil]);
    let cons_leaf_ten_cons_leaf_twenty_nil = tree_list_sort.variants[1]
        .constructor
        .apply(&[&leaf_ten, &cons_leaf_twenty_nil]);

    // n1 = Tree.node(TreeList.cons(Tree.leaf(10), TreeList.cons(Tree.leaf(20), TreeList.nil)))
    let n1 = tree_sort.variants[1]
        .constructor
        .apply(&[&cons_leaf_ten_cons_leaf_twenty_nil]);

    let n1_cons_nil = tree_list_sort.variants[1].constructor.apply(&[&n1, &nil]);
    // n2 = Tree.node(TreeList.cons(n1, TreeList.nil))
    let n2 = tree_sort.variants[1].constructor.apply(&[&n1_cons_nil]);

    solver.assert(&n2._eq(&n1).not());

    // assert(TreeList.car(Tree.children(n2)) == n1)
    solver.assert(
        &tree_list_sort.variants[1].accessors[0]
            .apply(&[&tree_sort.variants[1].accessors[0].apply(&[&n2])])
            ._eq(&n1),
    );
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn get_model_without_check_does_not_exit() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.get_model();
}

#[test]
fn check_application_of_tactic_to_goal() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let tactic = Tactic::new(&ctx, "simplify");
    let repeat_tactic = Tactic::repeat(&ctx, &tactic, 100);

    let goal = Goal::new(&ctx, false, false, false);
    let x = ast::Bool::new_const(&ctx, "x");
    goal.assert(&x);

    let one = ast::Int::from_i64(&ctx, 1);
    let two = ast::Int::from_i64(&ctx, 2);

    let y = ast::Int::new_const(&ctx, "y");

    let y_plus_one_greater_than_or_equal_to_two = y.clone().add(&one).ge(&two);
    goal.assert(&y_plus_one_greater_than_or_equal_to_two);

    let y_greater_than_or_equal_to_one = y.ge(&one);
    goal.assert(&y_greater_than_or_equal_to_one);

    assert_eq!(
        format!("{}", goal),
        "(goal\n  x\n  (>= (+ y 1) 2)\n  (>= y 1))"
    );
    let apply_results = repeat_tactic.apply(&goal, Some(&params));
    let goal_results = apply_results
        .unwrap()
        .list_subgoals()
        .collect::<Vec<Goal>>();
    let goal_result = goal_results.first().unwrap();

    assert_eq!(format!("{}", goal_result), "(goal\n  x\n  (>= y 1))");
}

#[test]
fn test_goal_depth() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_depth(), 0);
}

#[test]
fn test_goal_size() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_size(), 2);
}

#[test]
fn test_goal_num_expr() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    goal.assert(&a);
    assert_eq!(goal.get_num_expr(), 1);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_num_expr(), 2);
}

#[test]
fn test_goal_get_precision() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let false_bool = ast::Bool::from_bool(&ctx, false);

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert_eq!(goal.get_precision(), z3::GoalPrec::Precise);
}

#[test]
fn test_goal_is_inconsistent() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert!(goal.is_inconsistent());

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&true_bool);
    assert!(!goal.is_inconsistent());
}

#[test]
fn test_goal_is_sat() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert!(!goal.is_decided_sat());
    assert!(goal.is_decided_unsat());

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&true_bool);
    assert!(!goal.is_decided_unsat());
    assert!(goal.is_decided_sat());
}

#[test]
fn test_goal_reset() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::Bool::new_const(&ctx, "a");
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a);
    assert_eq!(format!("{}", goal), "(goal\n  a)");
    goal.reset();
    assert_eq!(format!("{}", goal), "(goal)");
}

#[test]
fn test_set_membership() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let set = ast::Set::new_const(&ctx, "integer_set", &Sort::int(&ctx));
    let one = ast::Int::from_u64(&ctx, 1);

    solver.push();
    solver.assert(&set._eq(&ast::Set::empty(&ctx, &Sort::int(&ctx))));

    solver.push();
    solver.assert(&set.member(&one));
    // An empty set will never contain 1
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);

    solver.push();
    let set_with_one = set.add(&one);
    // Adding 1 to the empty set means it does now contain 1
    solver.assert(&set_with_one.member(&one));
    assert_eq!(solver.check(), SatResult::Sat);
    let set_without_one = set_with_one.del(&one);
    // Removing 1 from the set means it no longer contains 1
    solver.assert(&set_without_one.member(&one));
    assert_eq!(solver.check(), SatResult::Unsat);
    solver.pop(1);

    solver.push();
    let x = ast::Int::new_const(&ctx, "x");
    // An empty set will always return false for member
    let forall: ast::Bool = ast::forall_const(&ctx, &[&x], &[], &set.member(&x).not());
    solver.assert(&forall);
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);

    solver.pop(1);

    solver.push();
    // A singleton set of 1 will contain 1
    solver.assert(&set._eq(&ast::Set::empty(&ctx, &Sort::int(&ctx)).add(&one)));
    solver.assert(&set.member(&one));
    assert_eq!(solver.check(), SatResult::Sat);
    solver.pop(1);
}

#[test]
fn test_dynamic_as_set() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let set_sort = Sort::set(&ctx, &Sort::int(&ctx));
    let array_sort = Sort::array(&ctx, &Sort::int(&ctx), &Sort::int(&ctx));
    let array_of_sets = ast::Array::new_const(&ctx, "array_of_sets", &Sort::int(&ctx), &set_sort);
    let array_of_arrays =
        ast::Array::new_const(&ctx, "array_of_arrays", &Sort::int(&ctx), &array_sort);
    assert!(array_of_sets
        .select(&ast::Int::from_u64(&ctx, 0))
        .as_set()
        .is_some());
    assert!(array_of_arrays
        .select(&ast::Int::from_u64(&ctx, 0))
        .as_set()
        .is_none());
}

#[test]
fn test_array_store_select() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let zero = ast::Int::from_u64(&ctx, 0);
    let one = ast::Int::from_u64(&ctx, 1);
    let set = ast::Array::new_const(&ctx, "integer_array", &Sort::int(&ctx), &Sort::int(&ctx))
        .store(&zero, &one);

    solver.assert(&set.select(&zero)._eq(&one.into()).not());
    assert_eq!(solver.check(), SatResult::Unsat);
}

#[test]
fn test_goal_get_formulas() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let c = ast::Bool::new_const(&ctx, "c");
    goal.assert(&a);
    goal.assert(&b);
    goal.assert(&c);
    assert_eq!(goal.get_formulas::<Bool>(), vec![a, b, c],);
}

#[test]
fn test_tactic_skip() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::create_skip(&ctx);
    let apply_results = tactic.apply(&goal, Some(&params));
    let goal_results = apply_results
        .unwrap()
        .list_subgoals()
        .collect::<Vec<Goal>>();
    let goal_result = goal_results.first().unwrap();
    assert_eq!(goal_result.get_formulas::<Bool>(), vec![a.clone(), b, a],);
}

#[test]
fn test_tactic_fail() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a);

    let tactic = Tactic::new(&ctx, "fail");
    let apply_results = tactic.apply(&goal, Some(&params));
    assert!(apply_results.is_err());
}

#[test]
fn test_tactic_try_for() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let one = ast::Int::from_i64(&ctx, 1);
    let two = ast::Int::from_i64(&ctx, 2);
    let x = ast::Int::new_const(&ctx, "x");

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&x.ge(&one.add(&two)));

    let tactic = Tactic::new(&ctx, "simplify");
    let try_for_tactic = tactic.try_for(Duration::from_secs(u64::MAX));

    // Test that `try_for` can successfully apply the underlying tactic
    let apply_results = try_for_tactic.apply(&goal, Some(&params));
    let goal_results = apply_results
        .unwrap()
        .list_subgoals()
        .collect::<Vec<Goal>>();
    let goal_result = goal_results.first().unwrap();
    assert_eq!(format!("{}", goal_result), "(goal\n  (>= x 3))");
}

#[test]
fn test_tactic_and_then() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::new(&ctx, "sat-preprocess");
    let and_then_tactic = tactic.and_then(&Tactic::new(&ctx, "simplify"));
    let apply_results = and_then_tactic.apply(&goal, Some(&params));
    let goal_results = apply_results
        .unwrap()
        .list_subgoals()
        .collect::<Vec<Goal>>();
    let goal_result = goal_results.first().unwrap();
    assert_eq!(goal_result.get_formulas::<Bool>(), vec![a, b]);
}

#[test]
fn test_tactic_or_else() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::new(&ctx, "sat-preprocess");
    let simplify = Tactic::new(&ctx, "simplify");
    let or_else_tactic = tactic.or_else(&simplify);
    let apply_results = or_else_tactic.apply(&goal, Some(&params));
    let goal_results = apply_results
        .unwrap()
        .list_subgoals()
        .collect::<Vec<Goal>>();
    let goal_result = goal_results.first().unwrap();
    assert_eq!(goal_result.get_formulas::<Bool>(), vec![a, b]);
}

#[test]
fn test_goal_apply_tactic() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    pub fn test_apply_tactic(
        ctx: &Context,
        goal: Goal,
        before_formulas: Vec<Bool>,
        after_formulas: Vec<Bool>,
    ) {
        assert_eq!(goal.get_formulas::<Bool>(), before_formulas);
        let params = Params::new(ctx);

        let tactic = Tactic::new(ctx, "sat-preprocess");
        let repeat_tactic = Tactic::repeat(ctx, &tactic, 100);
        let apply_results = repeat_tactic.apply(&goal, Some(&params));
        let goal_results = apply_results
            .unwrap()
            .list_subgoals()
            .collect::<Vec<Goal>>();
        let goal_result = goal_results.first().unwrap();
        assert_eq!(
            goal_result.get_formulas::<Bool>(),
            after_formulas,
            "Before: {:?}",
            before_formulas
        );
    }

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");

    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);
    test_apply_tactic(
        &ctx,
        goal,
        vec![a.clone(), b.clone(), a.clone()],
        vec![a.clone(), b.clone()],
    );

    let a_implies_b = ast::Bool::implies(&a, &b).simplify();
    let a_and_a_implies_b = Bool::and(&ctx, &[&a, &a_implies_b]);

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_a_implies_b);
    test_apply_tactic(
        &ctx,
        goal,
        vec![a.clone(), a_implies_b.clone()],
        vec![a.clone(), b.clone()],
    );

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a);
    goal.assert(&a_implies_b.clone());
    test_apply_tactic(
        &ctx,
        goal,
        vec![a.clone(), a_implies_b.clone()],
        vec![a.clone(), b.clone()],
    );

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    let true_and_false_and_true = ast::Bool::and(&ctx, &[&true_bool, &false_bool, &true_bool]);
    goal.assert(&true_and_false_and_true);
    test_apply_tactic(
        &ctx,
        goal,
        vec![false_bool.clone()],
        vec![false_bool.clone()],
    );
}

#[test]
fn test_tactic_cond() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let t1 = Tactic::new(&ctx, "qfnra");
    let t2 = Tactic::new(&ctx, "smt");
    let p = Probe::new(&ctx, "is-qfnra");

    let _t = Tactic::cond(&ctx, &p, &t1, &t2);
}

#[test]
fn test_tactic_conditions() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let t1 = Tactic::new(&ctx, "qfnra");
    let t2 = Tactic::new(&ctx, "smt");
    let p = Probe::new(&ctx, "is-qfnra");

    t1.probe_or_else(&p, &t2);
    t1.when(&p);
    Tactic::cond(&ctx, &p, &t1, &t2);
    Tactic::fail_if(&ctx, &p);
}

#[test]
fn test_probe_debug() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let _v: Vec<&str> = Probe::list_all(&ctx).map(|x| x.unwrap()).collect();
    assert_eq!(
        "A probe to give an upper bound of Ackermann congruence lemmas that a formula might generate.",
        Probe::describe(&ctx, "ackr-bound-probe").unwrap(),
    );
}

#[test]
fn test_probe_names() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let twenty = ast::Int::from_u64(&ctx, 20);
    let g = Goal::new(&ctx, false, false, false);

    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    g.assert(&x.lt(&twenty));

    let num_consts_probe = Probe::new(&ctx, "num-consts");
    assert_eq!(1.0, num_consts_probe.apply(&g));

    let is_prop_probe = Probe::new(&ctx, "is-propositional");
    assert_eq!(0.0, is_prop_probe.apply(&g));

    let is_qflia_probe = Probe::new(&ctx, "is-qflia");
    assert_eq!(1.0, is_qflia_probe.apply(&g));
}

#[test]
fn test_probe_eq() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);

    let two_probe = Probe::constant(&ctx, 2.0);
    let size_probe = Probe::new(&ctx, "size");
    let equals_two_probe = &size_probe.eq(&two_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(1.0, equals_two_probe.apply(&g));
}

#[test]
fn test_probe_gt() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let ten_probe = Probe::constant(&ctx, 10.0);
    let size_probe = Probe::new(&ctx, "size");
    let gt_ten_probe = &size_probe.gt(&ten_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(0.0, gt_ten_probe.apply(&g));
}

#[test]
fn test_probe_gte() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let two_probe = Probe::constant(&ctx, 2.0);
    let size_probe = Probe::new(&ctx, "size");
    let ge_two_probe = &size_probe.ge(&two_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(1.0, ge_two_probe.apply(&g));
}

#[test]
fn test_probe_le() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let two_probe = Probe::constant(&ctx, 2.0);
    let size_probe = Probe::new(&ctx, "size");
    let le_two_probe = &size_probe.le(&two_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(1.0, le_two_probe.apply(&g));
}

#[test]
fn test_probe_lt() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let ten_probe = Probe::constant(&ctx, 10.0);
    let size_probe = Probe::new(&ctx, "size");
    let le_ten_probe = &size_probe.le(&ten_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(1.0, le_ten_probe.apply(&g));
}

#[test]
fn test_probe_ne() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let two_probe = Probe::constant(&ctx, 2.0);
    let size_probe = Probe::new(&ctx, "size");
    let ne_two_probe = &size_probe.ne(&two_probe);

    let x = ast::Int::fresh_const(&ctx, "x");
    let zero = ast::Int::from_u64(&ctx, 0);
    let ten = ast::Int::from_u64(&ctx, 10);
    let g = Goal::new(&ctx, false, false, false);
    g.assert(&x.gt(&zero));
    g.assert(&x.lt(&ten));
    assert_eq!(0.0, ne_two_probe.apply(&g));
}

#[test]
#[should_panic]
fn test_issue_94() {
    let cfg = Config::new();
    let ctx0 = Context::new(&cfg);
    let ctx1 = Context::new(&cfg);
    let i0 = ast::Int::fresh_const(&ctx0, "a");
    let i1 = ast::Int::fresh_const(&ctx1, "b");
    ast::Int::add(&ctx0, &[&i0, &i1]);
}

#[test]
fn test_ast_safe_eq() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);
    let x: ast::Dynamic = ast::Bool::new_const(ctx, "a").into();
    let y: ast::Dynamic = ast::String::from_str(ctx, "b").unwrap().into();

    let other_bool: ast::Dynamic = ast::Bool::new_const(ctx, "c").into();
    let other_string: ast::Dynamic = ast::String::from_str(ctx, "d").unwrap().into();

    let sd: SortDiffers<'_> = SortDiffers::new(other_bool.get_sort(), other_string.get_sort());

    let result = x._safe_eq(&y);
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert_eq!(err.left(), sd.left());
    assert_eq!(err.right(), sd.right());
}

#[test]
fn test_ast_safe_decl() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);
    let x: ast::Bool = ast::Bool::new_const(ctx, "x");
    let x_not = x.not();
    assert_eq!(x_not.safe_decl().unwrap().kind(), DeclKind::NOT);

    let f = FuncDecl::new(ctx, "f", &[&Sort::int(ctx)], &Sort::int(ctx));
    let x = ast::Int::new_const(ctx, "x");
    let f_x: ast::Int = f.apply(&[&x]).try_into().unwrap();
    let f_x_pattern: Pattern = Pattern::new(ctx, &[&f_x]);
    let forall = ast::forall_const(ctx, &[&x], &[&f_x_pattern], &x._eq(&f_x));
    assert!(forall.safe_decl().is_err());
    assert_eq!(
        format!("{}", forall.safe_decl().err().unwrap()),
        "ast node is not a function application, has kind Quantifier"
    );
}

//the intersection of "FOO"+"bar" and [a-z]+ is empty
#[test]
fn test_regex_capital_foobar_intersect_az_plus_is_unsat() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);
    let solver = Solver::new(ctx);
    let s = ast::String::new_const(ctx, "s");

    let re = ast::Regexp::intersect(
        ctx,
        &[
            &ast::Regexp::concat(
                ctx,
                &[
                    &ast::Regexp::literal(ctx, "FOO"),
                    &ast::Regexp::literal(ctx, "bar"),
                ],
            ),
            &ast::Regexp::plus(&ast::Regexp::range(ctx, &'a', &'z')),
        ],
    );
    solver.assert(&s.regex_matches(&re));
    assert!(solver.check() == SatResult::Unsat);
}

#[test]
/// https://github.com/Z3Prover/z3/blob/21e59f7c6e5033006265fc6bc16e2c9f023db0e8/examples/dotnet/Program.cs#L329-L370
fn test_array_example1() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);

    let g = Goal::new(ctx, true, false, false);

    let aex = Array::new_const(ctx, "MyArray", &Sort::int(ctx), &Sort::bitvector(ctx, 32));

    let sel = aex.select(&Int::from_u64(ctx, 0));

    g.assert(&sel._eq(&BV::from_u64(ctx, 42, 32).into()));

    let xc = Int::new_const(ctx, "x");

    let fd = FuncDecl::new(ctx, "f", &[&Sort::int(ctx)], &Sort::int(ctx));

    let fapp = fd.apply(&[&xc as &dyn Ast]);

    g.assert(&Int::from_u64(ctx, 123)._eq(&xc.clone().add(&fapp.as_int().unwrap())));

    let s = &Solver::new(ctx);
    for a in g.get_formulas() {
        s.assert(&a);
    }
    println!("Solver: {}", s);

    let q = s.check();
    println!("Status: {:?}", q);

    if q != SatResult::Sat {
        panic!("Solver did not return sat");
    }

    let model = s.get_model().unwrap();

    assert!(
        model.to_string()
            == "MyArray -> ((as const (Array Int (_ BitVec 32))) #x0000002a)\nx -> 0\nf -> {\n  123\n}\n"
    );

    assert!(
        model.get_const_interp(&aex).unwrap().to_string()
            == "((as const (Array Int (_ BitVec 32))) #x0000002a)"
    );

    assert!(model.get_const_interp(&xc).unwrap().to_string() == "0");

    assert!(model.get_func_interp(&fd).unwrap().to_string() == "[else -> 123]");
}

#[test]
/// https://z3prover.github.io/api/html/classz3py_1_1_func_entry.html
fn return_number_args_in_given_entry() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);
    let f = FuncDecl::new(
        ctx,
        "f",
        &[&Sort::int(ctx), &Sort::int(ctx)],
        &Sort::int(ctx),
    );

    let solver = Solver::new(ctx);
    solver.assert(
        &f.apply(&[&Int::from_u64(ctx, 0), &Int::from_u64(ctx, 1)])
            ._eq(&Int::from_u64(ctx, 10).into()),
    );
    solver.assert(
        &f.apply(&[&Int::from_u64(ctx, 1), &Int::from_u64(ctx, 2)])
            ._eq(&Int::from_u64(ctx, 20).into()),
    );
    solver.assert(
        &f.apply(&[&Int::from_u64(ctx, 1), &Int::from_u64(ctx, 0)])
            ._eq(&Int::from_u64(ctx, 10).into()),
    );

    assert!(solver.check() == SatResult::Sat);

    let model = solver.get_model().unwrap();
    let f_i = model.get_func_interp(&f).unwrap();
    assert!(f_i.get_num_entries() == 1);
    let e = &f_i.get_entries()[0];
    assert!(e.to_string() == "[1, 2, 20]");
    assert!(e.get_num_args() == 2);
    assert!(e.get_args()[0].to_string() == "1");
    assert!(e.get_args()[1].to_string() == "2");
    assert!(e.get_args().get(2).is_none());

    assert!(model.to_string() == "f -> {\n  1 2 -> 20\n  else -> 10\n}\n");
}

#[test]
/// https://stackoverflow.com/questions/13395391/z3-finding-all-satisfying-models
fn iterate_all_solutions() {
    let cfg = Config::new();
    let ctx = &Context::new(&cfg);
    let solver = Solver::new(ctx);
    let a = &Int::new_const(ctx, "a");
    let b = &Int::new_const(ctx, "b");
    let one = Int::from_u64(ctx, 1);
    let two = Int::from_u64(ctx, 2);
    let five = &Int::from_u64(ctx, 5);

    solver.assert(&one.le(a));
    solver.assert(&a.le(five));
    solver.assert(&one.le(b));
    solver.assert(&b.le(five));
    solver.assert(&a.ge(&(two * b)));

    let mut solutions = std::collections::HashSet::new();
    while solver.check() == SatResult::Sat {
        let model = solver.get_model().unwrap();
        let mut modifications = Vec::new();
        let this_solution = model
            .iter()
            .map(|fd| {
                modifications.push(
                    fd.apply(&[])
                        ._eq(&model.get_const_interp(&fd.apply(&[])).unwrap())
                        .not(),
                );
                format!(
                    "{} = {}",
                    fd.name(),
                    model.get_const_interp(&fd.apply(&[])).unwrap()
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        solutions.insert(format!("[{this_solution}]"));
        solver.assert(&Bool::or(ctx, &modifications.iter().collect::<Vec<_>>()));
    }

    assert!(
        solutions
            == vec![
                "[b = 1, a = 2]".to_string(),
                "[b = 2, a = 4]".to_string(),
                "[b = 1, a = 3]".to_string(),
                "[b = 2, a = 5]".to_string(),
                "[b = 1, a = 4]".to_string(),
                "[b = 1, a = 5]".to_string()
            ]
            .into_iter()
            .collect()
    )
}
