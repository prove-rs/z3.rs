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
    let x_plus_two = ast::Int::add(&ctx, &[&x, &two]);
    solver.assert(&x_plus_two.gt(&seven));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
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

    let model = solver.get_model().unwrap();
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
    assert_eq!(2, model.eval(&a).unwrap().as_i64().unwrap());
    let translated_model = model.translate(&destination);
    assert_eq!(
        2,
        translated_model
            .eval(&translated_a)
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
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!((xv && !yv) || (!xv && yv));

    solver.pop(1);
    solver.push();
    solver.assert(&ast::Bool::pb_ge(&ctx, &[(&x, 1), (&y, 1)], 2));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv && yv);

    solver.pop(1);
    solver.assert(&ast::Bool::pb_le(&ctx, &[(&x, 1), (&y, 1)], 0));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
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

    let mut builder = DtypeBuilder::new(&ctx, "MaybeInt");
    builder.variant("Nothing", &[]);
    let just_accessors = [("int", DatatypeAccessor::Sort(Sort::int(&ctx)))];
    builder.variant("Just", &just_accessors);

    let maybe_int = builder.finish();

    let nothing = maybe_int.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let just_five = maybe_int.variants[1]
        .constructor
        .apply(&[&five.clone().into()]);

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

    let mut list_builder = DtypeBuilder::new(&ctx, "List");
    list_builder.variant("nil", &[]);
    let cons_accessors = [
        ("car", DatatypeAccessor::Sort(Sort::int(&ctx))),
        ("cdr", DatatypeAccessor::Datatype("List".into())),
    ];
    list_builder.variant("cons", &cons_accessors);

    let list_sort = list_builder.finish();

    assert_eq!(list_sort.variants.len(), 2);
    let nil = list_sort.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let cons_five_nil = list_sort.variants[1]
        .constructor
        .apply(&[&five.clone().into(), &nil]);

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
fn get_model_without_check_does_not_exit() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.get_model();
}
