extern crate env_logger;
#[macro_use]
extern crate log;

extern crate z3;
use std::convert::TryInto;
use z3::ast::Ast;
use z3::*;

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
    assert!(solver.check());
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
    assert!(solver.check());

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
    assert!(solver.check());

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

    let int = ctx.int_sort();
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
    assert!(solver.check());

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
    assert!(slv.check());

    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert!(!slv.check());
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
    assert!(slv.check());

    let translated_slv = slv.translate(&source);
    // Add a new constraint, make the old one unsatisfiable, while the copy remains satisfiable.
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert!(!slv.check());
    assert!(translated_slv.check());
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
    assert!(solver.check());
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

    let int_sort = ctx.int_sort();

    let _f = ctx.func_decl("f", &[&int_sort], &int_sort);
    let _g = ctx.func_decl("g", &[&int_sort], &int_sort);

    assert!(solver.check());
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

    let solver = Solver::new(&ctx);
    solver.set_params(&params);
    solver.assert(&x.gt(&y));
    assert!(solver.check());
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
    let forall = ctx.forall_const(&[&x.clone().into()], &x.lt(&x_plus_1).into());

    solver.assert(&forall.try_into().unwrap());
    assert!(solver.check());
}
