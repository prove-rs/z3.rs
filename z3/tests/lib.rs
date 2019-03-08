extern crate env_logger;
#[macro_use]
extern crate log;

extern crate z3;
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
    let _ = ctx.named_int_const("x");
    let _ = ctx.named_int_const("y");
}

#[test]
fn test_solving() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ctx.named_int_const("x");
    let y = ctx.named_int_const("y");

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    assert!(solver.check());
}

#[test]
fn test_solving_for_model() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ctx.named_int_const("x");
    let y = ctx.named_int_const("y");
    let zero = ctx.from_i64(0);
    let two = ctx.from_i64(2);
    let seven = ctx.from_i64(7);

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    solver.assert(&y.gt(&zero));
    solver.assert(&y.rem(&seven)._eq(&two));
    solver.assert(&x.add(&[&two]).gt(&seven));
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
    let x = ctx.named_int_const("x");
    let y = x.clone();
    let zero = ctx.from_i64(0);

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
    let ast = ctx.named_int_const("x");
    assert_eq!("x", format!("{}", ast));

    let int = ctx.int_sort();
    assert_eq!("Int", format!("{}", int));
}

#[test]
fn test_ast_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = source.named_int_const("a");

    let destination  = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&destination);
    slv.assert(&translated_a._eq(&destination.from_u64(2)));
    assert!(slv.check());

    slv.assert(&translated_a._eq(&destination.from_u64(3)));
    assert!(! slv.check());
}

//#[test]
//fn test_solver_translate() {
//    let cfg = Config::new();
//    let source = Context::new(&cfg);
//    let a = source.named_int_const("a");
//
//    let destination  = Context::new(&cfg);
//    let translated_a = a.translate(&destination);
//
//    let slv = Solver::new(&destination);
//    slv.assert(&translated_a._eq(&destination.from_u64(2)));
//    assert!(slv.check());
//
//    let translated_slv = slv.translate(&source);
//
//    slv.assert(&translated_a._eq(&destination.from_u64(3)));
//    assert!(! slv.check());
//    assert!(translated_slv.check());
//}

#[test]
fn test_pb_ops_model() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ctx.named_bool_const("x");
    let y = ctx.named_bool_const("y");

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
