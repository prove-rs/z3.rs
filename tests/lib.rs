#[macro_use]
extern crate log;
extern crate env_logger;

extern crate z3;
use z3::*;

#[test]
fn test_config() {
    let _ = env_logger::init();
    let mut c = Config::new();
    c.set_proof_generation(true);
    c.set_timeout_msec(10000);
}

#[test]
fn test_context() {
    let _ = env_logger::init();
    let mut cfg = Config::new();
    cfg.set_proof_generation(true);
    cfg.set_timeout_msec(10000);
    let _ = Context::new(&cfg);
}

#[test]
fn test_sorts_and_symbols() {
    let _ = env_logger::init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let i = ctx.int_sort();
    let _ = Ast::new_const(&ctx.str_sym("x"), &i);
    let _ = Ast::new_const(&ctx.str_sym("y"), &i);
}

#[test]
fn test_solving() {
    let _ = env_logger::init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let i = ctx.int_sort();
    let x = Ast::new_const(&ctx.str_sym("x"), &i);
    let y = Ast::new_const(&ctx.str_sym("y"), &i);

    let solver = Solver::new(&ctx);
    solver.assert(&Ast::new_gt(&x, &y));
    assert!(solver.check());
}

#[test]
fn test_solving_for_model() {
    let _ = env_logger::init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let i = ctx.int_sort();
    let x = Ast::new_const(&ctx.str_sym("x"), &i);
    let y = Ast::new_const(&ctx.str_sym("y"), &i);

    let solver = Solver::new(&ctx);
    solver.assert(&Ast::new_gt(&x, &y));
    assert!(solver.check());

    let model = Model::new(&solver);
    let xv = model.eval(&x).unwrap().as_int64().unwrap();
    let yv = model.eval(&y).unwrap().as_int64().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv > yv);
}

