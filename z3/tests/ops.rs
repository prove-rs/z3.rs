use z3::ast::Array;
use z3::ast::Bool;
use z3::ast::Dynamic;
use z3::ast::Float;
use z3::ast::Set;
use z3::{
    Config, Context, DeclKind, FuncDecl, SatResult, Solver, Sort, ast,
    ast::{Ast, AstKind, BV, Int, Real},
};

#[test]
fn test_bv_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);
    let bv = BV::from_u64(&ctx, 23, 23);
    macro_rules! test_binary_op {
        ($op:tt) => {
            let a = BV::new_const(&ctx, "a", 5);
            let b = BV::new_const(&ctx, "b", 5);
            let _ = a $op b $op 2u64 $op 2i64;
        };
    }
    macro_rules! test_op_assign {
        ($op:tt, $assign:tt) => {
            test_binary_op!($op);
            let mut a = BV::new_const(&ctx, "a", 5);
            let b = BV::new_const(&ctx, "b", 5);
            a $assign b;
            a $assign 2u64;
            a $assign 2i64;
        };
    }
    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = BV::new_const(&ctx, "a", 5);
            let _ = $op a;
        };
    }

    test_op_assign!(+, +=);
    test_op_assign!(-, -=);
    test_op_assign!(*, *=);
    test_op_assign!(&, &=);
    test_op_assign!(|, |=);
    test_op_assign!(^, ^=);
    test_op_assign!(<<, <<=);
    test_unary_op!(-);
    test_unary_op!(!);
}

#[test]
fn test_int_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    macro_rules! test_binary_op {
        ($op:tt) => {
            let a = Int::new_const(&ctx, "a");
            let b = Int::new_const(&ctx, "b");
            let _ = a $op b $op 2u64 $op 2i64;
        };
    }
    macro_rules! test_op_assign {
        ($op:tt, $assign:tt) => {
            test_binary_op!($op);
            let mut a = Int::new_const(&ctx, "a");
            let b = Int::new_const(&ctx, "b");
            a $assign b;
            a $assign 2u64;
            a $assign 2i64;
        };
    }
    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = Int::new_const(&ctx, "a");
            let _ = $op a;
        };
    }

    test_op_assign!(+, +=);
    test_op_assign!(-, -=);
    test_op_assign!(*, *=);
    test_op_assign!(/, /=);
    test_op_assign!(%, %=);
    test_unary_op!(-);
}

#[test]
fn test_pow_ret_real() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);
    let x = Int::new_const(&ctx, "x");
    let y = x.power(&x);
    assert!(y.get_sort() == Sort::real(&ctx));
}

#[test]
fn test_real_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    macro_rules! test_binary_op {
        ($op:tt) => {
            let a = Real::new_const(&ctx, "a");
            let b = Real::new_const(&ctx, "b");
            let _ = a $op b;
        };
    }
    macro_rules! test_op_assign {
        ($op:tt, $assign:tt) => {
            test_binary_op!($op);
            let mut a = Real::new_const(&ctx, "a");
            let b = Real::new_const(&ctx, "b");
            a $assign b;
        };
    }
    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = Real::new_const(&ctx, "a");
            let _ = $op a;
        };
    }

    test_op_assign!(+, +=);
    test_op_assign!(-, -=);
    test_op_assign!(*, *=);
    test_op_assign!(/, /=);
    test_unary_op!(-);
}

#[test]
fn test_float32_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = Float::new_const_float32(&ctx, "a");
            let _ = $op a;
        };
    }
    test_unary_op!(-);

    let solver = Solver::new(&ctx);

    // Infinite
    solver.check_assumptions(&[Float::from_f32(&ctx, f32::INFINITY).is_infinite()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, f32::NEG_INFINITY).is_infinite()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, 0f32).is_infinite().not()]);

    // Normal
    solver.check_assumptions(&[Float::from_f32(&ctx, 1f32).is_normal()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, f32::MIN_POSITIVE / 2.0)
        .is_normal()
        .not()]);

    // Subnormal
    solver.check_assumptions(&[Float::from_f32(&ctx, f32::MIN_POSITIVE / 2.0).is_subnormal()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, 1f32).is_subnormal().not()]);

    // Zero
    solver.check_assumptions(&[Float::from_f32(&ctx, 0f32).is_zero()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, 1f32).is_zero().not()]);

    // NaN
    solver.check_assumptions(&[Float::from_f32(&ctx, f32::NAN).is_nan()]);
    solver.check_assumptions(&[Float::from_f32(&ctx, 1f32).is_nan().not()]);
}

#[test]
fn test_double_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = Float::new_const_double(&ctx, "a");
            let _ = $op a;
        };
    }
    test_unary_op!(-);

    let solver = Solver::new(&ctx);

    // Infinite
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, f64::INFINITY).is_infinite()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, f64::NEG_INFINITY).is_infinite()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 0f64).is_infinite().not()]),
        SatResult::Sat
    );

    // Normal
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 1f64).is_normal()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, f64::MIN_POSITIVE / 2.0)
            .is_normal()
            .not()]),
        SatResult::Sat
    );

    // Subnormal
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, f64::MIN_POSITIVE / 2.0).is_subnormal()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 1f64).is_subnormal().not()]),
        SatResult::Sat
    );

    // Zero
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 0f64).is_zero()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 1f64).is_zero().not()]),
        SatResult::Sat
    );

    // NaN
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, f64::NAN).is_nan()]),
        SatResult::Sat
    );
    assert_eq!(
        solver.check_assumptions(&[Float::from_f64(&ctx, 1f64).is_nan().not()]),
        SatResult::Sat
    );
}

#[test]
fn test_bool_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    macro_rules! test_binary_op {
        ($op:tt) => {
            let a = Bool::new_const(&ctx, "a");
            let b = Bool::new_const(&ctx, "b");
            let _ = a $op b $op true $op false;
        };
    }
    macro_rules! test_op_assign {
        ($op:tt, $assign:tt) => {
            test_binary_op!($op);
            let mut a = Bool::new_const(&ctx, "a");
            let b = Bool::new_const(&ctx, "b");
            a $assign b;
            a $assign true;
            a $assign false;
        };
    }
    macro_rules! test_unary_op {
        ($op:tt) => {
            let a = Bool::new_const(&ctx, "a");
            let _ = $op a;
        };
    }

    test_op_assign!(&, &=);
    test_op_assign!(|, |=);
    test_op_assign!(^, ^=);
    test_unary_op!(!);
}

fn assert_bool_child(node: &impl Ast, idx: usize, expected: &Bool) {
    assert_eq!(&node.nth_child(idx).unwrap().as_bool().unwrap(), expected);
}

#[test]
fn test_ast_children() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    let a = Bool::new_const(&ctx, "a");
    assert_eq!(a.num_children(), 0);
    assert_eq!(a.nth_child(0), None);
    assert_eq!(a.children(), vec![]);

    let not_a = a.not();
    assert_eq!(not_a.num_children(), 1);
    assert_bool_child(&not_a, 0, &a);
    assert_eq!(not_a.nth_child(1), None);

    let b = Bool::new_const(&ctx, "b");
    // This is specifically testing for an array of values, not an array of slices
    let a_or_b = Bool::or(&ctx, &[a.clone(), b.clone()]);
    assert_eq!(a_or_b.num_children(), 2);
    assert_bool_child(&a_or_b, 0, &a);
    assert_bool_child(&a_or_b, 1, &b);
    assert_eq!(a_or_b.nth_child(2), None);
    let children = a_or_b.children();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0].as_bool().unwrap(), a);
    assert_eq!(children[1].as_bool().unwrap(), b);

    let c = Bool::new_const(&ctx, "c");
    let a_and_b_and_c = Bool::and(&ctx, &[&a, &b, &c]);
    assert_eq!(a_and_b_and_c.num_children(), 3);
    assert_bool_child(&a_and_b_and_c, 0, &a);
    assert_bool_child(&a_and_b_and_c, 1, &b);
    assert_bool_child(&a_and_b_and_c, 2, &c);
    assert_eq!(a_and_b_and_c.nth_child(3), None);
    let children = a_and_b_and_c.children();
    assert_eq!(children[0].as_bool().unwrap(), a);
    assert_eq!(children[1].as_bool().unwrap(), b);
    assert_eq!(children[2].as_bool().unwrap(), c);
}

fn assert_ast_attributes<T: Ast>(expr: &T, is_const: bool) {
    assert_eq!(expr.kind(), AstKind::App);
    assert!(expr.is_app());
    assert_eq!(expr.is_const(), is_const);
}

#[test]
fn test_ast_attributes() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    let a = Bool::new_const(&ctx, "a");
    let b = Bool::from_bool(&ctx, false);
    let not_a = a.not();
    let a_or_b = &Bool::or(&ctx, &[&a, &b]);
    assert_eq!(b.decl().kind(), DeclKind::FALSE);
    assert_eq!(not_a.decl().kind(), DeclKind::NOT);
    assert_eq!(a_or_b.decl().kind(), DeclKind::OR);

    assert_ast_attributes(&a, true);
    assert_ast_attributes(&b, true);
    assert_ast_attributes(&Dynamic::from_ast(&a), true);
    assert_ast_attributes(&not_a, false);
    assert_ast_attributes(a_or_b, false);

    assert_ast_attributes(
        &Array::new_const(&ctx, "arr", &Sort::int(&ctx), &Sort::bool(&ctx)),
        true,
    );
    assert_ast_attributes(&BV::new_const(&ctx, "bv", 512), true);
    assert_ast_attributes(&Real::new_const(&ctx, "r"), true);
    assert_ast_attributes(&ast::String::new_const(&ctx, "st"), true);

    let int_expr = Int::new_const(&ctx, "i");
    let set_expr = Set::new_const(&ctx, "set", &Sort::int(&ctx));
    assert_ast_attributes(&int_expr, true);
    assert_ast_attributes(&set_expr, true);
    assert_ast_attributes(&set_expr.add(&Dynamic::from_ast(&int_expr)), false);
}

#[test]
fn test_func_decl_attributes() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

    let const_decl = FuncDecl::new(&ctx, "c", &[], &Sort::bool(&ctx));
    assert_eq!(const_decl.kind(), DeclKind::UNINTERPRETED);
    assert_eq!(const_decl.name(), "c");
    assert_eq!(const_decl.arity(), 0);

    let unary_decl = FuncDecl::new(&ctx, "unary", &[&Sort::bool(&ctx)], &Sort::bool(&ctx));
    assert_eq!(unary_decl.kind(), DeclKind::UNINTERPRETED);
    assert_eq!(unary_decl.name(), "unary");
    assert_eq!(unary_decl.arity(), 1);

    let binary_decl = FuncDecl::new(
        &ctx,
        "binary",
        &[&Sort::bool(&ctx), &Sort::bool(&ctx)],
        &Sort::bool(&ctx),
    );
    assert_eq!(binary_decl.kind(), DeclKind::UNINTERPRETED);
    assert_eq!(binary_decl.name(), "binary");
    assert_eq!(binary_decl.arity(), 2);
}

#[test]
fn test_real_approx() {
    let ctx = Context::new(&Config::default());
    let x = Real::new_const(&ctx, "x");
    let xx = &x * &x;
    let zero = Real::from_real(&ctx, 0, 1);
    let two = Real::from_real(&ctx, 2, 1);
    let s = Solver::new(&ctx);
    s.assert(&x.ge(&zero));
    s.assert(&xx._eq(&two));
    assert_eq!(s.check(), SatResult::Sat);
    let m = s.get_model().unwrap();
    let res = m.eval(&x, false).unwrap();
    assert_eq!(res.as_real(), None); // sqrt is irrational
    println!("f64 res: {}", res.approx_f64());
    assert!((res.approx_f64() - ::std::f64::consts::SQRT_2).abs() < 1e-20);
    assert_eq!(res.approx(0), "1.");
    assert_eq!(res.approx(1), "1.4");
    assert_eq!(res.approx(2), "1.41");
    assert_eq!(res.approx(3), "1.414");
    assert_eq!(res.approx(4), "1.4142");
    assert_eq!(res.approx(5), "1.41421");
    assert_eq!(res.approx(6), "1.414213");
    assert_eq!(res.approx(7), "1.4142135");
    assert_eq!(res.approx(8), "1.41421356");
    assert_eq!(res.approx(9), "1.414213562");
    assert_eq!(res.approx(10), "1.4142135623");
    assert_eq!(res.approx(11), "1.41421356237");
    assert_eq!(res.approx(12), "1.414213562373");
    assert_eq!(res.approx(13), "1.4142135623730");
    assert_eq!(res.approx(14), "1.41421356237309");
    assert_eq!(res.approx(15), "1.414213562373095");
    assert_eq!(res.approx(16), "1.4142135623730950");
    assert_eq!(res.approx(17), "1.41421356237309504");
    assert_eq!(res.approx(18), "1.414213562373095048");
    assert_eq!(res.approx(19), "1.4142135623730950488");
    assert_eq!(res.approx(20), "1.41421356237309504880");
    assert_eq!(res.approx(21), "1.414213562373095048801");
    assert_eq!(res.approx(22), "1.4142135623730950488016");
    assert_eq!(res.approx(23), "1.41421356237309504880168");
    assert_eq!(res.approx(24), "1.414213562373095048801688");
    assert_eq!(res.approx(25), "1.4142135623730950488016887");
    assert_eq!(res.approx(26), "1.41421356237309504880168872");
    assert_eq!(res.approx(27), "1.414213562373095048801688724");
    assert_eq!(res.approx(28), "1.4142135623730950488016887242");
    assert_eq!(res.approx_f64(), res.approx(32).parse().unwrap());
    assert_ne!(res.approx_f64(), res.approx(16).parse().unwrap());
}
