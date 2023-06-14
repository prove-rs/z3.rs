extern crate z3;

use z3::{
    ast,
    ast::{Array, Ast, AstKind, Bool, Dynamic, Float, Int, Real, BV},
    Config, Context, DeclKind, FuncDecl, Sort,
};

#[test]
fn test_bv_ops() {
    let cfg = Config::default();
    let ctx = Context::new(&cfg);

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

fn assert_bool_child<'c>(node: &impl Ast<'c>, idx: usize, expected: &Bool<'c>) {
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
    let a_or_b = Bool::or(&ctx, &[&a, &b]);
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

fn assert_ast_attributes<'c, T: Ast<'c>>(expr: &T, is_const: bool) {
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
    let set_expr = ast::Set::new_const(&ctx, "set", &Sort::int(&ctx));
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
