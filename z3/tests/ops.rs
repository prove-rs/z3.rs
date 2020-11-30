extern crate z3;

use z3::{
    ast::{Ast, Bool, Int, Real, BV},
    Config, Context,
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
