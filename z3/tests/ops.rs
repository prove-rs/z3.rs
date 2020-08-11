extern crate z3;

use z3::{
    ast::{Bool, Int, Real, BV},
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
