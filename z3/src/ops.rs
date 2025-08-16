use crate::ast::{Bool, Float, IntoAst};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Sub, SubAssign,
};

use crate::ast::{BV, Int, Real};

macro_rules! impl_unary_op_raw {
    ($ty:ty, $output:ty, $base_trait:ident, $base_fn:ident, $function:ident) => {
        impl $base_trait for $ty {
            type Output = $output;

            fn $base_fn(self) -> Self::Output {
                (&self as &$output).$function()
            }
        }
    };
}

macro_rules! impl_unary_op {
    ($ty:ty, $base_trait:ident, $base_fn:ident, $function:ident) => {
        impl_unary_op_raw!($ty, $ty, $base_trait, $base_fn, $function);
        impl_unary_op_raw!(&$ty, $ty, $base_trait, $base_fn, $function);
    };
}

impl_unary_op!(BV, Not, not, bvnot);
impl_unary_op!(BV, Neg, neg, bvneg);

macro_rules! impl_bin_trait {
    ($t:ty, $tr:ident, $trop:ident, $op:ident) => {
        impl<T: IntoAst<$t>> $tr<T> for $t {
            type Output = $t;
            fn $trop(self, rhs: T) -> Self::Output {
                let rhs = rhs.into_ast(&self);
                <$t>::$op(&self, rhs)
            }
        }

        impl<T: IntoAst<$t>> $tr<T> for &$t {
            type Output = $t;
            fn $trop(self, rhs: T) -> Self::Output {
                let rhs = rhs.into_ast(&self);
                <$t>::$op(&self, rhs)
            }
        }
    };
}

macro_rules! impl_bin_assign_trait {
    ($t:ty, $tr:ident, $trop:ident, $op:ident) => {
        impl<T: IntoAst<$t>> $tr<T> for $t {
            fn $trop(&mut self, rhs: T) {
                let res = (self as &mut $t).clone().$op(rhs);
                *self = res
            }
        }
    };
}

macro_rules! impl_trait_number_types {
    ($Z3ty:ty, $tr:ident, [$($num:ty),+]) => {
        $(
        impl_trait_number_types!($Z3ty, $tr, $num)
        )+
    };
    ($Z3ty:ty, $tr:ident, $num:ty) => {
        impl $tr<$Z3ty> for $num {
            type Output = BV;
            fn add(self, rhs: BV) -> Self::Output {
                let lhs = self.into_ast(&rhs);
                <BV>::bvadd(&lhs, &rhs)
            }
        }
    };
}
macro_rules! impl_var_trait {
    ($t:ty, $tr:ident, $trop:ident, $op:ident) => {
        impl<T: IntoAst<$t>> $tr<T> for $t {
            type Output = $t;
            fn $trop(self, rhs: T) -> Self::Output {
                let rhs = rhs.into_ast(&self);
                <$t>::$op(&self.ctx, &[self.clone(), rhs])
            }
        }

        impl<T: IntoAst<$t>> $tr<T> for &$t {
            type Output = $t;
            fn $trop(self, rhs: T) -> Self::Output {
                let rhs = rhs.into_ast(&self);
                <$t>::$op(&self.ctx, &[self.clone(), rhs])
            }
        }
    };
}

impl_var_trait!(Bool, BitAnd, bitand, and);
impl_var_trait!(Bool, BitOr, bitor, or);
impl_bin_trait!(Bool, BitXor, bitxor, xor);

impl_bin_assign_trait!(Bool, BitAndAssign, bitand_assign, bitand);
impl_bin_assign_trait!(Bool, BitOrAssign, bitor_assign, bitor);
impl_bin_assign_trait!(Bool, BitXorAssign, bitxor_assign, bitxor);

impl_bin_trait!(BV, Add, add, bvadd);
impl_bin_trait!(BV, Sub, sub, bvsub);
impl_bin_trait!(BV, Mul, mul, bvmul);
impl_bin_trait!(BV, BitAnd, bitand, bvand);
impl_bin_trait!(BV, BitOr, bitor, bvor);
impl_bin_trait!(BV, BitXor, bitxor, bvxor);
impl_bin_trait!(BV, Shl, shl, bvshl);

impl_bin_assign_trait!(BV, AddAssign, add_assign, bvadd);
impl_bin_assign_trait!(BV, SubAssign, sub_assign, bvsub);
impl_bin_assign_trait!(BV, MulAssign, mul_assign, bvmul);
impl_bin_assign_trait!(BV, BitAndAssign, bitand_assign, bvand);
impl_bin_assign_trait!(BV, BitOrAssign, bitor_assign, bvor);
impl_bin_assign_trait!(BV, BitXorAssign, bitxor_assign, bvxor);
impl_bin_assign_trait!(BV, ShlAssign, shl_assign, bvshl);

impl_unary_op!(Int, Neg, neg, unary_minus);

impl_var_trait!(Int, Add, add, add);
impl_var_trait!(Int, Sub, sub, sub);
impl_var_trait!(Int, Mul, mul, mul);
impl_bin_trait!(Int, Div, div, div);
impl_bin_trait!(Int, Rem, rem, rem);

impl_bin_assign_trait!(Int, AddAssign, add_assign, add);
impl_bin_assign_trait!(Int, SubAssign, sub_assign, sub);
impl_bin_assign_trait!(Int, MulAssign, mul_assign, mul);
impl_bin_assign_trait!(Int, DivAssign, div_assign, div);
impl_bin_assign_trait!(Int, RemAssign, rem_assign, rem);

impl_var_trait!(Real, Add, add, add);
impl_var_trait!(Real, Sub, sub, sub);
impl_var_trait!(Real, Mul, mul, mul);
impl_bin_trait!(Real, Div, div, div);
impl_unary_op!(Real, Neg, neg, unary_minus);

impl_bin_assign_trait!(Real, AddAssign, add_assign, add);
impl_bin_assign_trait!(Real, SubAssign, sub_assign, sub);
impl_bin_assign_trait!(Real, MulAssign, mul_assign, mul);
impl_bin_assign_trait!(Real, DivAssign, div_assign, div);

// implementations for Real
//
// // // implementations for Float
impl_unary_op!(Float, Neg, neg, unary_neg);
//
// // implementations for Bool
impl_unary_op!(Bool, Not, not, not);

impl_trait_number_types!(Int, Add, [i8, i16, i32, i64]);
