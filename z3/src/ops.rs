use crate::ast::{Bool, Float, IntoAst};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Sub, SubAssign,
};

use crate::ast::{BV, Int, Real};
macro_rules! mk_const_bv {
    ($constant:expr, $function:ident, $val:expr, $other:expr) => {
        $constant = BV::$function($other.get_ctx(), $val, $other.get_size());
    };
}

macro_rules! mk_const_int {
    ($constant:expr, $function:ident, $val:expr, $other:expr) => {
        $constant = Int::$function($other.get_ctx(), $val);
    };
}

macro_rules! mk_const_bool {
    ($constant:expr, $function:ident, $val:expr, $other:expr) => {
        $constant = Bool::from_bool($other.get_ctx(), $val);
    };
}

macro_rules! impl_binary_op_raw {
    ($ty:ty, $rhs:ty, $output:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl $base_trait<$rhs> for $ty {
            type Output = $output;

            fn $base_fn(self, rhs: $rhs) -> Self::Output {
                (&self as &$output).$function(&rhs as &$output)
            }
        }
    };
}

macro_rules! impl_binary_assign_op_raw {
    ($ty:ty, $rhs:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_op_raw!(
            $ty,
            $rhs,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl $assign_trait<$rhs> for $ty {
            fn $assign_fn(&mut self, rhs: $rhs) {
                *self = (self as &$ty).$function(&rhs as &$ty);
            }
        }
    };
}

macro_rules! impl_binary_op_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $base_fn:ident, $function:ident, $construct_constant:ident) => {
        impl $base_trait<$other> for $ty {
            type Output = $output;

            fn $base_fn(self, rhs: $other) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                $base_trait::$base_fn(self, c)
            }
        }

        impl $base_trait<$ty> for $other {
            type Output = $output;

            fn $base_fn(self, rhs: $ty) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, self, rhs);
                $base_trait::$base_fn(rhs, c)
            }
        }
    };
}

macro_rules! impl_binary_op_assign_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident, $construct_constant:ident) => {
        impl_binary_op_number_raw!(
            $ty,
            $other,
            $other_fn,
            $output,
            $base_trait,
            $base_fn,
            $function,
            $construct_constant
        );

        impl $assign_trait<$other> for $ty {
            fn $assign_fn(&mut self, rhs: $other) {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                self.$assign_fn(c);
            }
        }
    };
}

macro_rules! impl_binary_op_without_numbers {
    ($ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_assign_op_raw!(
            $ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_assign_op_raw!(
            $ty,
            &$ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_op_raw!(
            &$ty,
            $ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_op_raw!(
            &$ty,
            &$ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
    };
}

macro_rules! impl_binary_op_bool {
    ($ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_op_without_numbers!(
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_op_assign_number_raw!(
            $ty,
            bool,
            from_bool,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function,
            mk_const_bool
        );
        impl_binary_op_number_raw!(
            &$ty,
            bool,
            from_bool,
            $ty,
            $base_trait,
            $base_fn,
            $function,
            mk_const_bool
        );
    };
}

macro_rules! impl_binary_op {
    ($ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident, $construct_constant:ident) => {
        impl_binary_op_without_numbers!(
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_op_assign_number_raw!(
            $ty,
            u64,
            from_u64,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function,
            $construct_constant
        );
        impl_binary_op_number_raw!(
            &$ty,
            u64,
            from_u64,
            $ty,
            $base_trait,
            $base_fn,
            $function,
            $construct_constant
        );
        impl_binary_op_assign_number_raw!(
            $ty,
            i64,
            from_i64,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function,
            $construct_constant
        );
        impl_binary_op_number_raw!(
            &$ty,
            i64,
            from_i64,
            $ty,
            $base_trait,
            $base_fn,
            $function,
            $construct_constant
        );
    };
}

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

macro_rules! impl_binary_mult_op_raw {
    ($base_ty:ident, $ty:ty, $rhs:ty, $output:ty, $base_trait:ident, $base_fn:ident, $function:ident) => {
        impl $base_trait<$rhs> for $ty {
            type Output = $output;

            fn $base_fn(self, other: $rhs) -> Self::Output {
                $base_ty::$function(self.get_ctx(), &[&self as &$output, &other as &$output])
            }
        }
    };
}

macro_rules! impl_binary_mult_op_assign_raw {
    ($base_ty:ident, $ty:ty, $rhs:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_mult_op_raw!($base_ty, $ty, $rhs, $ty, $base_trait, $base_fn, $function);

        impl $assign_trait<$rhs> for $ty {
            fn $assign_fn(&mut self, other: $rhs) {
                *self = $base_ty::$function(self.get_ctx(), &[&self as &$ty, &other as &$ty])
            }
        }
    };
}

macro_rules! impl_binary_mult_op_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $base_fn:ident, $construct_constant:ident) => {
        impl $base_trait<$other> for $ty {
            type Output = $output;

            fn $base_fn(self, rhs: $other) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                $base_trait::$base_fn(self, c)
            }
        }

        impl $base_trait<$ty> for $other {
            type Output = $output;

            fn $base_fn(self, rhs: $ty) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, self, rhs);
                $base_trait::$base_fn(rhs, c)
            }
        }
    };
}

macro_rules! impl_binary_mult_op_assign_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $construct_constant:ident) => {
        impl_binary_mult_op_number_raw!(
            $ty,
            $other,
            $other_fn,
            $output,
            $base_trait,
            $base_fn,
            $construct_constant
        );

        impl $assign_trait<$other> for $ty {
            fn $assign_fn(&mut self, rhs: $other) {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                *self = (&self as &$ty).$base_fn(&c as &$ty)
            }
        }
    };
}

macro_rules! impl_binary_mult_op_without_numbers {
    ($base_ty:ident, $ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_mult_op_assign_raw!(
            $base_ty,
            $ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_mult_op_assign_raw!(
            $base_ty,
            $ty,
            &$ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_mult_op_raw!($base_ty, &$ty, $ty, $ty, $base_trait, $base_fn, $function);
        impl_binary_mult_op_raw!($base_ty, &$ty, &$ty, $ty, $base_trait, $base_fn, $function);
    };
    ($base_ty:ident, $ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident) => {
        impl_binary_mult_op_without_numbers!(
            $base_ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $base_fn
        );
    };
}

macro_rules! impl_binary_mult_op_bool {
    ($base_ty:ident, $ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $function:ident) => {
        impl_binary_mult_op_without_numbers!(
            $base_ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $function
        );
        impl_binary_mult_op_assign_number_raw!(
            $ty,
            bool,
            from_bool,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            mk_const_bool
        );
        impl_binary_mult_op_number_raw!(
            &$ty,
            bool,
            from_bool,
            $ty,
            $base_trait,
            $base_fn,
            mk_const_bool
        );
    };
}

macro_rules! impl_binary_mult_op {
    ($base_ty:ident, $ty:ty, $base_trait:ident, $assign_trait:ident, $base_fn:ident, $assign_fn:ident, $construct_constant:ident) => {
        impl_binary_mult_op_without_numbers!(
            $base_ty,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn
        );
        impl_binary_mult_op_assign_number_raw!(
            $ty,
            u64,
            from_u64,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $construct_constant
        );
        impl_binary_mult_op_number_raw!(
            &$ty,
            u64,
            from_u64,
            $ty,
            $base_trait,
            $base_fn,
            $construct_constant
        );
        impl_binary_mult_op_assign_number_raw!(
            $ty,
            i64,
            from_i64,
            $ty,
            $base_trait,
            $assign_trait,
            $base_fn,
            $assign_fn,
            $construct_constant
        );
        impl_binary_mult_op_number_raw!(
            &$ty,
            i64,
            from_i64,
            $ty,
            $base_trait,
            $base_fn,
            $construct_constant
        );
    };
}

// implementations for BV
// impl_binary_op!(BV, Add, AddAssign, add, add_assign, bvadd, mk_const_bv);
// impl_binary_op!(BV, Sub, SubAssign, sub, sub_assign, bvsub, mk_const_bv);
// impl_binary_op!(BV, Mul, MulAssign, mul, mul_assign, bvmul, mk_const_bv);
// impl_binary_op!(
//     BV,
//     BitAnd,
//     BitAndAssign,
//     bitand,
//     bitand_assign,
//     bvand,
//     mk_const_bv
// );
// impl_binary_op!(
//     BV,
//     BitOr,
//     BitOrAssign,
//     bitor,
//     bitor_assign,
//     bvor,
//     mk_const_bv
// );
// impl_binary_op!(
//     BV,
//     BitXor,
//     BitXorAssign,
//     bitxor,
//     bitxor_assign,
//     bvxor,
//     mk_const_bv
// );
// impl_binary_op!(BV, Shl, ShlAssign, shl, shl_assign, bvshl, mk_const_bv);
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
