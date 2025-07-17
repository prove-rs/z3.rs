use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Sub, SubAssign,
};

use crate::ast::{Ast, BV, Bool, Float, Int, Real};

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
        impl<'ctx> $base_trait<$rhs> for $ty {
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
        impl<'ctx> $assign_trait<$rhs> for $ty {
            fn $assign_fn(&mut self, rhs: $rhs) {
                *self = (self as &$ty).$function(&rhs as &$ty);
            }
        }
    };
}

macro_rules! impl_binary_op_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $base_fn:ident, $function:ident, $construct_constant:ident) => {
        impl<'ctx> $base_trait<$other> for $ty {
            type Output = $output;

            fn $base_fn(self, rhs: $other) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                $base_trait::$base_fn(self, c)
            }
        }

        impl<'ctx> $base_trait<$ty> for $other {
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

        impl<'ctx> $assign_trait<$other> for $ty {
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
        impl<'ctx> $base_trait for $ty {
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
        impl<'ctx> $base_trait<$rhs> for $ty {
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

        impl<'ctx> $assign_trait<$rhs> for $ty {
            fn $assign_fn(&mut self, other: $rhs) {
                *self = $base_ty::$function(self.get_ctx(), &[&self as &$ty, &other as &$ty])
            }
        }
    };
}

macro_rules! impl_binary_mult_op_number_raw {
    ($ty:ty, $other:ty, $other_fn:ident, $output:ty, $base_trait:ident, $base_fn:ident, $construct_constant:ident) => {
        impl<'ctx> $base_trait<$other> for $ty {
            type Output = $output;

            fn $base_fn(self, rhs: $other) -> Self::Output {
                let c;
                $construct_constant!(c, $other_fn, rhs, self);
                $base_trait::$base_fn(self, c)
            }
        }

        impl<'ctx> $base_trait<$ty> for $other {
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

        impl<'ctx> $assign_trait<$other> for $ty {
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
impl_binary_op!(
    BV<'ctx>,
    Add,
    AddAssign,
    add,
    add_assign,
    bvadd,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    Sub,
    SubAssign,
    sub,
    sub_assign,
    bvsub,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    Mul,
    MulAssign,
    mul,
    mul_assign,
    bvmul,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    BitAnd,
    BitAndAssign,
    bitand,
    bitand_assign,
    bvand,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    BitOr,
    BitOrAssign,
    bitor,
    bitor_assign,
    bvor,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    BitXor,
    BitXorAssign,
    bitxor,
    bitxor_assign,
    bvxor,
    mk_const_bv
);
impl_binary_op!(
    BV<'ctx>,
    Shl,
    ShlAssign,
    shl,
    shl_assign,
    bvshl,
    mk_const_bv
);
impl_unary_op!(BV<'ctx>, Not, not, bvnot);
impl_unary_op!(BV<'ctx>, Neg, neg, bvneg);

// implementations for Int
impl_binary_mult_op!(
    Int,
    Int<'ctx>,
    Add,
    AddAssign,
    add,
    add_assign,
    mk_const_int
);
impl_binary_mult_op!(
    Int,
    Int<'ctx>,
    Sub,
    SubAssign,
    sub,
    sub_assign,
    mk_const_int
);
impl_binary_mult_op!(
    Int,
    Int<'ctx>,
    Mul,
    MulAssign,
    mul,
    mul_assign,
    mk_const_int
);
impl_binary_op!(
    Int<'ctx>,
    Div,
    DivAssign,
    div,
    div_assign,
    div,
    mk_const_int
);
impl_binary_op!(
    Int<'ctx>,
    Rem,
    RemAssign,
    rem,
    rem_assign,
    rem,
    mk_const_int
);
impl_unary_op!(Int<'ctx>, Neg, neg, unary_minus);

// implementations for Real
impl_binary_mult_op_without_numbers!(Real, Real<'ctx>, Add, AddAssign, add, add_assign);
impl_binary_mult_op_without_numbers!(Real, Real<'ctx>, Sub, SubAssign, sub, sub_assign);
impl_binary_mult_op_without_numbers!(Real, Real<'ctx>, Mul, MulAssign, mul, mul_assign);
impl_binary_op_without_numbers!(Real<'ctx>, Div, DivAssign, div, div_assign, div);
impl_unary_op!(Real<'ctx>, Neg, neg, unary_minus);

// // implementations for Float
impl_unary_op!(Float<'ctx>, Neg, neg, unary_neg);

// implementations for Bool
impl_binary_mult_op_bool!(
    Bool,
    Bool<'ctx>,
    BitAnd,
    BitAndAssign,
    bitand,
    bitand_assign,
    and
);
impl_binary_mult_op_bool!(
    Bool,
    Bool<'ctx>,
    BitOr,
    BitOrAssign,
    bitor,
    bitor_assign,
    or
);
impl_binary_op_bool!(Bool<'ctx>, BitXor, BitXorAssign, bitxor, bitxor_assign, xor);
impl_unary_op!(Bool<'ctx>, Not, not, not);
