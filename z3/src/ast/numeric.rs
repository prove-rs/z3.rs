use crate::ast::Ast;
use crate::ast::{Int, Real};
use num::pow::Pow;
use std::ops::{Add, Div, Mul, Sub};
use z3_sys::*;

// Z3 does support mixing ints and reals in add(), sub(), mul(), div(), and power()
fn add_int_real(i: &Int, r: &Real) -> Real {
    unsafe {
        let args = [i.z3_ast, r.z3_ast];
        Real::wrap(&i.ctx, Z3_mk_add(i.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn add_real_int(r: &Real, i: &Int) -> Real {
    unsafe {
        let args = [r.z3_ast, i.z3_ast];
        Real::wrap(&r.ctx, Z3_mk_add(r.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn sub_int_real(i: &Int, r: &Real) -> Real {
    unsafe {
        let args = [i.z3_ast, r.z3_ast];
        Real::wrap(&i.ctx, Z3_mk_sub(i.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn sub_real_int(r: &Real, i: &Int) -> Real {
    unsafe {
        let args = [r.z3_ast, i.z3_ast];
        Real::wrap(&r.ctx, Z3_mk_sub(r.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn mul_int_real(i: &Int, r: &Real) -> Real {
    unsafe {
        let args = [i.z3_ast, r.z3_ast];
        Real::wrap(&i.ctx, Z3_mk_mul(i.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn mul_real_int(r: &Real, i: &Int) -> Real {
    unsafe {
        let args = [r.z3_ast, i.z3_ast];
        Real::wrap(&r.ctx, Z3_mk_mul(r.ctx.z3_ctx.0, 2, args.as_ptr()))
    }
}

fn div_int_real(i: &Int, r: &Real) -> Real {
    unsafe {
        let i_as_real = Z3_mk_int2real(i.ctx.z3_ctx.0, i.z3_ast);
        Real::wrap(&i.ctx, Z3_mk_div(i.ctx.z3_ctx.0, i_as_real, r.z3_ast))
    }
}

fn div_real_int(r: &Real, i: &Int) -> Real {
    unsafe {
        let i_as_real = Z3_mk_int2real(r.ctx.z3_ctx.0, i.z3_ast);
        Real::wrap(&r.ctx, Z3_mk_div(r.ctx.z3_ctx.0, r.z3_ast, i_as_real))
    }
}

fn pow_int_real(i: &Int, r: &Real) -> Real {
    unsafe { Real::wrap(&i.ctx, Z3_mk_power(i.ctx.z3_ctx.0, i.z3_ast, r.z3_ast)) }
}

fn pow_real_int(r: &Real, i: &Int) -> Real {
    unsafe { Real::wrap(&r.ctx, Z3_mk_power(r.ctx.z3_ctx.0, r.z3_ast, i.z3_ast)) }
}

// Generic macro to implement the four ownership combinations
macro_rules! impl_mixed_binop {
    ($Trait:ident, $method:ident, $L:ident, $R:ident, $builder:ident) => {
        impl $Trait<&$R> for &$L {
            type Output = Real;
            fn $method(self, rhs: &$R) -> Real {
                $builder(self, rhs)
            }
        }
    };
}

// Add
impl_mixed_binop!(Add, add, Int, Real, add_int_real);
impl_mixed_binop!(Add, add, Real, Int, add_real_int);

// Sub
impl_mixed_binop!(Sub, sub, Int, Real, sub_int_real);
impl_mixed_binop!(Sub, sub, Real, Int, sub_real_int);

// Mul
impl_mixed_binop!(Mul, mul, Int, Real, mul_int_real);
impl_mixed_binop!(Mul, mul, Real, Int, mul_real_int);

// Div
impl_mixed_binop!(Div, div, Int, Real, div_int_real);
impl_mixed_binop!(Div, div, Real, Int, div_real_int);

// Pow
impl_mixed_binop!(Pow, pow, Int, Real, pow_int_real);
impl_mixed_binop!(Pow, pow, Real, Int, pow_real_int);
