use crate::ast::{Ast, BV, Bool, binop, trinop, unop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a float value.
pub struct Float {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Float {
    // Create a 32-bit (IEEE-754) Float [`Ast`] from a rust f32
    pub fn from_f32(ctx: &Context, value: f32) -> Float {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_float(ctx.z3_ctx.0, value, sort.z3_sort)
            })
        }
    }

    // Create a 364-bit (IEEE-754) Float [`Ast`] from a rust f64
    pub fn from_f64(ctx: &Context, value: f64) -> Float {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_double(ctx.z3_ctx.0, value, sort.z3_sort)
            })
        }
    }

    pub fn as_f64(&self) -> f64 {
        unsafe { Z3_get_numeral_double(self.ctx.z3_ctx.0, self.z3_ast) }
    }
}

impl Float {
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S, ebits: u32, sbits: u32) -> Float {
        let sort = Sort::float(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 32-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_float32<S: Into<Symbol>>(ctx: &Context, name: S) -> Float {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 64-bit (IEEE-754) Float [`Ast`].
    pub fn new_const_double<S: Into<Symbol>>(ctx: &Context, name: S) -> Float {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &Context, prefix: &str, ebits: u32, sbits: u32) -> Float {
        let sort = Sort::float(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    pub fn fresh_const_float32(ctx: &Context, prefix: &str) -> Float {
        let sort = Sort::float32(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    pub fn fresh_const_double(ctx: &Context, prefix: &str) -> Float {
        let sort = Sort::double(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    // returns RoundingMode towards zero
    pub fn round_towards_zero(ctx: &Context) -> Float {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_zero(ctx.z3_ctx.0)) }
    }

    // returns RoundingMode towards negative
    pub fn round_towards_negative(ctx: &Context) -> Float {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_negative(ctx.z3_ctx.0)) }
    }

    // returns RoundingMode towards positive
    pub fn round_towards_positive(ctx: &Context) -> Float {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_positive(ctx.z3_ctx.0)) }
    }

    // Add two floats of the same size, rounding towards zero
    pub fn add_towards_zero(&self, other: &Self) -> Float {
        Self::round_towards_zero(&self.ctx).add(self, other)
    }

    // Subtract two floats of the same size, rounding towards zero
    pub fn sub_towards_zero(&self, other: &Self) -> Float {
        Self::round_towards_zero(&self.ctx).sub(self, other)
    }

    // Multiply two floats of the same size, rounding towards zero
    pub fn mul_towards_zero(&self, other: &Self) -> Float {
        Self::round_towards_zero(&self.ctx).mul(self, other)
    }

    // Divide two floats of the same size, rounding towards zero
    pub fn div_towards_zero(&self, other: &Self) -> Float {
        Self::round_towards_zero(&self.ctx).div(self, other)
    }

    // Convert to IEEE-754 bit-vector
    pub fn to_ieee_bv(&self) -> BV {
        unsafe {
            BV::wrap(
                &self.ctx,
                Z3_mk_fpa_to_ieee_bv(self.ctx.z3_ctx.0, self.z3_ast),
            )
        }
    }

    unop! {
        unary_abs(Z3_mk_fpa_abs, Self);
        unary_neg(Z3_mk_fpa_neg, Self);
        is_infinite(Z3_mk_fpa_is_infinite, Bool);
        is_normal(Z3_mk_fpa_is_normal, Bool);
        is_subnormal(Z3_mk_fpa_is_subnormal, Bool);
        is_zero(Z3_mk_fpa_is_zero, Bool);
        is_nan(Z3_mk_fpa_is_nan, Bool);
    }
    binop! {
        lt(Z3_mk_fpa_lt, Bool);
        le(Z3_mk_fpa_leq, Bool);
        gt(Z3_mk_fpa_gt, Bool);
        ge(Z3_mk_fpa_geq, Bool);
    }
    trinop! {
        add(Z3_mk_fpa_add, Self);
        sub(Z3_mk_fpa_sub, Self);
        mul(Z3_mk_fpa_mul, Self);
        div(Z3_mk_fpa_div, Self);
    }
}
