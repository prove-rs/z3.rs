use crate::ast::rounding_mode::RoundingMode;
use crate::ast::{Ast, BV, Bool, binop, unop};
use crate::ast::{IntoAst, IntoAstCtx};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_macros::z3;
use z3_sys::*;

/// [`Ast`] node representing a float value.
pub struct Float {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Float {
    // Create a 32-bit (IEEE-754) Float [`Ast`] from a rust f32
    #[z3(Context::thread_local)]
    pub fn from_f32(ctx: &Context, value: f32) -> Float {
        let sort = Sort::float32_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_float(ctx.z3_ctx.0, value, sort.z3_sort)
            })
        }
    }

    // Create a 364-bit (IEEE-754) Float [`Ast`] from a rust f64
    #[z3(Context::thread_local)]
    pub fn from_f64(ctx: &Context, value: f64) -> Float {
        let sort = Sort::double_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_fpa_numeral_double(ctx.z3_ctx.0, value, sort.z3_sort)
            })
        }
    }

    pub fn as_f64(&self) -> f64 {
        unsafe { Z3_get_numeral_double(self.ctx.z3_ctx.0, self.z3_ast) }
    }

    /// A NaN (Not a Number) value of the given ([`Float`]) [`Sort`].
    #[z3(Context::thread_local)]
    pub fn nan(ctx: &Context, sort: &Sort) -> Float {
        assert!(matches!(sort.kind(), SortKind::FloatingPoint));
        unsafe { Self::wrap(ctx, Z3_mk_fpa_nan(ctx.z3_ctx.0, sort.z3_sort)) }
    }

    /// A single-precision [`Float`] NaN value.
    ///
    /// Any two NANs are equal to each-other, and they are not equal to any concrete number.
    /// # Example
    /// ```
    /// use z3::{ast, Config, Context, Solver, Sort};
    /// use z3::ast::{Ast, Float};
    ///
    /// let ctx = Context::default();
    /// let solver = Solver::new(&ctx);
    ///
    /// let nan_32 = Float::nan32(&ctx);
    /// let nan_64 = Float::nan64(&ctx);
    ///
    /// solver.assert(&nan_32._eq(&nan_32));
    /// solver.assert(&nan_64._eq(&nan_64));
    /// solver.assert(&nan_32._eq(&Float::from_f32(&ctx, 1.0)).not());
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    #[z3(Context::thread_local)]
    pub fn nan32(ctx: &Context) -> Float {
        let s = Sort::float32_in_ctx(ctx);
        Self::nan_in_ctx(ctx, &s)
    }

    /// A double-precision [`Float`] NaN value.
    ///
    /// Any two NANs are equal to each-other, and they are not equal to any concrete number.
    /// # Example
    /// ```
    /// use z3::{ast, Config, Context, Solver, Sort};
    /// use z3::ast::{Ast, Float};
    ///
    /// let ctx = Context::default();
    /// let solver = Solver::new(&ctx);
    ///
    /// let nan_32 = Float::nan32(&ctx);
    /// let nan_64 = Float::nan64(&ctx);
    ///
    /// solver.assert(&nan_32._eq(&nan_32));
    /// solver.assert(&nan_64._eq(&nan_64));
    /// solver.assert(&nan_32._eq(&Float::from_f32(&ctx, 1.0)).not());
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    #[z3(Context::thread_local)]
    pub fn nan64(ctx: &Context) -> Float {
        let s = Sort::double_in_ctx(ctx);
        Self::nan_in_ctx(ctx, &s)
    }
}

impl Float {
    #[z3(Context::thread_local)]
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S, ebits: u32, sbits: u32) -> Float {
        let sort = Sort::float_in_ctx(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol_in_ctx(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 32-bit (IEEE-754) Float [`Ast`].
    #[z3(Context::thread_local)]
    pub fn new_const_float32<S: Into<Symbol>>(ctx: &Context, name: S) -> Float {
        let sort = Sort::float32_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol_in_ctx(ctx), sort.z3_sort)
            })
        }
    }

    /// Create a 64-bit (IEEE-754) Float [`Ast`].
    #[z3(Context::thread_local)]
    pub fn new_const_double<S: Into<Symbol>>(ctx: &Context, name: S) -> Float {
        let sort = Sort::double_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol_in_ctx(ctx), sort.z3_sort)
            })
        }
    }

    #[z3(Context::thread_local)]
    pub fn fresh_const(ctx: &Context, prefix: &str, ebits: u32, sbits: u32) -> Float {
        let sort = Sort::float_in_ctx(ctx, ebits, sbits);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    #[z3(Context::thread_local)]
    pub fn fresh_const_float32(ctx: &Context, prefix: &str) -> Float {
        let sort = Sort::float32_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    #[z3(Context::thread_local)]
    pub fn fresh_const_double(ctx: &Context, prefix: &str) -> Float {
        let sort = Sort::double_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    /// Add with the provided [`RoundingMode`]
    pub fn add_with_rounding_mode<T: IntoAst<Self>>(&self, other: T, r: &RoundingMode) -> Float {
        let other = other.into_ast(self);
        r.add(self, other)
    }

    /// Subtract with the provided [`RoundingMode`]
    pub fn sub_with_rounding_mode<T: IntoAst<Self>>(&self, other: T, r: &RoundingMode) -> Float {
        let other = other.into_ast(self);
        r.sub(self, other)
    }

    /// Multiply with the provided [`RoundingMode`]
    pub fn mul_with_rounding_mode<T: IntoAst<Self>>(&self, other: T, r: &RoundingMode) -> Float {
        let other = other.into_ast(self);
        r.mul(self, other)
    }

    /// Divide with the provided [`RoundingMode`]
    pub fn div_with_rounding_mode<T: IntoAst<Self>>(&self, other: T, r: &RoundingMode) -> Float {
        let other = other.into_ast(self);
        r.div(self, other)
    }

    // Add two floats of the same size, rounding towards zero
    pub fn add_towards_zero<T: IntoAst<Self>>(&self, other: T) -> Float {
        self.add_with_rounding_mode(other, &RoundingMode::round_towards_zero(&self.ctx))
    }

    // Subtract two floats of the same size, rounding towards zero
    pub fn sub_towards_zero<T: IntoAst<Self>>(&self, other: T) -> Float {
        self.sub_with_rounding_mode(other, &RoundingMode::round_towards_zero(&self.ctx))
    }

    // Multiply two floats of the same size, rounding towards zero
    pub fn mul_towards_zero<T: IntoAst<Self>>(&self, other: T) -> Float {
        self.mul_with_rounding_mode(other, &RoundingMode::round_towards_zero(&self.ctx))
    }

    // Divide two floats of the same size, rounding towards zero
    pub fn div_towards_zero<T: IntoAst<Self>>(&self, other: T) -> Float {
        self.div_with_rounding_mode(other, &RoundingMode::round_towards_zero(&self.ctx))
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
}

macro_rules! impl_into_ast {
    ($t:ty, $op:ident) => {
        impl IntoAst<Float> for $t {
            fn into_ast(self, a: &Float) -> Float {
                let sort = a.get_sort();
                let value = self as f64;
                let ctx = a.get_ctx();
                unsafe {
                    Float::wrap(ctx, {
                        Z3_mk_fpa_numeral_double(ctx.z3_ctx.0, value, sort.z3_sort)
                    })
                }
            }
        }
        impl IntoAstCtx<Float> for $t {
            fn into_ast_ctx(self, ctx: &Context) -> Float {
                Float::$op(ctx, self)
            }
        }
    };
}

impl_into_ast!(f32, from_f32_in_ctx);
impl_into_ast!(f64, from_f64_in_ctx);

#[cfg(test)]
mod tests {
    use crate::ast::{Ast, Float};
    use crate::{Context, Solver};

    #[test]
    fn test_nonstandard_float() {
        // this float has a nonstandard size
        let f1 = Float::new_const( "weird", 15, 53);
        let solver = Solver::new();
        // but we can make compatible symbolic floats out of a f64!
        solver.assert(f1._eq(300.0));
        solver.check();
        let model = solver.get_model().unwrap();
        let f1_value = model.eval(&f1, false).unwrap();
        // and we can also use compare models to floats
        assert!(f1_value._eq(300.0).simplify().eq(&true));
    }
}
