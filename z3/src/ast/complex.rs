use crate::ast::Ast;
use crate::ast::{Int, Real, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a complex value: a pair of [`Real`] components.
///
/// Complex numbers support addition, subtraction, multiplication, negation,
/// division and equality. They have no ordering and no exponentiation.
/// Division by zero is totalized: at a zero denominator both components take
/// the same (unspecified) Real `0/0` value.
///
/// Requires Z3 5.3.1 or newer.
pub struct Complex {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Complex {
    pub fn new_const<S: Into<Symbol>>(name: S) -> Complex {
        let ctx = &Context::thread_local();
        let sort = Sort::complex();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(
                    ctx.z3_ctx.as_ptr(),
                    name.into().as_z3_symbol(),
                    sort.z3_sort,
                )
                .unwrap()
            })
        }
    }

    pub fn fresh_const(prefix: &str) -> Complex {
        let ctx = &Context::thread_local();
        let sort = Sort::complex();
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.as_ptr(), p, sort.z3_sort).unwrap()
            })
        }
    }

    /// Create the complex number `re + im*i` from its components.
    pub fn new(re: &Real, im: &Real) -> Complex {
        unsafe {
            Self::wrap(
                &re.ctx,
                Z3_mk_complex(re.ctx.z3_ctx.as_ptr(), re.z3_ast, im.z3_ast).unwrap(),
            )
        }
    }

    /// Create the complex number `re_num/re_den + (im_num/im_den)*i`.
    pub fn from_rationals(re_num: i64, re_den: i64, im_num: i64, im_den: i64) -> Complex {
        Self::new(
            &Real::from_rational(re_num, re_den),
            &Real::from_rational(im_num, im_den),
        )
    }

    /// Embed a real as the complex number `ast + 0i`.
    pub fn from_real(ast: &Real) -> Complex {
        Self::new(ast, &Real::from_rational(0, 1))
    }

    /// Embed an integer as the complex number `ast + 0i`.
    pub fn from_int(ast: &Int) -> Complex {
        Self::from_real(&ast.to_real())
    }

    /// If both components of this complex number simplify to rational
    /// numerals that fit in `i64`, return them as
    /// `((re_num, re_den), (im_num, im_den))`.
    ///
    /// This is mainly useful for reading back values from a [`crate::Model`].
    pub fn as_rationals(&self) -> Option<((i64, i64), (i64, i64))> {
        let re = self.real_part().simplify().as_rational()?;
        let im = self.imag_part().simplify().as_rational()?;
        Some((re, im))
    }

    unop! {
        /// The real component of this complex number.
        real_part(Z3_mk_real_part, Real);
        /// The imaginary component of this complex number.
        imag_part(Z3_mk_imag_part, Real);
    }

    varop! {
        add(Z3_mk_add, Self);
        sub(Z3_mk_sub, Self);
        mul(Z3_mk_mul, Self);
    }
    unop! {
        unary_minus(Z3_mk_unary_minus, Self);
    }
    binop! {
        div(Z3_mk_div, Self);
    }
}

impl From<Real> for Complex {
    fn from(value: Real) -> Self {
        Complex::from_real(&value)
    }
}

impl From<&Real> for Complex {
    fn from(value: &Real) -> Self {
        Complex::from_real(value)
    }
}

impl From<Int> for Complex {
    fn from(value: Int) -> Self {
        Complex::from_int(&value)
    }
}

impl From<&Int> for Complex {
    fn from(value: &Int) -> Self {
        Complex::from_int(value)
    }
}
