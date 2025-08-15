use crate::ast::Borrow;
use num::BigInt;
use std::ffi::CString;
use z3_sys::*;
use crate::{Context, Sort, Symbol};
use crate::ast::{binop, bool, unop, varop, Ast, Bool, BV};
use crate::ast::real::Real;

/// [`Ast`] node representing an integer value.
pub struct Int {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Int {
    pub fn from_big_int(ctx: &Context, value: &BigInt) -> Int {
        Int::from_str(ctx, &value.to_str_radix(10)).unwrap()
    }

    pub fn from_str(ctx: &Context, value: &str) -> Option<Int> {
        let sort = Sort::int(ctx);
        let ast = unsafe {
            let int_cstring = CString::new(value).unwrap();
            let numeral_ptr = Z3_mk_numeral(ctx.z3_ctx.0, int_cstring.as_ptr(), sort.z3_sort);
            if numeral_ptr.is_null() {
                return None;
            }

            numeral_ptr
        };
        Some(unsafe { Int::wrap(ctx, ast) })
    }
}

impl Int {
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S) -> Int {
        let sort = Sort::int(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &Context, prefix: &str) -> Int {
        let sort = Sort::int(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    pub fn from_i64(ctx: &Context, i: i64) -> Int {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap(ctx, Z3_mk_int64(ctx.z3_ctx.0, i, sort.z3_sort)) }
    }

    pub fn from_u64(ctx: &Context, u: u64) -> Int {
        let sort = Sort::int(ctx);
        unsafe { Self::wrap(ctx, Z3_mk_unsigned_int64(ctx.z3_ctx.0, u, sort.z3_sort)) }
    }

    pub fn as_i64(&self) -> Option<i64> {
        unsafe {
            let mut tmp: ::std::os::raw::c_longlong = 0;
            if Z3_get_numeral_int64(self.ctx.z3_ctx.0, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        unsafe {
            let mut tmp: ::std::os::raw::c_ulonglong = 0;
            if Z3_get_numeral_uint64(self.ctx.z3_ctx.0, self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }

    pub fn from_real(ast: &Real) -> Int {
        unsafe { Self::wrap(&ast.ctx, Z3_mk_real2int(ast.ctx.z3_ctx.0, ast.z3_ast)) }
    }

    /// Create a real from an integer.
    /// This is just a convenience wrapper around
    /// [`Real::from_int()`]; see notes there.
    pub fn to_real(&self) -> Real {
        Real::from_int(self)
    }

    /// Create an integer from a bitvector.
    ///
    /// Signed and unsigned version.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, SatResult, Solver};
    /// # use z3::ast::Ast;
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let bv = ast::BV::new_const(&ctx, "x", 32);
    /// solver.assert(&bv._eq(&ast::BV::from_i64(&ctx, -3, 32)));
    ///
    /// let x = ast::Int::from_bv(&bv, true);
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// let model = solver.get_model().unwrap();
    ///
    /// assert_eq!(-3, model.eval(&x, true).unwrap().as_i64().unwrap());
    /// ```
    pub fn from_bv(ast: &BV, signed: bool) -> Int {
        unsafe {
            Self::wrap(&ast.ctx, {
                Z3_mk_bv2int(ast.ctx.z3_ctx.0, ast.z3_ast, signed)
            })
        }
    }

    /// Create a bitvector from an integer.
    /// This is just a convenience wrapper around
    /// [`BV::from_int()`]; see notes there.
    pub fn to_ast(&self, sz: u32) -> BV {
        BV::from_int(self, sz)
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
        rem(Z3_mk_rem, Self);
        modulo(Z3_mk_mod, Self);
        power(Z3_mk_power, Real);
        lt(Z3_mk_lt, Bool);
        le(Z3_mk_le, Bool);
        gt(Z3_mk_gt, Bool);
        ge(Z3_mk_ge, Bool);
    }
    // Z3 does support mixing ints and reals in add(), sub(), mul(), div(), and power()
    //   (but not rem(), modulo(), lt(), le(), gt(), or ge()).
    // TODO: we could consider expressing this by having a Numeric trait with these methods.
    //    Int and Real would have the Numeric trait, but not the other Asts.
    // For example:
    //   fn add(&self, other: &impl Numeric) -> Dynamic { ... }
    // Note the return type would have to be Dynamic I think (?), as the exact result type
    //   depends on the particular types of the inputs.
    // Alternately, we could just have
    //   Int::add_real(&self, other: &Real) -> Real
    // and
    //   Real::add_int(&self, other: &Int) -> Real
    // This might be cleaner because we know exactly what the output type will be for these methods.
}