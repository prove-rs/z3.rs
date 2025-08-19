use crate::ast::IntoAst;
use crate::ast::IntoAstCtx;
use crate::ast::{Ast, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_macros::z3;
use z3_sys::*;

/// [`Ast`] node representing a boolean value.
pub struct Bool {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}
#[z3(Context::thread_local)]
impl Bool {

    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S) -> Bool {
        let sort = Sort::bool_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(
                    ctx.z3_ctx.0,
                    name.into().as_z3_symbol_in_ctx(ctx),
                    sort.z3_sort,
                )
            })
        }
    }


    pub fn fresh_const(ctx: &Context, prefix: &str) -> Bool {
        let sort = Sort::bool_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }


    pub fn from_bool(ctx: &Context, b: bool) -> Bool {
        unsafe {
            Self::wrap(ctx, {
                if b {
                    Z3_mk_true(ctx.z3_ctx.0)
                } else {
                    Z3_mk_false(ctx.z3_ctx.0)
                }
            })
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        unsafe {
            match Z3_get_bool_value(self.ctx.z3_ctx.0, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    // This doesn't quite fit the trinop! macro because of the generic argty
    pub fn ite<T>(&self, a: &T, b: &T) -> T
    where
        T: Ast,
    {
        unsafe {
            T::wrap(&self.ctx, {
                Z3_mk_ite(
                    self.ctx.z3_ctx.0,
                    self.z3_ast,
                    a.get_z3_ast(),
                    b.get_z3_ast(),
                )
            })
        }
    }

    varop! {
        and(Z3_mk_and, Self);
        or(Z3_mk_or, Self);
    }
    binop! {
        xor(Z3_mk_xor, Self);
        iff(Z3_mk_iff, Self);
        implies(Z3_mk_implies, Self);
    }
    unop! {
        not(Z3_mk_not, Self);
    }


    pub fn pb_le(ctx: &Context, values: &[(&Bool, i32)], k: i32) -> Bool {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pble(
                    ctx.z3_ctx.0,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }

    pub fn pb_ge(ctx: &Context, values: &[(&Bool, i32)], k: i32) -> Bool {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pbge(
                    ctx.z3_ctx.0,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }

    pub fn pb_eq(ctx: &Context, values: &[(&Bool, i32)], k: i32) -> Bool {
        unsafe {
            Bool::wrap(ctx, {
                assert!(values.len() <= 0xffffffff);
                let (values, coefficients): (Vec<Z3_ast>, Vec<i32>) = values
                    .iter()
                    .map(|(boolean, coefficient)| (boolean.z3_ast, coefficient))
                    .unzip();
                Z3_mk_pbeq(
                    ctx.z3_ctx.0,
                    values.len() as u32,
                    values.as_ptr(),
                    coefficients.as_ptr(),
                    k,
                )
            })
        }
    }
}

impl IntoAst<Bool> for bool {
    fn into_ast(self, a: &Bool) -> Bool {
        Bool::from_bool_in_ctx(&a.ctx, self)
    }
}

impl IntoAstCtx<Bool> for bool {
    fn into_ast_ctx(self, ctx: &Context) -> Bool {
        Bool::from_bool_in_ctx(ctx, self)
    }
}
