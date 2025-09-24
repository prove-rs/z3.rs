use crate::ast::IntoAst;
use crate::ast::{Ast, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a boolean value.
pub struct Bool {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}
impl Bool {
    pub fn new_const<S: Into<Symbol>>(name: S) -> Bool {
        let ctx = &Context::thread_local();
        let sort = Sort::bool();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(), sort.z3_sort).unwrap()
            })
        }
    }

    pub fn fresh_const(prefix: &str) -> Bool {
        let ctx = &Context::thread_local();
        let sort = Sort::bool();
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort).unwrap()
            })
        }
    }

    pub fn from_bool(b: bool) -> Bool {
        let ctx = &Context::thread_local();
        unsafe {
            Self::wrap(ctx, {
                if b {
                    Z3_mk_true(ctx.z3_ctx.0).unwrap()
                } else {
                    Z3_mk_false(ctx.z3_ctx.0).unwrap()
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
                .unwrap()
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

    pub fn pb_le(values: &[(&Bool, i32)], k: i32) -> Bool {
        let ctx = &Context::thread_local();
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
                .unwrap()
            })
        }
    }

    pub fn pb_ge(values: &[(&Bool, i32)], k: i32) -> Bool {
        let ctx = &Context::thread_local();
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
                .unwrap()
            })
        }
    }

    pub fn pb_eq(values: &[(&Bool, i32)], k: i32) -> Bool {
        let ctx = &Context::thread_local();
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
                .unwrap()
            })
        }
    }
}
