use crate::ast::Ast;
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a datatype or enumeration value.
pub struct Datatype {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Datatype {
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S, sort: &Sort) -> Self {
        assert_eq!(ctx, &sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);

        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &Context, prefix: &str, sort: &Sort) -> Self {
        assert_eq!(ctx, &sort.ctx);
        assert_eq!(sort.kind(), SortKind::Datatype);

        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }
}
