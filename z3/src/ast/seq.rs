use crate::ast::Borrow;
use std::ffi::CString;
use z3_sys::*;
use crate::ast::{varop, Ast, Dynamic, Int};
use crate::{Context, Sort, Symbol};

/// [`Ast`] node representing a sequence value.
pub struct Seq {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Seq {
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S, eltype: &Sort) -> Self {
        let sort = Sort::seq(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    pub fn fresh_const(ctx: &Context, prefix: &str, eltype: &Sort) -> Self {
        let sort = Sort::seq(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    /// Create a unit sequence of `a`.
    pub fn unit<A: Ast>(ctx: &Context, a: &A) -> Self {
        unsafe { Self::wrap(ctx, Z3_mk_seq_unit(ctx.z3_ctx.0, a.get_z3_ast())) }
    }

    /// Retrieve the unit sequence positioned at position `index`.
    /// Use [`Seq::nth`] to get just the element.
    pub fn at(&self, index: &Int) -> Self {
        unsafe {
            Self::wrap(
                &self.ctx,
                Z3_mk_seq_at(self.ctx.z3_ctx.0, self.z3_ast, index.z3_ast),
            )
        }
    }

    /// Retrieve the element positioned at position `index`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, Solver, Sort};
    /// # use z3::ast::{Ast, Bool, Int, Seq};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// let seq = Seq::fresh_const(&ctx, "", &Sort::bool(&ctx));
    ///
    /// solver.assert(
    ///     &seq.nth(&Int::from_u64(&ctx, 0))
    ///         .simplify()
    ///         .as_bool()
    ///         .unwrap()
    ///         ._eq(&Bool::from_bool(&ctx, true))
    /// );
    /// ```
    pub fn nth(&self, index: &Int) -> Dynamic {
        unsafe {
            Dynamic::wrap(
                &self.ctx,
                Z3_mk_seq_nth(self.ctx.z3_ctx.0, self.z3_ast, index.z3_ast),
            )
        }
    }

    pub fn length(&self) -> Int {
        unsafe { Int::wrap(&self.ctx, Z3_mk_seq_length(self.ctx.z3_ctx.0, self.z3_ast)) }
    }

    varop! {
        /// Concatenate sequences.
        concat(Z3_mk_seq_concat, Self);
    }
}