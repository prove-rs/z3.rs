use crate::ast::IntoAstCtx;
use crate::ast::{Ast, Dynamic, Int, varop};
use crate::ast::{Bool, IntoAst};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_macros::z3;
use z3_sys::*;

/// [`Ast`] node representing a sequence value.
pub struct Seq {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}
#[z3(Context::thread_local)]
impl Seq {

    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S, eltype: &Sort) -> Self {
        let sort = Sort::seq_in_ctx(ctx, eltype);
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


    pub fn fresh_const(ctx: &Context, prefix: &str, eltype: &Sort) -> Self {
        let sort = Sort::seq_in_ctx(ctx, eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    /// the concatenation of any sequence T and the empty sequence is T.
    /// # Example
    /// ```
    /// use z3::{ast, Config, Context, Solver, Sort};
    /// use z3::ast::{Ast, Seq};
    /// let solver = Solver::new();
    /// let empty_seq = Seq::empty(&Sort::int());
    /// let any_seq = Seq::new_const("any_seq", &Sort::int());
    /// let concatenated = Seq::concat(&[&empty_seq, &any_seq]);
    ///
    /// solver.assert(&concatenated._eq(&any_seq));
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```

    pub fn empty(ctx: &Context, eltype: &Sort) -> Self {
        let sort = Sort::seq_in_ctx(ctx, eltype);
        unsafe { Self::wrap(ctx, Z3_mk_seq_empty(ctx.z3_ctx.0, sort.z3_sort)) }
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
    /// # let solver = Solver::new();
    /// let seq = Seq::fresh_const( "", &Sort::bool());
    ///
    /// solver.assert(
    ///     &seq.nth(0)
    ///         .simplify()
    ///         .as_bool()
    ///         .unwrap()
    ///         ._eq(true)
    /// );
    /// ```
    pub fn nth<T: IntoAstCtx<Int>>(&self, index: T) -> Dynamic {
        let index = index.into_ast_ctx(&self.ctx);
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

    /// Any extension of a seq contains itself.
    /// # Example
    /// ```
    /// # use z3::{ast, Config, Context, Solver, Sort};
    /// # use z3::ast::{Ast, Bool, Seq};
    /// let solver = Solver::new();
    /// let seq1 = Seq::unit(&ast::Int::from_u64(0));
    /// let seq2 = Seq::unit(&ast::Int::from_u64(1));
    /// let concatenated = Seq::concat(&[&seq1, &seq2]);
    ///
    /// solver.assert(&Bool::and(&[&concatenated.contains(&seq1), &concatenated.contains(&seq2)]));
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn contains<T: IntoAst<Self>>(&self, containee: T) -> Bool {
        let containee = containee.into_ast(self);
        unsafe {
            Bool::wrap(
                &self.ctx,
                Z3_mk_seq_contains(self.ctx.z3_ctx.0, self.z3_ast, containee.z3_ast),
            )
        }
    }

    varop! {
        /// Concatenate sequences.
        concat(Z3_mk_seq_concat, Self);
    }
}
