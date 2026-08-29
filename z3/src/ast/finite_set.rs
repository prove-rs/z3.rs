use crate::ast::{Array, Ast, Bool, Int, binop, unop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a finite set value.
///
/// Unlike [`Set`](crate::ast::Set), `FiniteSet` is not backed by an array and
/// cannot be built up element-by-element (there is no `add`/`del`). Sets are
/// constructed via [`FiniteSet::singleton`], [`FiniteSet::range`], and the
/// set operations below.
pub struct FiniteSet {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl FiniteSet {
    pub fn new_const<S: Into<Symbol>>(name: S, eltype: &Sort) -> FiniteSet {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(), sort.z3_sort).unwrap()
            })
        }
    }

    pub fn fresh_const(prefix: &str, eltype: &Sort) -> FiniteSet {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort).unwrap()
            })
        }
    }

    /// Creates the empty finite set with the given element sort.
    pub fn empty(eltype: &Sort) -> FiniteSet {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_finite_set_empty(ctx.z3_ctx.0, sort.z3_sort).unwrap(),
            )
        }
    }

    /// Creates a finite set containing a single element.
    pub fn singleton<A: Ast>(elem: &A) -> FiniteSet {
        let ctx = elem.get_ctx();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_finite_set_singleton(ctx.z3_ctx.0, elem.get_z3_ast()).unwrap()
            })
        }
    }

    /// Creates a finite set of integers in the range `[low, high]`.
    pub fn range(low: &Int, high: &Int) -> FiniteSet {
        let ctx = low.get_ctx();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_finite_set_range(ctx.z3_ctx.0, low.get_z3_ast(), high.get_z3_ast()).unwrap()
            })
        }
    }

    /// Check if an item is a member of the set.
    ///
    /// Note that the `element` _must be_ of the `FiniteSet`'s `eltype` sort.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member<A: Ast>(&self, element: &A) -> Bool {
        unsafe {
            Bool::wrap(&self.ctx, {
                Z3_mk_finite_set_member(self.ctx.z3_ctx.0, element.get_z3_ast(), self.z3_ast)
                    .unwrap()
            })
        }
    }

    /// Apply `f` to every element of the set, producing a new finite set.
    ///
    /// `f` must be an [`Array`] of sort `eltype -> range` (Z3 represents
    /// function values structurally as arrays); build one with
    /// [`Array::const_array`], [`ast::lambda_const`](crate::ast::lambda_const),
    /// or an `(as-array f)` wrapper around a [`FuncDecl`](crate::FuncDecl).
    //
    // We avoid the binop! macro because the result element sort differs from `self`'s.
    pub fn map(&self, f: &Array) -> FiniteSet {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_finite_set_map(self.ctx.z3_ctx.0, f.get_z3_ast(), self.z3_ast).unwrap()
            })
        }
    }

    /// Filter the set's elements using the predicate `f`, producing a new finite set.
    ///
    /// `f` must be an [`Array`] of sort `eltype -> Bool` (Z3 represents
    /// function values structurally as arrays); build one with
    /// [`Array::const_array`], [`ast::lambda_const`](crate::ast::lambda_const),
    /// or an `(as-array f)` wrapper around a [`FuncDecl`](crate::FuncDecl).
    pub fn filter(&self, f: &Array) -> FiniteSet {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_finite_set_filter(self.ctx.z3_ctx.0, f.get_z3_ast(), self.z3_ast).unwrap()
            })
        }
    }

    unop! {
        /// Get the cardinality of the set as an [`Int`].
        size(Z3_mk_finite_set_size, Int);
    }
    binop! {
        /// Take the union of two finite sets.
        union(Z3_mk_finite_set_union, Self);
        /// Take the intersection of two finite sets.
        intersect(Z3_mk_finite_set_intersect, Self);
        /// Take the set difference between two finite sets.
        difference(Z3_mk_finite_set_difference, Self);
        /// Check if the set is a subset of another set.
        subset(Z3_mk_finite_set_subset, Bool);
    }
}
