use crate::ast::{Array, Ast, Bool, Dynamic, Int, binop, unop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use std::marker::PhantomData;
use z3_sys::*;

/// [`Ast`] node representing a finite set value, whose elements are all of sort `Elt`.
///
/// Unlike [`Set`](crate::ast::Set), `FiniteSet` is not backed by an array and
/// cannot be built up element-by-element (there is no `add`/`del`). Sets are
/// constructed via [`FiniteSet::singleton`], [`FiniteSet::range`], and the
/// set operations below.
///
/// Z3 has no dedicated [`SortKind`](crate::SortKind) for finite sets: the
/// sort of a `FiniteSet` reports [`SortKind::Unknown`](crate::SortKind::Unknown)
/// from [`Sort::kind`] and [`Dynamic::sort_kind`]. Use [`Sort::narrow`]
/// or [`Dynamic::as_finite_set`] to recognize finite sets.
pub struct FiniteSet<Elt = Dynamic> {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
    pub(crate) phantom: PhantomData<Elt>,
}

impl<Elt: Ast> FiniteSet<Elt> {
    pub fn new_const<S: Into<Symbol>>(name: S, eltype: &Sort<Elt>) -> FiniteSet<Elt> {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
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

    pub fn fresh_const(prefix: &str, eltype: &Sort<Elt>) -> FiniteSet<Elt> {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.as_ptr(), p, sort.z3_sort).unwrap()
            })
        }
    }

    /// Creates the empty finite set with the given element sort.
    pub fn empty(eltype: &Sort<Elt>) -> FiniteSet<Elt> {
        let ctx = &Context::thread_local();
        let sort = Sort::finite_set(eltype);
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_finite_set_empty(ctx.z3_ctx.as_ptr(), sort.z3_sort).unwrap(),
            )
        }
    }

    /// Creates a finite set containing a single element.
    pub fn singleton(elem: &Elt) -> FiniteSet<Elt> {
        let ctx = elem.get_ctx();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_finite_set_singleton(ctx.z3_ctx.as_ptr(), elem.get_z3_ast()).unwrap()
            })
        }
    }

    /// Check if an item is a member of the set.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member(&self, element: &Elt) -> Bool {
        unsafe {
            Bool::wrap(&self.ctx, {
                Z3_mk_finite_set_member(self.ctx.z3_ctx.as_ptr(), element.get_z3_ast(), self.z3_ast)
                    .unwrap()
            })
        }
    }

    /// Apply `f` to every element of the set, producing a new finite set.
    ///
    /// `f` is an [`Array`] of sort `Elt -> R` (Z3 represents
    /// function values structurally as arrays); build one with
    /// [`Array::const_array`], [`ast::lambda_const`](crate::ast::lambda_const),
    /// or an `(as-array f)` wrapper around a [`FuncDecl`](crate::FuncDecl).
    //
    // We avoid the binop! macro because the result element sort differs from `self`'s.
    pub fn map<R: Ast>(&self, f: &Array<Elt, R>) -> FiniteSet<R> {
        unsafe {
            FiniteSet::wrap(&self.ctx, {
                Z3_mk_finite_set_map(self.ctx.z3_ctx.as_ptr(), f.get_z3_ast(), self.z3_ast).unwrap()
            })
        }
    }

    /// Filter the set's elements using the predicate `f`, producing a new finite set.
    ///
    /// `f` is an [`Array`] of sort `Elt -> Bool` (Z3 represents
    /// function values structurally as arrays); build one with
    /// [`Array::const_array`], [`ast::lambda_const`](crate::ast::lambda_const),
    /// or an `(as-array f)` wrapper around a [`FuncDecl`](crate::FuncDecl).
    pub fn filter(&self, f: &Array<Elt, Bool>) -> FiniteSet<Elt> {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_finite_set_filter(self.ctx.z3_ctx.as_ptr(), f.get_z3_ast(), self.z3_ast)
                    .unwrap()
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

impl FiniteSet<Int> {
    /// Creates a finite set of integers in the range `[low, high]`.
    pub fn range(low: &Int, high: &Int) -> FiniteSet<Int> {
        let ctx = low.get_ctx();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_finite_set_range(ctx.z3_ctx.as_ptr(), low.get_z3_ast(), high.get_z3_ast())
                    .unwrap()
            })
        }
    }
}

impl Dynamic {
    /// Returns `None` if the `Dynamic` is not actually a `FiniteSet`.
    ///
    /// Unlike the other `as_*` methods, this does not dispatch on
    /// [`Dynamic::sort_kind`], which is [`SortKind::Unknown`](crate::SortKind::Unknown)
    /// for finite sets.
    pub fn as_finite_set(&self) -> Option<FiniteSet> {
        self.narrow()
    }
}
