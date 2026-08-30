use crate::ast::{Array, Ast, BV, Bool, Char, Datatype, Float, Int, Real, Seq, Set, SortMarker};
use crate::{Context, Sort, Symbol, ast};
use std::ffi::CString;
use z3_sys::*;

/// A dynamically typed [`Ast`] node.
pub struct Dynamic {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Dynamic {
    pub fn from_ast(ast: &dyn Ast) -> Self {
        unsafe { Self::wrap(ast.get_ctx(), ast.get_z3_ast()) }
    }

    pub fn new_const<S: Into<Symbol>>(name: S, sort: &Sort) -> Self {
        let ctx = &Context::thread_local();
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_const(
                    ctx.z3_ctx.as_ptr(),
                    name.into().as_z3_symbol(),
                    sort.z3_sort,
                )
                .unwrap(),
            )
        }
    }

    pub fn fresh_const(prefix: &str, sort: &Sort) -> Self {
        let ctx = sort.ctx.clone();
        unsafe {
            Self::wrap(&ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.as_ptr(), p, sort.z3_sort).unwrap()
            })
        }
    }

    pub fn sort_kind(&self) -> SortKind {
        unsafe {
            Z3_get_sort_kind(
                self.ctx.z3_ctx.as_ptr(),
                Z3_get_sort(self.ctx.z3_ctx.as_ptr(), self.z3_ast).unwrap(),
            )
        }
    }

    /// Attempt to narrow this `Dynamic` to a specific [`Ast`] type `T`, including a specific
    /// parameterization of a generic type such as `Array<Int, Bool>` or `Seq<BV>`.
    ///
    /// Returns `None` if the runtime [`Sort`] of this value doesn't match what `T` requires.
    /// For a parameterized `T` this recursively checks its domain/range/element marker types
    /// too, so e.g. `narrow::<Array<Int, Bool>>()` only succeeds for arrays whose domain sort
    /// is `Int` and whose range sort is `Bool` -- unlike [`Dynamic::as_array`], which can only
    /// recover the fully-dynamic `Array<Dynamic, Dynamic>`.
    ///
    /// # Examples
    /// ```
    /// # use z3::ast::{Array, Ast, Bool, Dynamic, Int};
    /// # use z3::Sort;
    /// let arr = Array::new_const("a", &Sort::int(), &Sort::bool());
    /// let dyn_arr: Dynamic = arr.into();
    /// assert!(dyn_arr.narrow::<Array<Int, Bool>>().is_some());
    /// assert!(dyn_arr.narrow::<Array<Bool, Int>>().is_none());
    /// ```
    pub fn narrow<T: SortMarker>(&self) -> Option<T> {
        T::sort_matches(&self.get_sort()).then(|| unsafe { T::wrap(&self.ctx, self.z3_ast) })
    }

    /// Returns `None` if the `Dynamic` is not actually a `Bool`
    pub fn as_bool(&self) -> Option<Bool> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually an `Int`
    pub fn as_int(&self) -> Option<Int> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Real`
    pub fn as_real(&self) -> Option<Real> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Float`
    pub fn as_float(&self) -> Option<Float> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Char`
    pub fn as_char(&self) -> Option<Char> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `String`
    pub fn as_string(&self) -> Option<ast::String> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `BV`
    pub fn as_bv(&self) -> Option<BV> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually an `Array`
    pub fn as_array(&self) -> Option<Array> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Set`
    pub fn as_set(&self) -> Option<Set> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Seq`.
    pub fn as_seq(&self) -> Option<Seq> {
        self.narrow()
    }

    /// Returns `None` if the `Dynamic` is not actually a `Datatype`
    pub fn as_datatype(&self) -> Option<Datatype> {
        self.narrow()
    }
}
