use crate::ast::{Ast, Dynamic};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use std::marker::PhantomData;
use z3_sys::*;

/// [`Ast`] node representing an array value.
/// An array in Z3 is a mapping from indices of sort `D` to values of sort `R`.
pub struct Array<D = Dynamic, R = Dynamic> {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
    pub(crate) phantom: PhantomData<(D, R)>,
}

impl<D: Ast, R: Ast> Array<D, R> {
    /// Create an `Array` which maps from indices of the `domain` `Sort` to
    /// values of the `range` `Sort`.
    ///
    /// All values in the `Array` will be unconstrained.
    pub fn new_const<S: Into<Symbol>>(name: S, domain: &Sort<D>, range: &Sort<R>) -> Array<D, R> {
        let ctx = &Context::thread_local();
        let sort = Sort::array(domain, range);
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

    pub fn fresh_const(prefix: &str, domain: &Sort<D>, range: &Sort<R>) -> Array<D, R> {
        let ctx = &Context::thread_local();
        let sort = Sort::array(domain, range);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.as_ptr(), p, sort.z3_sort).unwrap()
            })
        }
    }

    /// Create a "constant array", that is, an `Array` initialized so that all of the
    /// indices in the `domain` map to the given value `val`
    pub fn const_array(domain: &Sort<D>, val: &R) -> Array<D, R> {
        let ctx = &Context::thread_local();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const_array(ctx.z3_ctx.as_ptr(), domain.z3_sort, val.get_z3_ast()).unwrap()
            })
        }
    }

    /// Get the value at a given index in the array.
    pub fn select(&self, index: &D) -> R {
        unsafe {
            R::wrap(&self.ctx, {
                Z3_mk_select(self.ctx.z3_ctx.as_ptr(), self.z3_ast, index.get_z3_ast()).unwrap()
            })
        }
    }

    /// n-ary Array read. `idxs` are the indices of the array that gets read.
    /// This is useful for applying lambdas.
    pub fn select_n(&self, idxs: &[&dyn Ast]) -> R {
        let idxs: Vec<_> = idxs.iter().map(|idx| idx.get_z3_ast()).collect();

        unsafe {
            R::wrap(&self.ctx, {
                Z3_mk_select_n(
                    self.ctx.z3_ctx.as_ptr(),
                    self.z3_ast,
                    idxs.len().try_into().unwrap(),
                    idxs.as_ptr() as *const Z3_ast,
                )
                .unwrap()
            })
        }
    }

    /// Update the value at a given index in the array.
    pub fn store(&self, index: &D, value: &R) -> Self {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_store(
                    self.ctx.z3_ctx.as_ptr(),
                    self.z3_ast,
                    index.get_z3_ast(),
                    value.get_z3_ast(),
                )
                .unwrap()
            })
        }
    }

    /// Returns true if the array is a const array (i.e. `a.is_const_array() => exists v, forall i. select(a, i) == v`)
    ///
    /// # Examples
    /// ```
    /// # use z3::{ast, Config, Context, ast::{Array, Int}, Sort};
    /// # use z3::ast::Ast;
    /// # use std::convert::TryInto;
    /// let arr = Array::const_array(&Sort::int(), &Int::from_u64(9));
    /// assert!(arr.is_const_array());
    /// let arr2 = Array::fresh_const("a", &Sort::int(), &Sort::int());
    /// assert!(!arr2.is_const_array());
    /// ```
    pub fn is_const_array(&self) -> bool {
        // python:
        // is_app_of(a, Z3_OP_CONST_ARRAY)
        // >> is_app(a) and a.decl().kind() == Z3_OP_CONST_ARRAY
        self.is_app() && matches!(self.decl().kind(), DeclKind::ConstArray)
    }
}
