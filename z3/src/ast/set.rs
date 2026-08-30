use crate::ast::{Ast, Bool, Dynamic, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use std::marker::PhantomData;
use z3_sys::*;

/// [`Ast`] node representing a set value, whose elements are all of sort `Elt`.
pub struct Set<Elt = Dynamic> {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
    pub(crate) phantom: PhantomData<Elt>,
}

impl<Elt: Ast> Set<Elt> {
    pub fn new_const<S: Into<Symbol>>(name: S, eltype: &Sort<Elt>) -> Set<Elt> {
        let ctx = &Context::thread_local();
        let sort = Sort::set(eltype);
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

    pub fn fresh_const(prefix: &str, eltype: &Sort<Elt>) -> Set<Elt> {
        let ctx = &Context::thread_local();
        let sort = Sort::set(eltype);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.as_ptr(), p, sort.z3_sort).unwrap()
            })
        }
    }

    /// Creates a set that maps the domain to false by default
    pub fn empty(eltype: &Sort<Elt>) -> Set<Elt> {
        let ctx = &Context::thread_local();
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_empty_set(ctx.z3_ctx.as_ptr(), eltype.z3_sort).unwrap(),
            )
        }
    }

    /// Add an element to the set.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn add(&self, element: &Elt) -> Set<Elt> {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_set_add(self.ctx.z3_ctx.as_ptr(), self.z3_ast, element.get_z3_ast()).unwrap()
            })
        }
    }

    /// Remove an element from the set.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn del(&self, element: &Elt) -> Set<Elt> {
        unsafe {
            Self::wrap(&self.ctx, {
                Z3_mk_set_del(self.ctx.z3_ctx.as_ptr(), self.z3_ast, element.get_z3_ast()).unwrap()
            })
        }
    }

    /// Check if an item is a member of the set.
    //
    // We avoid the binop! macro because the argument has a non-Self type
    pub fn member(&self, element: &Elt) -> Bool {
        unsafe {
            Bool::wrap(&self.ctx, {
                Z3_mk_set_member(self.ctx.z3_ctx.as_ptr(), element.get_z3_ast(), self.z3_ast)
                    .unwrap()
            })
        }
    }

    varop! {
        /// Take the intersection of a list of sets.
        intersect(Z3_mk_set_intersect, Self);
        /// Take the union of a list of sets.
        set_union(Z3_mk_set_union, Self);
    }
    unop! {
        /// Take the complement of the set.
        complement(Z3_mk_set_complement, Self);
    }
    binop! {
        /// Check if the set is a subset of another set.
        set_subset(Z3_mk_set_subset, Bool);
        /// Take the set difference between two sets.
        difference(Z3_mk_set_difference, Self);
    }
}
