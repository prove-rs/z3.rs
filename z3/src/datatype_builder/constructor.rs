use z3_sys::{
    Z3_constructor, Z3_constructor_list, Z3_del_constructor, Z3_del_constructor_list,
    Z3_mk_constructor, Z3_mk_constructor_list, Z3_sort, Z3_symbol,
};

use crate::Context;

/// Wrapper around a raw `Z3_constructor`.
pub struct Constructor {
    ctx: Context,
    z3_constructor: Z3_constructor,
}

impl Constructor {
    /// Create a wrapper around a raw `Z3_constructor`.
    ///
    /// This does not allocate a new Z3 constructor; it wraps an existing raw
    /// handle and will call `Z3_del_constructor` when dropped.
    pub unsafe fn wrap(ctx: &Context, z3_constructor: Z3_constructor) -> Self {
        Self {
            ctx: ctx.clone(),
            z3_constructor,
        }
    }

    /// Create a new Z3 constructor via the FFI and wrap it.
    ///
    /// This mirrors the parameters of `Z3_mk_constructor`. Callers must ensure
    /// that the pointers passed in are valid for the duration of the call.
    pub unsafe fn new(
        ctx: &Context,
        cname: Z3_symbol,
        rname: Z3_symbol,
        num_fs: ::std::os::raw::c_uint,
        field_names: *const Z3_symbol,
        field_sorts: *const Option<Z3_sort>,
        sort_refs: *mut ::std::os::raw::c_uint,
    ) -> Self {
        // Call the unsafe FFI function inside an inner `unsafe` block to avoid
        // the `unsafe_op_in_unsafe_fn` warning and to make the unsafe region
        // explicit.
        let z3_constructor = unsafe {
            Z3_mk_constructor(
                ctx.z3_ctx.0,
                cname,
                rname,
                num_fs,
                field_names,
                field_sorts,
                sort_refs,
            )
        }
        .unwrap();
        Self {
            ctx: ctx.clone(),
            z3_constructor,
        }
    }

    /// Access the underlying raw Z3 handle.
    pub fn z3_constructor(&self) -> Z3_constructor {
        self.z3_constructor
    }

    /// Borrow the context associated with this constructor.
    pub fn ctx(&self) -> &Context {
        &self.ctx
    }
}

impl Drop for Constructor {
    fn drop(&mut self) {
        unsafe {
            Z3_del_constructor(self.ctx.z3_ctx.0, self.z3_constructor);
        }
    }
}

/// Wrapper around a raw `Z3_constructor_list`.
pub struct ConstructorList {
    ctx: Context,
    z3_constructor_list: Z3_constructor_list,
}

impl ConstructorList {
    /// Create a wrapper around a raw `Z3_constructor_list`.
    ///
    /// This does not allocate a new Z3 constructor list; it wraps an existing
    /// raw handle and will call `Z3_del_constructor_list` when dropped.
    pub unsafe fn wrap(ctx: &Context, z3_constructor_list: Z3_constructor_list) -> Self {
        Self {
            ctx: ctx.clone(),
            z3_constructor_list,
        }
    }

    /// Create a new Z3 constructor list via the FFI and wrap it.
    pub fn new(ctx: &Context, ctors: &[Constructor]) -> Self {
        let num_cs = ctors.len();
        // Build a temporary vector of raw constructor handles to pass to
        // `Z3_mk_constructor_list`. The underlying constructors are owned by
        // the `ctors` slice, which keeps them alive.
        let mut cs_handles: Vec<Z3_constructor> =
            ctors.iter().map(|c| c.z3_constructor()).collect();

        // Call the unsafe FFI function inside an inner `unsafe` block to avoid
        // the `unsafe_op_in_unsafe_fn` warning and to make the unsafe region
        // explicit.
        let z3_constructor_list = unsafe {
            Z3_mk_constructor_list(
                ctx.z3_ctx.0,
                num_cs.try_into().unwrap(),
                cs_handles.as_mut_ptr(),
            )
        }
        .unwrap();

        unsafe { Self::wrap(ctx, z3_constructor_list) }
    }

    /// Access the underlying raw Z3 handle.
    pub fn z3_constructor_list(&self) -> Z3_constructor_list {
        self.z3_constructor_list
    }

    /// Borrow the context associated with this constructor list.
    pub fn ctx(&self) -> &Context {
        &self.ctx
    }
}

impl Drop for ConstructorList {
    fn drop(&mut self) {
        unsafe {
            Z3_del_constructor_list(self.ctx.z3_ctx.0, self.z3_constructor_list);
        }
    }
}
