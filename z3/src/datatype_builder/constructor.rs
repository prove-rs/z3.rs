use z3_sys::{Z3_constructor, Z3_constructor_list, Z3_del_constructor, Z3_del_constructor_list};

use crate::Context;

/// Wrapper around a raw `Z3_constructor`.
pub struct Constructor {
    ctx: Context,
    z3_constructor: Z3_constructor,
}

impl Constructor {
    /// Create a wrapper around a raw `Z3_constructor`.
    pub unsafe fn wrap(ctx: &Context, z3_constructor: Z3_constructor) -> Self {
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
    pub unsafe fn wrap(ctx: &Context, z3_constructor_list: Z3_constructor_list) -> Self {
        Self {
            ctx: ctx.clone(),
            z3_constructor_list,
        }
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
