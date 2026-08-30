use std::fmt;
use z3_sys::*;

use crate::{
    AstVector, Context, FuncEntry, FuncInterp, Interp,
    ast::{Ast, Dynamic},
};

impl Interp {
    /// Returns the const interpretation, if this is [`Interp::Const`].
    pub fn as_const(&self) -> Option<&Dynamic> {
        match self {
            Interp::Const(d) => Some(d),
            Interp::Func(_) => None,
        }
    }

    /// Returns the func interpretation, if this is [`Interp::Func`].
    pub fn as_func(&self) -> Option<&FuncInterp> {
        match self {
            Interp::Const(_) => None,
            Interp::Func(f) => Some(f),
        }
    }
}

impl fmt::Display for Interp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Interp::Const(d) => write!(f, "{d}"),
            Interp::Func(func_interp) => write!(f, "{func_interp}"),
        }
    }
}

impl fmt::Debug for Interp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl FuncInterp {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_func_interp: Z3_func_interp) -> Self {
        unsafe {
            Z3_func_interp_inc_ref(ctx.z3_ctx.as_ptr(), z3_func_interp);
        }

        Self {
            ctx: ctx.clone(),
            z3_func_interp,
        }
    }

    /// Returns the number of arguments in the function interpretation.
    pub fn get_arity(&self) -> usize {
        unsafe { Z3_func_interp_get_arity(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp) as usize }
    }

    /// Returns the number of entries in the function interpretation.
    pub fn get_num_entries(&self) -> u32 {
        unsafe { Z3_func_interp_get_num_entries(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp) }
    }

    /// Adds an entry to the function interpretation.
    pub fn add_entry(&self, args: &[Dynamic], value: &Dynamic) {
        let v: AstVector = args.into();
        unsafe {
            Z3_func_interp_add_entry(
                self.ctx.z3_ctx.as_ptr(),
                self.z3_func_interp,
                v.z3_ast_vector,
                value.z3_ast,
            );
        }
    }

    /// Returns the entries of the function interpretation.
    pub fn get_entries(&self) -> Vec<FuncEntry> {
        (0..self.get_num_entries())
            .map(|i| unsafe {
                FuncEntry::wrap(
                    &self.ctx,
                    Z3_func_interp_get_entry(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp, i)
                        .unwrap(),
                )
            })
            .collect()
    }

    /// Returns the else value of the function interpretation.
    ///
    /// Returns `None` if the interpretation is partial, i.e. Z3 has not assigned a
    /// default value for arguments not covered by [`FuncInterp::get_entries`].
    pub fn get_else(&self) -> Option<Dynamic> {
        let ast =
            unsafe { Z3_func_interp_get_else(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp) }?;
        Some(unsafe { Dynamic::wrap(&self.ctx, ast) })
    }

    /// Sets the else value of the function interpretation.
    pub fn set_else(&self, ast: &Dynamic) {
        unsafe {
            Z3_func_interp_set_else(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp, ast.z3_ast)
        }
    }
}

impl fmt::Display for FuncInterp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        self.get_entries().into_iter().try_for_each(|e| {
            let n = e.get_num_args();
            if n > 1 {
                write!(f, "[")?;
            };
            write!(
                f,
                "{}",
                e.get_args()
                    .into_iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
            if n > 1 {
                write!(f, "]")?;
            }
            write!(f, " -> {}, ", e.get_value())
        })?;
        match self.get_else() {
            Some(else_value) => write!(f, "else -> {else_value}")?,
            None => write!(f, "else -> <partial>")?,
        }
        write!(f, "]")
    }
}

impl fmt::Debug for FuncInterp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Drop for FuncInterp {
    fn drop(&mut self) {
        unsafe {
            Z3_func_interp_dec_ref(self.ctx.z3_ctx.as_ptr(), self.z3_func_interp);
        }
    }
}
