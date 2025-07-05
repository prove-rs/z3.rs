use log::debug;
use std::ffi::CString;

use z3_sys::*;

use crate::{Config, Context, ContextHandle};

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {p:p}");
                Z3_set_error_handler(p, None);
                p
            },
        }
    }

    pub fn get_z3_context(&self) -> Z3_context {
        self.z3_ctx
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt();
    }

    /// Obtain a handle that can be used to interrupt computation from another thread.
    ///
    /// # See also:
    ///
    /// - [`ContextHandle`]
    /// - [`ContextHandle::interrupt()`]
    pub fn handle(&self) -> ContextHandle {
        ContextHandle { ctx: self }
    }

    /// Update a global parameter.
    ///
    /// # See also
    ///
    /// - [`Context::update_bool_param_value()`]
    pub fn update_param_value(&mut self, k: &str, v: &str) {
        let ks = CString::new(k).unwrap();
        let vs = CString::new(v).unwrap();
        unsafe { Z3_update_param_value(self.z3_ctx, ks.as_ptr(), vs.as_ptr()) };
    }

    /// Update a global parameter.
    ///
    /// This is a helper function.
    ///
    /// # See also
    ///
    /// - [`Context::update_param_value()`]
    pub fn update_bool_param_value(&mut self, k: &str, v: bool) {
        self.update_param_value(k, if v { "true" } else { "false" });
    }
}

impl ContextHandle<'_> {
    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ctx.z3_ctx);
        }
    }
}

unsafe impl Sync for ContextHandle<'_> {}
unsafe impl Send for ContextHandle<'_> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) };
    }
}
