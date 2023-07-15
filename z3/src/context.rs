use std::ffi::{CStr, CString};
use ast::Ast;
use z3_sys::*;
use Config;
use Context;
use ContextHandle;

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                Z3_set_error_handler(p, None);
                p
            },
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt()
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

    pub fn dump_smtlib<'ctx>(&'ctx self, formula: impl Ast<'ctx>) -> String {
        let name = CString::new("").unwrap();
        let logic = CString::new("").unwrap();
        let status = CString::new("").unwrap();
        let attributes = CString::new("").unwrap();
        let assumptions: Vec<Z3_ast> = vec![];
        unsafe {
            let dump = Z3_benchmark_to_smtlib_string(self.z3_ctx, name.as_ptr(), logic.as_ptr(), status.as_ptr(), attributes.as_ptr(), 0, assumptions.as_ptr(), formula.get_z3_ast());
            CStr::from_ptr(dump).to_str().unwrap().to_string()
        }
    }
}

impl<'ctx> ContextHandle<'ctx> {
    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ctx.z3_ctx);
        }
    }
}

unsafe impl<'ctx> Sync for ContextHandle<'ctx> {}
unsafe impl<'ctx> Send for ContextHandle<'ctx> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) };
    }
}
