use z3_sys::*;
use Config;
use Context;
use ContextHandle;
use Z3_MUTEX;

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
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
    pub fn handle(&self) -> ContextHandle {
        ContextHandle { ctx: self }
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
