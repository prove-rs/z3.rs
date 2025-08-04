use log::debug;
use std::ffi::CString;
use std::rc::Rc;
use z3_sys::*;

use crate::{Config, ContextHandle};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContextInternal(pub(crate) Z3_context);

impl Drop for ContextInternal {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.0) };
    }
}

/// Manager of all other Z3 objects, global configuration options, etc.
///
/// An application may use multiple Z3 contexts. Objects created in one context
/// cannot be used in another one. However, several objects may be "translated" from
/// one context to another. It is not safe to access Z3 objects from multiple threads.
///
/// # Examples:
///
/// Creating a context with the default configuration:
///
/// ```
/// use z3::{Config, Context};
/// let cfg = Config::new();
/// let ctx = Context::new(&cfg);
/// ```
///
/// # See also:
///
/// - [`Config`]
/// - [`Context::new()`]
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Context {
    pub(crate) z3_ctx: Rc<ContextInternal>,
}
impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {p:p}");
                Z3_set_error_handler(p, None);
                Rc::new(ContextInternal(p))
            },
        }
    }

    pub fn get_z3_context(&self) -> Z3_context {
        self.z3_ctx.0
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
    pub fn handle(&self) -> ContextHandle<'_> {
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
        unsafe { Z3_update_param_value(self.z3_ctx.0, ks.as_ptr(), vs.as_ptr()) };
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
            Z3_interrupt(self.ctx.z3_ctx.0);
        }
    }
}

unsafe impl Sync for ContextHandle<'_> {}
unsafe impl Send for ContextHandle<'_> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx.0) };
    }
}
