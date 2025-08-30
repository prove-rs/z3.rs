use log::debug;
use std::cell::RefCell;
use std::clone::Clone;
use std::ffi::CString;
use std::rc::Rc;
use z3_sys::*;

use crate::{Config, ContextHandle};

/// A wrapper around [`Z3_context`] that enforces proper dropping behavior.
/// All high-level code should instead use [`Context`]
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
/// one context to another.
///
/// While it is not safe to access Z3 objects from multiple threads, this library includes
/// a safe structured abstraction for usage of Z3 objects across threads.
/// See [`Synchronized`](crate::Synchronized).
///
///
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
    /// Returns a handle to the default thread-local [`Context`].
    ///
    /// This [`Context`] is used in all z3 operations.
    /// Custom [`Context`]s are supported through [`with_z3_config`](crate::with_z3_config),
    /// which allow for running a closure inside an environment with the provided [`Context`]
    ///
    /// # See also:
    /// - [`with_z3_config`](crate::with_z3_config)
    pub fn thread_local() -> Context {
        DEFAULT_CONTEXT.with(|f| f.borrow().clone())
    }

    /// _Replaces_ the thread-local [`Context`] with a new one created from the given [`Config`].
    /// This is useful if you want to use a specific configuration, but also want
    /// to use the default thread-local context. Note that calling this function will
    /// _replace_ the existing thread-local context. All existing [`Ast`]s and other Z3 objects
    /// that were created using the previous thread-local context will still be valid, but cannot
    /// be used with the new context without translation. You will generally want to call this
    /// before you create any [`Ast`]s or other Z3 objects to avoid confusion. Also note that
    /// since the [`Context`] is thread-local, this will only affect the current thread.
    ///
    /// # See also:
    /// /// - [`Context::thread_local()`]
    pub(crate) fn set_thread_local(ctx: &Context) {
        DEFAULT_CONTEXT.with(|f| {
            *f.borrow_mut() = ctx.clone();
        });
    }

    /// Creates a new Z3 Context using the given configuration.
    #[deprecated(
        note = "The z3 crate now uses an implicit thread-local context. To configure the active context,\
     use `with_z3_config` instead"
    )]
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

    /// Construct a [`Context`] from a raw [`Z3_context`] pointer. This is mostly useful for
    /// consumers who want to interoperate with Z3 contexts created through other means,
    /// such as the C API or other bindings such as Python.
    ///
    /// # Safety
    ///
    /// The caller must ensure the pointer is valid and not already managed elsewhere.
    ///
    /// # Examples
    ///
    /// ```
    /// use z3::ast::Bool;
    /// use z3_sys::{Z3_mk_config, Z3_del_config, Z3_mk_context_rc};
    /// use z3::Context;
    ///
    /// // Create a raw Z3_config using the low-level API
    /// let cfg = unsafe { Z3_mk_config() };
    /// let raw_ctx = unsafe { Z3_mk_context_rc(cfg) };
    /// let ctx = unsafe { Context::from_raw(raw_ctx) };
    /// // Use `ctx` as usual...
    /// unsafe { Z3_del_config(cfg) };
    /// let b = Bool::from_bool(true);
    /// assert_eq!(b.as_bool(), Some(true));
    /// ```
    pub unsafe fn from_raw(z3_ctx: Z3_context) -> Context {
        debug!("from_raw context {z3_ctx:p}");
        Context {
            z3_ctx: Rc::new(ContextInternal(z3_ctx)),
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

/// The default [`Context`] uses [`Config::default`]
///
/// Note: this implementation will be removed in a future release,
/// when [`Context::new`] and [`with_z3_context`](crate::with_z3_context) are removed.
#[allow(deprecated)]
impl Default for Context {
    fn default() -> Self {
        let cfg = Config::default();
        Context::new(&cfg)
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

thread_local! {
    static DEFAULT_CONTEXT: RefCell<Context> = RefCell::new(Context::default());
}
