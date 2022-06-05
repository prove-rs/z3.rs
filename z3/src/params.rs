use std::ffi::{CStr, CString};
use std::fmt;
use z3_sys::*;
use Context;
use Params;
use Symbol;
use Z3_MUTEX;

impl<'ctx> Params<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Params<'ctx> {
        Params {
            ctx,
            z3_params: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_params(ctx.z3_ctx);
                Z3_params_inc_ref(ctx.z3_ctx, p);
                p
            },
        }
    }

    pub fn set_symbol<K: Into<Symbol>, V: Into<Symbol>>(&mut self, k: K, v: V) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_params_set_symbol(
                self.ctx.z3_ctx,
                self.z3_params,
                k.into().as_z3_symbol(self.ctx),
                v.into().as_z3_symbol(self.ctx),
            )
        };
    }

    pub fn set_bool<K: Into<Symbol>>(&mut self, k: K, v: bool) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_params_set_bool(
                self.ctx.z3_ctx,
                self.z3_params,
                k.into().as_z3_symbol(self.ctx),
                v,
            )
        };
    }

    pub fn set_f64<K: Into<Symbol>>(&mut self, k: K, v: f64) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_params_set_double(
                self.ctx.z3_ctx,
                self.z3_params,
                k.into().as_z3_symbol(self.ctx),
                v,
            )
        };
    }

    pub fn set_u32<K: Into<Symbol>>(&mut self, k: K, v: u32) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_params_set_uint(
                self.ctx.z3_ctx,
                self.z3_params,
                k.into().as_z3_symbol(self.ctx),
                v,
            )
        };
    }
}

/// Set a global (or module) parameter. This setting is shared by all Z3 contexts.
pub fn set_global_param(param_id: &str, param_value: &str) {
    let param_id = CString::new(param_id).unwrap();
    let param_value = CString::new(param_value).unwrap();
    let _guard = Z3_MUTEX.lock().unwrap();
    unsafe {
        Z3_global_param_set(param_id.as_ptr(), param_value.as_ptr());
    }
}

/// Get a global (or module) parameter.
pub fn get_global_param(param_id: &str) -> Option<String> {
    let param_id = CString::new(param_id).unwrap();
    let _guard = Z3_MUTEX.lock().unwrap();
    let mut ptr = std::ptr::null();
    if unsafe { Z3_global_param_get(param_id.as_ptr(), &mut ptr as *mut *const i8) } {
        let s = unsafe { CStr::from_ptr(ptr) };
        s.to_str().ok().map(|s| s.to_owned())
    } else {
        None
    }
}

/// Restore the value of all global (and module) parameters. This command will not affect already created objects (such as tactics and solvers).
pub fn reset_all_global_params() {
    let _guard = Z3_MUTEX.lock().unwrap();
    unsafe { Z3_global_param_reset_all() };
}

impl<'ctx> fmt::Display for Params<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_params_to_string(self.ctx.z3_ctx, self.z3_params) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Params<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Params<'ctx> {
    fn drop(&mut self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_params_dec_ref(self.ctx.z3_ctx, self.z3_params) };
    }
}
