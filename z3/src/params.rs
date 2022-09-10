use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use Params;
use Symbol;

impl<'ctx> Params<'ctx> {
    unsafe fn wrap(ctx: &'ctx Context, z3_params: Z3_params) -> Params<'ctx> {
        Z3_params_inc_ref(ctx.z3_ctx, z3_params);
        Params { ctx, z3_params }
    }

    pub fn new(ctx: &'ctx Context) -> Params<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_params(ctx.z3_ctx)) }
    }

    pub fn set_symbol<K: Into<Symbol>, V: Into<Symbol>>(&mut self, k: K, v: V) {
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
        unsafe { Z3_params_dec_ref(self.ctx.z3_ctx, self.z3_params) };
    }
}
