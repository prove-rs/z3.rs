use std::ffi::CString;
use z3_sys::*;
use Context;
use Symbol;
use Z3_MUTEX;

impl<'ctx> Symbol<'ctx> {
    pub fn from_int(ctx: &Context, i: u32) -> Symbol {
        Symbol {
            ctx,
            cst: None,
            z3_sym: {
                let guard = Z3_MUTEX.lock().unwrap();
                unsafe { Z3_mk_int_symbol(ctx.z3_ctx, i as ::std::os::raw::c_int) }
            },
        }
    }

    pub fn from_string(ctx: &'ctx Context, s: &str) -> Symbol<'ctx> {
        let ss = CString::new(s).unwrap();
        let p = ss.as_ptr();
        Symbol {
            ctx,
            cst: Some(ss),
            z3_sym: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_string_symbol(ctx.z3_ctx, p)
            },
        }
    }
}
