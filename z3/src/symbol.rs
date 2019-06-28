use std::ffi::CString;
use z3_sys::*;
use Context;
use Symbol;

impl Symbol {
    pub fn as_z3_symbol(&self, ctx: &Context) -> Z3_symbol {
        match self {
            Symbol::Int(i) => {
                unsafe { Z3_mk_int_symbol(ctx.z3_ctx, *i as ::std::os::raw::c_int) }
            }
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, p) }
            }
        }
    }
}
