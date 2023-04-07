use std::convert::TryInto;
use std::ffi::{CStr, CString};
use std::fmt;
use z3_sys::*;
use Context;
use Symbol;
use Z3_MUTEX;

impl Symbol {
    pub fn as_z3_symbol(&self, ctx: &Context) -> Z3_symbol {
        match self {
            Symbol::Int(i) => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, *i as ::std::os::raw::c_int) },
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, p) }
            }
        }
    }

    pub fn new_from_z3_symbol(ctx: &Context, z3_symbol: Z3_symbol) -> Option<Symbol> {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let kind = Z3_get_symbol_kind(ctx.z3_ctx, z3_symbol);
            match kind {
                SymbolKind::Int => Z3_get_symbol_int(ctx.z3_ctx, z3_symbol)
                    .try_into()
                    .ok()
                    .map(|i| Symbol::Int(i)),
                SymbolKind::String => {
                    let s = Z3_get_symbol_string(ctx.z3_ctx, z3_symbol);
                    if s.is_null() {
                        return None;
                    }
                    CStr::from_ptr(s)
                        .to_str()
                        .ok()
                        .map(|s| Symbol::String(s.to_owned()))
                }
            }
        }
    }
}

impl From<u32> for Symbol {
    fn from(val: u32) -> Self {
        Symbol::Int(val)
    }
}

impl From<String> for Symbol {
    fn from(val: String) -> Self {
        Symbol::String(val)
    }
}

impl From<&str> for Symbol {
    fn from(val: &str) -> Self {
        Symbol::String(val.to_owned())
    }
}

impl<'ctx> fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::Int(i) => write!(f, "{}", i),
            Symbol::String(s) => write!(f, "{}", s),
        }
    }
}
