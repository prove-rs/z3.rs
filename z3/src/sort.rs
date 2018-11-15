use std::ffi::CString;
use std::fmt;
use z3_sys::*;
use Context;
use Sort;
use Symbol;
use Z3_MUTEX;

impl<'ctx> Sort<'ctx> {
    pub fn uninterpretd(ctx: &'ctx Context, sym: &Symbol<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_uninterpreted_sort(ctx.z3_ctx, sym.z3_sym)
            },
        }
    }

    pub fn bool(ctx: &Context) -> Sort {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bool_sort(ctx.z3_ctx)
            },
        }
    }

    pub fn int(ctx: &Context) -> Sort {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_int_sort(ctx.z3_ctx)
            },
        }
    }

    pub fn real(ctx: &Context) -> Sort {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_real_sort(ctx.z3_ctx)
            },
        }
    }

    pub fn bitvector(ctx: &Context, sz: u32) -> Sort {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bv_sort(ctx.z3_ctx, sz as ::std::os::raw::c_uint)
            },
        }
    }

    pub fn array(ctx: &'ctx Context, domain: &Sort<'ctx>, range: &Sort<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_array_sort(ctx.z3_ctx, domain.z3_sort, range.z3_sort)
            },
        }
    }

    pub fn set(ctx: &'ctx Context, elt: &Sort<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_set_sort(ctx.z3_ctx, elt.z3_sort)
            },
        }
    }
}

impl<'ctx> fmt::Display for Sort<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe {
            CString::from_raw(Z3_sort_to_string(self.ctx.z3_ctx, self.z3_sort) as *mut i8)
        };
        if p.as_ptr().is_null() {
            return Result::Err(fmt::Error);
        }
        match p.into_string() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => return Result::Err(fmt::Error),
        }
    }
}
