use z3_sys::*;
use Context;
use Symbol;
use Sort;
use Z3_MUTEX;

impl<'ctx> Sort<'ctx> {

    pub fn uninterpretd(ctx: &'ctx Context, sym: &Symbol<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_uninterpreted_sort(ctx.z3_ctx, sym.z3_sym)
            }
        }
    }

    pub fn bool(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bool_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn int(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_int_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn real(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_real_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn bitvector(ctx: &Context, sz: u32) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bv_sort(ctx.z3_ctx, sz as ::libc::c_uint)
            }
        }
    }

    pub fn array(ctx: &'ctx Context,
                 domain: &Sort<'ctx>,
                 range: &Sort<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_array_sort(ctx.z3_ctx, domain.z3_sort, range.z3_sort)
            }
        }
    }

    pub fn set(ctx: &'ctx Context, elt: &Sort<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_set_sort(ctx.z3_ctx, elt.z3_sort)
            }
        }
    }

}
