use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use FuncDecl;
use Sort;
use Symbol;

impl<'ctx> Sort<'ctx> {
    pub(crate) fn new(ctx: &'ctx Context, z3_sort: Z3_sort) -> Sort<'ctx> {
        unsafe {
            Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort))
        };
        Sort {
            ctx,
            z3_sort,
        }
    }

    pub fn uninterpreted(ctx: &'ctx Context, name: Symbol) -> Sort<'ctx> {
        Sort::new(ctx, unsafe {
            Z3_mk_uninterpreted_sort(ctx.z3_ctx, name.as_z3_symbol(ctx))
        })
    }

    pub fn bool(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe {
            Z3_mk_bool_sort(ctx.z3_ctx)
        })
    }

    pub fn int(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe {
            Z3_mk_int_sort(ctx.z3_ctx)
        })
    }

    pub fn real(ctx: &Context) -> Sort {
        Sort::new(ctx, unsafe {
            Z3_mk_real_sort(ctx.z3_ctx)
        })
    }

    pub fn bitvector(ctx: &Context, sz: u32) -> Sort {
        Sort::new(ctx, unsafe {
            Z3_mk_bv_sort(ctx.z3_ctx, sz as ::std::os::raw::c_uint)
        })
    }

    pub fn array(ctx: &'ctx Context, domain: &Sort<'ctx>, range: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::new(ctx, unsafe {
            Z3_mk_array_sort(ctx.z3_ctx, domain.z3_sort, range.z3_sort)
        })
    }

    pub fn set(ctx: &'ctx Context, elt: &Sort<'ctx>) -> Sort<'ctx> {
        Sort::new(ctx, unsafe {
            Z3_mk_set_sort(ctx.z3_ctx, elt.z3_sort)
        })
    }

    pub fn enumeration(
        ctx: &'ctx Context,
        name: Symbol,
        enum_names: &[Symbol],
    ) -> (Sort<'ctx>, Vec<FuncDecl<'ctx>>, Vec<FuncDecl<'ctx>>) {
        let enum_names: Vec<_> = enum_names.iter().map(|s| s.as_z3_symbol(ctx)).collect();
        let mut enum_consts = vec![std::ptr::null_mut(); enum_names.len()];
        let mut enum_testers = vec![std::ptr::null_mut(); enum_names.len()];

        let sort = Sort::new(ctx, unsafe {
            Z3_mk_enumeration_sort(
                ctx.z3_ctx,
                name.as_z3_symbol(ctx),
                enum_names.len().try_into().unwrap(),
                enum_names.as_ptr(),
                enum_consts.as_mut_ptr(),
                enum_testers.as_mut_ptr(),
            )
        });

        // increase ref counts
        for i in &enum_consts {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }
        for i in &enum_testers {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }

        // convert to Rust types
        let enum_consts: Vec<_> = enum_consts
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx,
                z3_func_decl: *z3_func_decl,
            })
            .collect();
        let enum_testers: Vec<_> = enum_testers
            .iter()
            .map(|z3_func_decl| FuncDecl {
                ctx,
                z3_func_decl: *z3_func_decl,
            })
            .collect();

        (sort, enum_consts, enum_testers)
    }

    pub fn kind(&self) -> SortKind {
        unsafe {
            Z3_get_sort_kind(self.ctx.z3_ctx, self.z3_sort)
        }
    }
}

impl<'ctx> fmt::Display for Sort<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p =
            unsafe { CStr::from_ptr(Z3_sort_to_string(self.ctx.z3_ctx, self.z3_sort) as *mut i8) };
        if p.as_ptr().is_null() {
            return Result::Err(fmt::Error);
        }
        match p.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> PartialEq<Sort<'ctx>> for Sort<'ctx> {
    fn eq(&self, other: &Sort<'ctx>) -> bool {
        unsafe { Z3_is_eq_sort(self.ctx.z3_ctx, self.z3_sort, other.z3_sort) }
    }
}

impl<'ctx> Eq for Sort<'ctx> {}

impl<'ctx> Drop for Sort<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_sort_to_ast(self.ctx.z3_ctx, self.z3_sort),
            );
        }
    }
}
