use std::convert::TryInto;
use z3_sys::*;
use {Ast, Context, FuncDecl, Sort, Symbol, Z3_MUTEX};

impl<'ctx> FuncDecl<'ctx> {
    pub fn new(
        ctx: &'ctx Context,
        name: Symbol<'ctx>,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert_eq!(ctx.z3_ctx, name.ctx.z3_ctx);
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

        Self {
            ctx,
            z3_func_decl: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();

                for d in domain.iter() {
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, *d));
                }
                Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, range.z3_sort));

                let f = Z3_mk_func_decl(
                    ctx.z3_ctx,
                    name.z3_sym,
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                );
                Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, f));
                f
            },
        }
    }

    pub fn apply(&self, args: &[&Ast<'ctx>]) -> Ast<'ctx> {
        assert!(args.iter().all(|s| s.ctx.z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.z3_ast).collect();

        Ast::new(self.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_app(
                self.ctx.z3_ctx,
                self.z3_func_decl,
                args.len().try_into().unwrap(),
                args.as_ptr(),
            )
        })
    }
}

impl<'ctx> std::fmt::Display for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx, self.z3_func_decl) };
        if p.is_null() {
            Err(std::fmt::Error)
        } else {
            let s = unsafe { std::ffi::CStr::from_ptr(p) };
            write!(f, "{:?}", s)
        }
    }
}

impl<'ctx> Drop for FuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl),
            );
        }
    }
}
