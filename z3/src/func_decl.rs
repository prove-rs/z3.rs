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
                Z3_mk_func_decl(
                    ctx.z3_ctx,
                    name.z3_sym,
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                )
            },
        }
    }

    pub fn apply(&self, args: &[&Ast<'ctx>]) -> Ast<'ctx> {
        assert!(args.iter().all(|s| s.ctx.z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.z3_ast).collect();

        Ast {
            ctx: self.ctx,
            z3_ast: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            },
        }
    }
}
