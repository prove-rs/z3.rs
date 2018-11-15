use z3_sys::*;
use Ast;
use Context;
use Model;
use Optimize;
use Z3_MUTEX;

impl<'ctx> Optimize<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Optimize<'ctx> {
        Optimize {
            ctx,
            z3_opt: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let opt = Z3_mk_optimize(ctx.z3_ctx);
                Z3_optimize_inc_ref(ctx.z3_ctx, opt);
                opt
            },
        }
    }

    pub fn assert(&self, ast: &Ast<'ctx>) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_optimize_assert(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast);
        }
    }

    pub fn maximize(&self, ast: &Ast<'ctx>) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_optimize_maximize(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast);
        }
    }

    pub fn minimize(&self, ast: &Ast<'ctx>) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_optimize_minimize(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast);
        }
    }

    pub fn check(&self) -> bool {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_optimize_check(self.ctx.z3_ctx, self.z3_opt) == Z3_L_TRUE
        }
    }

    pub fn get_model(&self) -> Model<'ctx> {
        Model::of_optimize(self)
    }
}

impl<'ctx> Drop for Optimize<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_optimize_dec_ref(self.ctx.z3_ctx, self.z3_opt);
        }
    }
}
