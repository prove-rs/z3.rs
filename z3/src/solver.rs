use z3_sys::*;
use Context;
use Solver;
use Model;
use Ast;
use Z3_MUTEX;

impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &Context) -> Solver {
        Solver {
            ctx: ctx,
            z3_slv: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let s = Z3_mk_solver(ctx.z3_ctx);
                Z3_solver_inc_ref(ctx.z3_ctx, s);
                s
            }
        }
    }

    pub fn assert(&self, ast: &Ast<'ctx>) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_assert(self.ctx.z3_ctx,
                             self.z3_slv,
                             ast.z3_ast);
        }
    }

    pub fn check(&self) -> bool {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_check(self.ctx.z3_ctx,
                            self.z3_slv) == Z3_TRUE
        }
    }

    pub fn get_model(&self) -> Model<'ctx> {
        Model::of_solver(self)
    }
}


impl<'ctx> Drop for Solver<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_slv);
        }
    }
}
