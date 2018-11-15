use z3_sys::*;
use Ast;
use Model;
use Optimize;
use Solver;
use Z3_MUTEX;

impl<'ctx> Model<'ctx> {
    pub fn of_solver(slv: &Solver<'ctx>) -> Model<'ctx> {
        Model {
            ctx: slv.ctx,
            z3_mdl: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let m = Z3_solver_get_model(slv.ctx.z3_ctx, slv.z3_slv);
                Z3_model_inc_ref(slv.ctx.z3_ctx, m);
                m
            },
        }
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Model<'ctx> {
        Model {
            ctx: opt.ctx,
            z3_mdl: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let m = Z3_optimize_get_model(opt.ctx.z3_ctx, opt.z3_opt);
                Z3_model_inc_ref(opt.ctx.z3_ctx, m);
                m
            },
        }
    }

    pub fn eval(&self, ast: &Ast<'ctx>) -> Option<Ast<'ctx>> {
        unsafe {
            let mut tmp: Z3_ast = ast.z3_ast;
            let res;
            {
                let guard = Z3_MUTEX.lock().unwrap();
                res = Z3_model_eval(self.ctx.z3_ctx, self.z3_mdl, ast.z3_ast, Z3_TRUE, &mut tmp)
            }
            if res == Z3_TRUE {
                Some(Ast::new(self.ctx, tmp))
            } else {
                None
            }
        }
    }
}

impl<'ctx> Drop for Model<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_model_dec_ref(self.ctx.z3_ctx, self.z3_mdl);
        }
    }
}
