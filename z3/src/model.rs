use ast::Ast;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Optimize;
use Solver;

impl<'ctx> Model<'ctx> {
    unsafe fn wrap(ctx: &'ctx Context, z3_mdl: Z3_model) -> Model<'ctx> {
        Z3_model_inc_ref(ctx.z3_ctx, z3_mdl);
        Model { ctx, z3_mdl }
    }

    pub fn of_solver(slv: &Solver<'ctx>) -> Option<Model<'ctx>> {
        unsafe {
            let m = Z3_solver_get_model(slv.ctx.z3_ctx, slv.z3_slv);
            if m.is_null() {
                None
            } else {
                Some(Self::wrap(slv.ctx, m))
            }
        }
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Option<Model<'ctx>> {
        unsafe {
            let m = Z3_optimize_get_model(opt.ctx.z3_ctx, opt.z3_opt);
            if m.is_null() {
                None
            } else {
                Some(Self::wrap(opt.ctx, m))
            }
        }
    }

    /// Translate model to context `dest`
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Model<'dest_ctx> {
        unsafe {
            Model::wrap(
                dest,
                Z3_model_translate(self.ctx.z3_ctx, self.z3_mdl, dest.z3_ctx),
            )
        }
    }

    pub fn eval<T>(&self, ast: &T, model_completion: bool) -> Option<T>
    where
        T: Ast<'ctx>,
    {
        let mut tmp: Z3_ast = ast.get_z3_ast();
        let res = {
            unsafe {
                Z3_model_eval(
                    self.ctx.z3_ctx,
                    self.z3_mdl,
                    ast.get_z3_ast(),
                    model_completion,
                    &mut tmp,
                )
            }
        };
        if res {
            Some(unsafe { T::new(self.ctx, tmp) })
        } else {
            None
        }
    }
}

impl<'ctx> fmt::Display for Model<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_model_to_string(self.ctx.z3_ctx, self.z3_mdl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Model<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Model<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.ctx.z3_ctx, self.z3_mdl) };
    }
}

#[test]
fn test_unsat() {
    use crate::{ast, Config, SatResult};
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.assert(&ast::Bool::from_bool(&ctx, false));
    assert_eq!(solver.check(), SatResult::Unsat);
    assert!(solver.get_model().is_none());
}
