use ast::Ast;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Optimize;
use Solver;

impl<'ctx> Model<'ctx> {
    pub fn of_solver(slv: &Solver<'ctx>) -> Option<Model<'ctx>> {
        Some(Model {
            ctx: slv.ctx,
            z3_mdl: unsafe {
                let m = Z3_solver_get_model(slv.ctx.z3_ctx, slv.z3_slv);
                if m.is_null() {
                    return None;
                }
                Z3_model_inc_ref(slv.ctx.z3_ctx, m);
                m
            },
        })
    }

    pub fn of_optimize(opt: &Optimize<'ctx>) -> Option<Model<'ctx>> {
        Some(Model {
            ctx: opt.ctx,
            z3_mdl: unsafe {
                let m = Z3_optimize_get_model(opt.ctx.z3_ctx, opt.z3_opt);
                if m.is_null() {
                    return None;
                }
                Z3_model_inc_ref(opt.ctx.z3_ctx, m);
                m
            },
        })
    }

    /// Translate model to context `dest`
    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Model<'dest_ctx> {
        Model {
            ctx: dest,
            z3_mdl: unsafe {
                let m = Z3_model_translate(self.ctx.z3_ctx, self.z3_mdl, dest.z3_ctx);
                Z3_model_inc_ref(dest.z3_ctx, m);
                m
            },
        }
    }

    pub fn eval<T>(&self, ast: &T) -> Option<T>
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
                    true,
                    &mut tmp,
                )
            }
        };
        if res {
            Some(T::new(self.ctx, tmp))
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
