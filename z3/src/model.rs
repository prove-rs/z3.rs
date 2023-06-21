use ast::Ast;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Optimize;
use Solver;

use crate::{FuncDecl, FuncInterp};

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

    /// Returns the interpretation of the given `ast` in the `Model`
    /// Returns `None` if there is no interpretation in the `Model`
    pub fn get_const_interp<T: Ast<'ctx>>(&self, ast: &T) -> Option<T> {
        let func = ast.safe_decl().ok()?;

        let ret =
            unsafe { Z3_model_get_const_interp(self.ctx.z3_ctx, self.z3_mdl, func.z3_func_decl) };
        if ret.is_null() {
            None
        } else {
            Some(unsafe { T::wrap(self.ctx, ret) })
        }
    }

    /// Returns the interpretation of the given `f` in the `Model`
    /// Returns `None` if there is no interpretation in the `Model`
    pub fn get_func_interp(&self, f: &FuncDecl) -> Option<FuncInterp<'ctx>> {
        if f.arity() == 0 {
            let ret =
                unsafe { Z3_model_get_const_interp(self.ctx.z3_ctx, self.z3_mdl, f.z3_func_decl) };
            if ret.is_null() {
                None
            } else {
                let sort_kind = unsafe {
                    Z3_get_sort_kind(
                        self.ctx.z3_ctx,
                        Z3_get_range(self.ctx.z3_ctx, f.z3_func_decl),
                    )
                };
                match sort_kind {
                    SortKind::Array => {
                        if unsafe { Z3_is_as_array(self.ctx.z3_ctx, ret) } {
                            let fd = unsafe {
                                FuncDecl::wrap(
                                    self.ctx,
                                    Z3_get_as_array_func_decl(self.ctx.z3_ctx, ret),
                                )
                            };
                            self.get_func_interp(&fd)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
        } else {
            let ret =
                unsafe { Z3_model_get_func_interp(self.ctx.z3_ctx, self.z3_mdl, f.z3_func_decl) };
            if ret.is_null() {
                None
            } else {
                Some(unsafe { FuncInterp::wrap(self.ctx, ret) })
            }
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
            Some(unsafe { T::wrap(self.ctx, tmp) })
        } else {
            None
        }
    }

    fn len(&self) -> u32 {
        unsafe {
            Z3_model_get_num_consts(self.ctx.z3_ctx, self.z3_mdl)
                + Z3_model_get_num_funcs(self.ctx.z3_ctx, self.z3_mdl)
        }
    }

    pub fn iter(&'ctx self) -> ModelIter<'ctx> {
        self.into_iter()
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

#[derive(Debug)]
/// https://z3prover.github.io/api/html/classz3py_1_1_model_ref.html#a7890b7c9bc70cf2a26a343c22d2c8367
pub struct ModelIter<'ctx> {
    model: &'ctx Model<'ctx>,
    idx: u32,
    len: u32,
}

impl<'ctx> IntoIterator for &'ctx Model<'ctx> {
    type Item = FuncDecl<'ctx>;
    type IntoIter = ModelIter<'ctx>;

    fn into_iter(self) -> Self::IntoIter {
        ModelIter {
            model: self,
            idx: 0,
            len: self.len(),
        }
    }
}

impl<'ctx> Iterator for ModelIter<'ctx> {
    type Item = FuncDecl<'ctx>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.len {
            None
        } else {
            let num_consts =
                unsafe { Z3_model_get_num_consts(self.model.ctx.z3_ctx, self.model.z3_mdl) };
            if self.idx < num_consts {
                let const_decl = unsafe {
                    Z3_model_get_const_decl(self.model.ctx.z3_ctx, self.model.z3_mdl, self.idx)
                };
                self.idx += 1;
                Some(unsafe { FuncDecl::wrap(self.model.ctx, const_decl) })
            } else {
                let func_decl = unsafe {
                    Z3_model_get_func_decl(
                        self.model.ctx.z3_ctx,
                        self.model.z3_mdl,
                        self.idx - num_consts,
                    )
                };
                self.idx += 1;
                Some(unsafe { FuncDecl::wrap(self.model.ctx, func_decl) })
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.len - self.idx) as usize;
        (len, Some(len))
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
