use std::ffi::CString;
use std::fmt;
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
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_assert(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast) };
    }

    pub fn maximize(&self, ast: &Ast<'ctx>) {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_maximize(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast) };
    }

    pub fn minimize(&self, ast: &Ast<'ctx>) {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_minimize(self.ctx.z3_ctx, self.z3_opt, ast.z3_ast) };
    }

    pub fn check(&self) -> bool {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_check(self.ctx.z3_ctx, self.z3_opt) == Z3_L_TRUE }
    }

    pub fn get_model(&self) -> Model<'ctx> {
        Model::of_optimize(self)
    }
}

impl<'ctx> fmt::Display for Optimize<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe {
            CString::from_raw(Z3_optimize_to_string(self.ctx.z3_ctx, self.z3_opt) as *mut i8)
        };
        if p.as_ptr().is_null() {
            return Result::Err(fmt::Error);
        }
        match p.into_string() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> Drop for Optimize<'ctx> {
    fn drop(&mut self) {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_dec_ref(self.ctx.z3_ctx, self.z3_opt) };
    }
}
