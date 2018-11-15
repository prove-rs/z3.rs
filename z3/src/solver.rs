use std::ffi::CString;
use std::fmt;
use z3_sys::*;
use Ast;
use Context;
use Model;
use Solver;
use Z3_MUTEX;

impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &Context) -> Solver {
        Solver {
            ctx,
            z3_slv: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let s = Z3_mk_solver(ctx.z3_ctx);
                Z3_solver_inc_ref(ctx.z3_ctx, s);
                s
            },
        }
    }

    pub fn assert(&self, ast: &Ast<'ctx>) {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_assert(self.ctx.z3_ctx, self.z3_slv, ast.z3_ast);
        }
    }

    pub fn check(&self) -> bool {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_check(self.ctx.z3_ctx, self.z3_slv) == Z3_L_TRUE
        }
    }

    pub fn get_model(&self) -> Model<'ctx> {
        Model::of_solver(self)
    }
}

impl<'ctx> fmt::Display for Solver<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe {
            CString::from_raw(Z3_solver_to_string(self.ctx.z3_ctx, self.z3_slv) as *mut i8)
        };
        if p.as_ptr().is_null() {
            return Result::Err(fmt::Error);
        }
        match p.into_string() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => return Result::Err(fmt::Error),
        }
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
