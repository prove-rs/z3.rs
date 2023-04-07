use std::ffi::CStr;
use std::fmt;
use std::str::Utf8Error;
use z3_sys::*;
use Context;
use ParamDescrs;
use Solver;
use Symbol;
use Tactic;
use Z3_MUTEX;

impl<'ctx> ParamDescrs<'ctx> {
    fn new_from_z3_type(ctx: &'ctx Context, z3_param_descrs: Z3_param_descrs) -> ParamDescrs<'ctx> {
        ParamDescrs {
            ctx,
            z3_param_descrs,
        }
    }

    pub fn from_tactic(tactic: &'ctx Tactic<'ctx>) -> ParamDescrs<'ctx> {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let ctx = tactic.ctx;
            let z3_param_descrs = Z3_tactic_get_param_descrs(ctx.z3_ctx, tactic.z3_tactic);
            let pd = ParamDescrs::new_from_z3_type(ctx, z3_param_descrs);
            Z3_param_descrs_inc_ref(ctx.z3_ctx, z3_param_descrs);
            pd
        }
    }

    pub fn from_solver(solver: &'ctx Solver<'ctx>) -> ParamDescrs<'ctx> {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let ctx = solver.ctx;
            let z3_param_descrs = Z3_solver_get_param_descrs(ctx.z3_ctx, solver.z3_slv);
            let pd = ParamDescrs::new_from_z3_type(ctx, z3_param_descrs);
            Z3_param_descrs_inc_ref(ctx.z3_ctx, z3_param_descrs);
            pd
        }
    }

    pub fn get_size(&self) -> u32 {
        unsafe { Z3_param_descrs_size(self.ctx.z3_ctx, self.z3_param_descrs) }
    }

    pub fn get_param_kind<N: Into<Symbol>>(&self, n: N) -> ParamKind {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_param_descrs_get_kind(
                self.ctx.z3_ctx,
                self.z3_param_descrs,
                n.into().as_z3_symbol(self.ctx),
            )
        }
    }

    pub fn get_param_name(&self, index: u32) -> Option<Symbol> {
        let n = {
            let _guard = Z3_MUTEX.lock().unwrap();
            let p = self.get_size();
            if index > p {
                return None;
            }
            unsafe { Z3_param_descrs_get_name(self.ctx.z3_ctx, self.z3_param_descrs, index) }
        };
        Symbol::new_from_z3_symbol(self.ctx, n)
    }

    pub fn get_param_documentation<N: Into<Symbol> + Clone>(&'ctx self, n: N) -> Option<&'ctx str> {
        if let ParamKind::Invalid = self.get_param_kind(n.clone()) {
            return None;
        }
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            let d = Z3_param_descrs_get_documentation(
                self.ctx.z3_ctx,
                self.z3_param_descrs,
                n.into().as_z3_symbol(self.ctx),
            );
            if d.is_null() {
                None
            } else {
                CStr::from_ptr(d).to_str().ok()
            }
        }
    }
}

impl<'ctx> fmt::Display for ParamDescrs<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_param_descrs_to_string(self.ctx.z3_ctx, self.z3_param_descrs) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for ParamDescrs<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for ParamDescrs<'ctx> {
    fn drop(&mut self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_param_descrs_dec_ref(self.ctx.z3_ctx, self.z3_param_descrs);
        }
    }
}
