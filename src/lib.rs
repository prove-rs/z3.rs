#![allow(dead_code)]
#![allow(unused_variables)]

#[macro_use]
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate lazy_static;

extern crate z3_sys;
extern crate libc;

use std::sync::Mutex;
use std::ffi::CString;
use z3_sys::*;

// Despite warm assurances from the Z3 documentation, it appears
// that Z3 does not like multiple threads making calls on it at
// the same time. Memory corruption galore during initializations.
// So we mutex-guard all accesses.
lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

pub struct Config {
    kvs: Vec<(CString,CString)>,
    z3_cfg: Z3_config
}

pub struct Context {
    z3_ctx: Z3_context
}

pub struct Symbol<'ctx>
{
    ctx: &'ctx Context,
    cst: Option<CString>,
    z3_sym: Z3_symbol
}

pub struct Sort<'ctx>
{
    ctx: &'ctx Context,
    z3_sort: Z3_sort
}

pub struct Ast<'ctx>
{
    ctx: &'ctx Context,
    z3_ast: Z3_ast
}

pub struct Solver<'ctx>
{
    ctx: &'ctx Context,
    z3_slv: Z3_solver
}

pub struct Model<'ctx>
{
    ctx: &'ctx Context,
    z3_mdl: Z3_model
}

impl Config {
    pub fn new() -> Config {
        Config {
            kvs: Vec::new(),
            z3_cfg: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_config();
                debug!("new config {:p}", p);
                p
            }
        }
    }
    pub fn set_param_value(&mut self, k: &str, v: &str) {
        let ks = CString::new(k).unwrap();
        let vs = CString::new(v).unwrap();
        self.kvs.push((ks, vs));
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_set_param_value(self.z3_cfg,
                               self.kvs.last().unwrap().0.as_ptr(),
                               self.kvs.last().unwrap().1.as_ptr());
        }
    }

    pub fn set_bool_param_value(&mut self, k: &str, v: bool) {
        self.set_param_value(k, if v { "true" } else { "false" });
    }

    // Helpers for common parameters
    pub fn set_proof_generation(&mut self, b: bool)
    {
        self.set_bool_param_value("proof", b);
    }

    pub fn set_model_generation(&mut self, b: bool)
    {
        self.set_bool_param_value("model", b);
    }

    pub fn set_debug_ref_count(&mut self, b: bool)
    {
        self.set_bool_param_value("debug_ref_count", b);
    }

    pub fn set_timeout_msec(&mut self, ms: u64)
    {
        self.set_param_value("timeout", &format!("{}", ms));
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        unsafe {
            debug!("drop config {:p}", self.z3_cfg);
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_del_config(self.z3_cfg);
        }
    }
}

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                p
            }
        }
    }

    // Helpers for common constructions
    pub fn int_sym(&self, i: u32) -> Symbol {
        Symbol::from_int(self, i)
    }

    pub fn str_sym(&self, s: &str) -> Symbol {
        Symbol::from_string(self, s)
    }

    pub fn bool_sort(&self) -> Sort {
        Sort::bool(self)
    }

    pub fn int_sort(&self) -> Sort {
        Sort::int(self)
    }

    pub fn real_sort(&self) -> Sort {
        Sort::real(self)
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            debug!("drop context {:p}", self.z3_ctx);
            Z3_del_context(self.z3_ctx);
        }
    }
}

impl<'ctx> Symbol<'ctx> {
    pub fn from_int(ctx: &Context, i: u32) -> Symbol {
        Symbol {
            ctx: ctx,
            cst: None,
            z3_sym: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_int_symbol(ctx.z3_ctx, i as ::libc::c_int)
            }
        }
    }

    pub fn from_string(ctx: &'ctx Context, s: &str) -> Symbol<'ctx> {
        let ss = CString::new(s).unwrap();
        let p = ss.as_ptr();
        Symbol {
            ctx: ctx,
            cst: Some(ss),
            z3_sym: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_string_symbol(ctx.z3_ctx, p)
            }
        }
    }
}

impl<'ctx> Sort<'ctx> {

    pub fn uninterpretd(ctx: &'ctx Context, sym: &Symbol<'ctx>) -> Sort<'ctx> {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_uninterpreted_sort(ctx.z3_ctx, sym.z3_sym)
            }
        }
    }

    pub fn bool(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bool_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn int(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_int_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn real(ctx: &Context) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_real_sort(ctx.z3_ctx)
            }
        }
    }

    pub fn bitvector(ctx: &Context, sz: u32) -> Sort {
        Sort {
            ctx: ctx,
            z3_sort: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_bv_sort(ctx.z3_ctx, sz as ::libc::c_uint)
            }
        }
    }
}

impl<'ctx> Ast<'ctx> {
    fn new(ctx: &Context, ast: Z3_ast) -> Ast {
        Ast {
            ctx: ctx,
            z3_ast: unsafe {
                debug!("new ast {:p}", ast);
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_inc_ref(ctx.z3_ctx, ast);
                ast
            }
        }
    }
    pub fn new_const(sym: &Symbol<'ctx>,
                     sort: &Sort<'ctx>) -> Ast<'ctx> {
        Ast::new(sym.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_const(sym.ctx.z3_ctx, sym.z3_sym, sort.z3_sort)
        })
    }

    pub fn new_gt(a: &Ast<'ctx>, b: &Ast<'ctx>) -> Ast<'ctx> {
        Ast::new(a.ctx, unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_mk_gt(a.ctx.z3_ctx, a.z3_ast, b.z3_ast)
        })
    }

    pub fn as_int64(&self) -> Option<i64> {
        unsafe {
            let guard = Z3_MUTEX.lock().unwrap();
            let mut tmp : ::libc::c_longlong = 0;
            if Z3_TRUE == Z3_get_numeral_int64(self.ctx.z3_ctx,
                                               self.z3_ast, &mut tmp) {
                Some(tmp)
            } else {
                None
            }
        }
    }
}



impl<'ctx> Drop for Ast<'ctx> {
    fn drop(&mut self) {
        unsafe {
            debug!("drop ast {:p}", self.z3_ast);
            let guard = Z3_MUTEX.lock().unwrap();
            Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast);
        }
    }
}


impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &Context) -> Solver {
        Solver {
            ctx: ctx,
            z3_slv: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_mk_solver(ctx.z3_ctx)
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

}

impl<'ctx> Model<'ctx> {
    pub fn new(slv: &Solver<'ctx>) -> Model<'ctx> {
        Model {
            ctx: slv.ctx,
            z3_mdl: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                Z3_solver_get_model(slv.ctx.z3_ctx, slv.z3_slv)
            }
        }
    }

    pub fn eval(&self, ast: &Ast<'ctx>) -> Option<Ast<'ctx>> {
        unsafe {
            let mut tmp : Z3_ast = ast.z3_ast;
            let res;
            {
                let guard = Z3_MUTEX.lock().unwrap();
                res = Z3_model_eval(self.ctx.z3_ctx,
                                    self.z3_mdl,
                                    ast.z3_ast,
                                    Z3_TRUE,
                                    &mut tmp)
            }
            if res == Z3_TRUE {
                Some(Ast::new(self.ctx, tmp))
            } else {
                None
            }
        }
    }
}

