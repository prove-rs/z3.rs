use z3_sys::*;
use Config;
use Context;
use Z3_MUTEX;
use crate::ast::Ast;
use crate::Solver;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;


impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let guard = Z3_MUTEX.lock().unwrap();
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                Z3_set_error_handler(p, None);
                p
            },
            moved: AtomicBool::new(false),
        }
    }

    pub unsafe fn from_raw(z3_ctx: *mut z3_sys::_Z3_context) -> Context {
        Context {
            z3_ctx,
            moved: AtomicBool::new(false),
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    ///
    /// This method can be invoked from a thread different from the one executing the
    /// interruptible procedure.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.z3_ctx);
        }
    }

    pub unsafe fn prepare_move<'ctx>(&self, asts: Option<&mut [&mut impl Ast<'ctx>]>, solvers: Option<&mut [&mut Solver<'ctx>]>) -> SendableContext {
        let mut raw_asts = vec![];
        let mut raw_solvers = vec![];

        if let Some(asts) = asts {
            for ast in asts.iter_mut() {
                assert!(ast.get_ctx() == self);
                ast.mark_moved();
                raw_asts.push(ast.get_z3_ast())
            }
        }

        if let Some(solvers) = solvers {
            for solver in solvers.iter_mut() {
                assert!(solver.ctx == self);
                solver.mark_moved();
                raw_solvers.push(solver.z3_slv);
            }
        }

        self.moved.store(true, Ordering::SeqCst);
        SendableContext {
            z3_ctx: self.z3_ctx,
            asts: raw_asts,
            solvers: raw_solvers,
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        if self.moved.load(Ordering::SeqCst) {
            unsafe { Z3_del_context(self.z3_ctx) };
        }
    }
}

impl PartialEq for Context {
    fn eq(&self, other: &Self) -> bool {
        self.z3_ctx == other.z3_ctx
    }
}

impl Eq for Context {}

#[derive(Debug)]
pub struct SendableContext {
    pub z3_ctx: Z3_context,
    pub asts: Vec<Z3_ast>,
    pub solvers: Vec<Z3_solver>,
}

unsafe impl Send for SendableContext {}
