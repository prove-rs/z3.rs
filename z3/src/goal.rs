use std::ffi::CStr;
use std::fmt;

use z3_sys::*;

use crate::ast;
use crate::ast::Ast;
use Context;
use Goal;
use Z3_MUTEX;

impl<'ctx> Clone for Goal<'ctx> {
    fn clone(&self) -> Self {
        Self {
            ctx: self.ctx,
            z3_goal: self.z3_goal,
        }
    }
}

impl<'ctx> Goal<'ctx> {
    pub fn new(ctx: &'ctx Context, models: bool, unsat_cores: bool, proofs: bool) -> Goal<'ctx> {
        // NOTE: The Z3 context ctx must have been created with proof generation support.
        Self {
            ctx,
            z3_goal: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let g = Z3_mk_goal(ctx.z3_ctx, models, unsat_cores, proofs);
                Z3_goal_inc_ref(ctx.z3_ctx, g);
                g
            },
        }
    }

    /// Add a new formula `a` to the given goal.
    pub fn assert(&self, ast: &impl ast::Ast<'ctx>) {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_assert(self.ctx.z3_ctx, self.z3_goal, ast.get_z3_ast())
        }
    }

    /// Return true if the given goal contains the formula `false`.
    pub fn is_inconsistent(&self) -> bool {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_inconsistent(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the depth of the given goal. It tracks how many transformations were applied to it.
    pub fn get_depth(&self) -> u32 {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_depth(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the number of formulas in the given goal.
    pub fn get_size(&self) -> u32 {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_size(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the number of formulas, subformulas and terms in the given goal.
    pub fn get_num_expr(&self) -> u32 {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_num_exprs(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return true if the goal is empty, and it is precise or the product of a under approximation.
    pub fn is_decided_sat(&self) -> bool {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_is_decided_sat(self.ctx.z3_ctx, self.z3_goal)
        }
    }
    /// Return true if the goal contains false, and it is precise or the product of an over approximation.
    pub fn is_decided_unsat(&self) -> bool {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_is_decided_unsat(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Erase all formulas from the given goal.
    pub fn reset(&self) {
        unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_goal_reset(self.ctx.z3_ctx, self.z3_goal)
        };
    }

    /// Copy a goal `g` from the context `source` to the context `target`.
    pub fn translate<'dest_ctx>(self, ctx: &'dest_ctx Context) -> Goal<'dest_ctx> {
        Goal {
            ctx,
            z3_goal: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let g = Z3_goal_translate(self.ctx.z3_ctx, self.z3_goal, ctx.z3_ctx);
                Z3_goal_inc_ref(ctx.z3_ctx, g);
                g
            },
        }
    }

    /// Return the "precision" of the given goal. Goals can be transformed using over and under approximations.
    pub fn get_precision(&self) -> GoalPrec {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_goal_precision(self.ctx.z3_ctx, self.z3_goal) }
    }

    pub fn iter_formulas<'a, T>(&'a self) -> impl Iterator<Item = T> + 'a
    where
        T: Ast<'a>,
    {
        let goal_size = self.get_size() as usize;
        let z3_ctx = self.ctx.z3_ctx;
        let z3_goal = self.z3_goal;
        (0..goal_size).into_iter().map(move |i| {
            let formula = unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                Z3_goal_formula(z3_ctx, z3_goal, i as u32)
            };
            unsafe { T::new(self.ctx, formula) }
        })
    }

    /// Return a vector of the formulas from the given goal.
    pub fn get_formulas<T>(&self) -> Vec<T>
    where
        T: Ast<'ctx>,
    {
        let goal_size = self.get_size() as usize;
        let mut formulas: Vec<T> = Vec::with_capacity(goal_size);

        for i in 0..goal_size {
            let formula = unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                Z3_goal_formula(self.ctx.z3_ctx, self.z3_goal, i as u32)
            };
            formulas.push(unsafe { T::new(self.ctx, formula) });
        }
        formulas
    }
}

impl<'ctx> fmt::Display for Goal<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_goal_to_string(self.ctx.z3_ctx, self.z3_goal) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Goal<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Goal<'ctx> {
    fn drop(&mut self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_goal_dec_ref(self.ctx.z3_ctx, self.z3_goal);
        };
    }
}
