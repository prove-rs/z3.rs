use std::ffi::CStr;
use std::fmt;

use z3_sys::*;

use crate::ast;
use crate::ast::Ast;
use Context;
use Goal;
use Z3_MUTEX;

impl<'ctx> Goal<'ctx> {
    pub fn new_from_z3_type(ctx: &'ctx Context, z3_goal: Z3_goal) -> Goal<'ctx>{
        Goal {
            ctx,
            z3_goal: z3_goal,
        }
    }

    pub fn new(ctx: &'ctx Context, models: bool, unsat_cores: bool, proofs: bool) -> Goal<'ctx> {
        let goal = Self {
            ctx,
            z3_goal: unsafe {
                let g = Z3_mk_goal(ctx.z3_ctx, models, unsat_cores, proofs);
                Z3_goal_inc_ref(ctx.z3_ctx, g);
                g
            }
        };
        goal
    }

    /// Add a new formula `a` to the given goal.
    pub fn assert(&self, ast: &impl ast::Ast<'ctx>) {
        unsafe {
            Z3_goal_assert(self.ctx.z3_ctx, self.z3_goal, ast.get_z3_ast())
        }
    }

    /// Return true if the given goal contains the formula `false`.
    pub fn is_inconsistent(&self) -> bool {
        unsafe {
            Z3_goal_inconsistent(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the depth of the given goal. It tracks how many transformations were applied to it.
    pub fn get_depth(&self) -> u32 {
        unsafe {
            Z3_goal_depth(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the number of formulas in the given goal.
    pub fn get_size(&self) -> u32 {
        unsafe {
            Z3_goal_size(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return the number of formulas, subformulas and terms in the given goal.
    pub fn get_num_expr(&self) -> u32 {
        unsafe {
            Z3_goal_num_exprs(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Return true if the goal is empty, and it is precise or the product of a under approximation.
    pub fn is_decided_sat(&self) -> bool {
        unsafe {
            Z3_goal_is_decided_sat(self.ctx.z3_ctx, self.z3_goal)
        }
    }
    /// Return true if the goal contains false, and it is precise or the product of an over approximation.
    pub fn is_decided_unsat(&self) -> bool {
        unsafe {
            Z3_goal_is_decided_unsat(self.ctx.z3_ctx, self.z3_goal)
        }
    }

    /// Erase all formulas from the given goal.
    pub fn reset(&self) {
        unsafe {
            Z3_goal_reset(self.ctx.z3_ctx, self.z3_goal)
        };
    }

    /// Copy a goal `g` from the context `source` to the context `target`.
    pub fn translate<'dest_ctx>(self, ctx: &'dest_ctx Context) -> Goal<'dest_ctx> {
        Goal {
            ctx,
            z3_goal: unsafe {
                Z3_goal_translate(self.ctx.z3_ctx, self.z3_goal, ctx.z3_ctx)
            }
        }
    }

    /// Return the "precision" of the given goal. Goals can be transformed using over and under approximations.
    pub fn get_precision(&self) -> String {
        match unsafe {
            Z3_goal_precision(self.ctx.z3_ctx, self.z3_goal)
        } {
            GoalPrec::Precise => "PRECISE".to_string(),
            GoalPrec::Under => "UNDER".to_string(),
            GoalPrec::Over => "OVER".to_string(),
            GoalPrec::UnderOver => "UNDEROVER".to_string(),
        }
    }

    /// Return a vector of the formulas from the given goal.
    pub fn get_formulas<T>(&self) -> Vec<T> where T: Ast<'ctx> {
        let goal_size = self.get_size();
        let formula = unsafe {
            Z3_goal_formula(self.ctx.z3_ctx, self.z3_goal, 0)
        };
        let mut formulas = vec![T::new(&self.ctx, formula)];

        for i in 1..goal_size {
            let formula = unsafe {
                Z3_goal_formula(self.ctx.z3_ctx, self.z3_goal, i)
            };
            formulas.push(T::new(&self.ctx, formula));
        };
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
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_goal_dec_ref(self.ctx.z3_ctx, self.z3_goal);
        };
    }
}
