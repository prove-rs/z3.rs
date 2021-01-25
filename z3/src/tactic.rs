use std::ffi::{CStr, CString};
use std::fmt;

use z3_sys::*;
use Context;
use Goal;
use Params;
use Tactic;
use Z3_MUTEX;

impl<'ctx> Tactic<'ctx> {
    pub fn list_all(ctx: &'ctx Context) {
        let p = unsafe {
            Z3_get_num_tactics(ctx.z3_ctx)
        };
        for n in 0..p {
            let t = unsafe {
                Z3_get_tactic_name(ctx.z3_ctx, n)
            };
            match unsafe { CStr::from_ptr(t) }.to_str() {
                Ok(s) => println!("{}", s),
                Err(_) => (),
            }
        }
    }

    fn new_from_z3(ctx: &'ctx Context, z3_tactic: Z3_tactic) -> Tactic<'ctx> {
        Tactic {
            ctx,
            z3_tactic,
        }
    }

    pub fn new(ctx: &'ctx Context, name: &'ctx str) -> Tactic<'ctx> {
        let tactic_name = CString::new(name).unwrap();
        Tactic {
            ctx,
            z3_tactic: unsafe {
                let t = Z3_mk_tactic(ctx.z3_ctx, tactic_name.as_ptr());
                Z3_tactic_inc_ref(ctx.z3_ctx, t);
                t
            },
        }
    }

    /// Return a tactic that just return the given goal.
    pub fn create_skip(ctx: &'ctx Context) -> Tactic<'ctx> {
        Tactic::new_from_z3(ctx, unsafe {
            let t = Z3_tactic_skip(ctx.z3_ctx);
            Z3_tactic_inc_ref(ctx.z3_ctx, t);
            t
        })
    }

    /// Return a tactic that always fails.
    pub fn create_fail(ctx: &'ctx Context) -> Tactic<'ctx> {
        Tactic::new_from_z3(ctx, unsafe {
            let t = Z3_tactic_fail(ctx.z3_ctx);
            Z3_tactic_inc_ref(ctx.z3_ctx, t);
            t
        })
    }

    /// Return a tactic that keeps applying `t` until the goal is not modified anymore or the maximum
    /// number of iterations `max` is reached.
    pub fn repeat(ctx: &'ctx Context, t: Tactic, max: u32) -> Tactic<'ctx> {
        Tactic {
            ctx,
            z3_tactic: unsafe {
                let t = Z3_tactic_repeat(ctx.z3_ctx, t.z3_tactic, max);
                Z3_tactic_inc_ref(ctx.z3_ctx, t);
                t
            },
        }
    }

    /// Return a tactic that applies the current tactic to a given goal and
    /// the `then_tactic` to every subgoal produced by the original tactic.
    pub fn and_then(&self, then_tactic: Tactic) -> Tactic {
        let t = unsafe {
            let t = Z3_tactic_and_then(self.ctx.z3_ctx, self.z3_tactic, then_tactic.z3_tactic);
            Z3_tactic_inc_ref(self.ctx.z3_ctx, t);
            t
        };
        Tactic {
            ctx: self.ctx,
            z3_tactic: t,
        }
    }

    /// Return a tactic that current tactic to a given goal,
    /// if it fails then returns the result of `else_tactic` applied to the given goal.
    pub fn or_else(&self, else_tactic: Tactic) -> Tactic {
        let t = unsafe {
            let t = Z3_tactic_or_else(self.ctx.z3_ctx, self.z3_tactic, else_tactic.z3_tactic);
            Z3_tactic_inc_ref(self.ctx.z3_ctx, t);
            t
        };
        Tactic {
            ctx: self.ctx,
            z3_tactic: t,
        }
    }

    pub fn apply(self, goal: &Goal, params: &Params) -> Goal<'ctx> {
        let result = unsafe {
            Z3_tactic_apply(
                self.ctx.z3_ctx,
                self.z3_tactic,
                goal.z3_goal,
            )
        };
        unsafe {
            Z3_apply_result_inc_ref(self.ctx.z3_ctx, result);
            if Z3_apply_result_get_num_subgoals(self.ctx.z3_ctx, result) == 1 {
                let sg = Z3_apply_result_get_subgoal(self.ctx.z3_ctx, result, 0);
                Z3_goal_inc_ref(self.ctx.z3_ctx, sg);
                return Goal::new_from_z3_type(self.ctx, sg)
            } else {
                panic!("Invalid Goal")
            }
        }
    }
}

impl<'ctx> fmt::Display for Tactic<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_tactic_get_help(self.ctx.z3_ctx, self.z3_tactic) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Tactic<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Tactic<'ctx> {
    fn drop(&mut self) {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_tactic_dec_ref(self.ctx.z3_ctx, self.z3_tactic);
        }
    }
}
