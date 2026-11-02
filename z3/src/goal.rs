use core::iter::FusedIterator;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;

use crate::{
    Context, Goal, Model, SatResult, Solvable, Solver, Translate,
    ast::{self, Ast, Bool},
};

impl Clone for Goal {
    fn clone(&self) -> Self {
        unsafe { Self::wrap(&self.ctx, self.z3_goal, self.models) }
    }
}

impl Goal {
    pub(crate) unsafe fn wrap(ctx: &Context, z3_goal: Z3_goal, models: bool) -> Goal {
        unsafe {
            Z3_goal_inc_ref(ctx.z3_ctx.as_ptr(), z3_goal);
        }
        Goal {
            ctx: ctx.clone(),
            z3_goal,
            models,
        }
    }

    /// Create empty `Goal`.
    ///
    /// NOTE: if you intend to iterate over the solutions
    /// ([`Goal::into_solutions`]) of this [`Goal`],
    /// or apply a [`crate::Tactic`] to this [`Goal`]
    /// and then iterate over solutions
    /// ([`crate::Tactic::apply`]+[`crate::ApplyResult::into_solutions`]),
    /// you need to pass `/*models=*/true` here.
    pub fn new(models: bool, unsat_cores: bool, proofs: bool) -> Goal {
        let ctx = &Context::thread_local();
        // NOTE: The Z3 context ctx must have been created with proof generation support.
        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_goal(ctx.z3_ctx.as_ptr(), models, unsat_cores, proofs).unwrap(),
                models,
            )
        }
    }

    /// Add a new formula `a` to the given goal.
    pub fn assert(&self, ast: &impl ast::Ast) {
        unsafe { Z3_goal_assert(self.ctx.z3_ctx.as_ptr(), self.z3_goal, ast.get_z3_ast()) }
    }

    /// Return true if the given goal contains the formula `false`.
    pub fn is_inconsistent(&self) -> bool {
        unsafe { Z3_goal_inconsistent(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    /// Return the depth of the given goal. It tracks how many transformations were applied to it.
    pub fn get_depth(&self) -> u32 {
        unsafe { Z3_goal_depth(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    /// Return the number of formulas in the given goal.
    pub fn get_size(&self) -> u32 {
        unsafe { Z3_goal_size(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    /// Return the number of formulas, subformulas and terms in the given goal.
    pub fn get_num_expr(&self) -> u32 {
        unsafe { Z3_goal_num_exprs(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    /// Return true if the goal is empty, and it is precise or the product of a under approximation.
    pub fn is_decided_sat(&self) -> bool {
        unsafe { Z3_goal_is_decided_sat(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }
    /// Return true if the goal contains false, and it is precise or the product of an over approximation.
    pub fn is_decided_unsat(&self) -> bool {
        unsafe { Z3_goal_is_decided_unsat(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    /// Erase all formulas from the given goal.
    pub fn reset(&self) {
        unsafe { Z3_goal_reset(self.ctx.z3_ctx.as_ptr(), self.z3_goal) };
    }

    /// Return the "precision" of the given goal. Goals can be transformed using over and under approximations.
    pub fn get_precision(&self) -> GoalPrec {
        unsafe { Z3_goal_precision(self.ctx.z3_ctx.as_ptr(), self.z3_goal) }
    }

    pub fn iter_formulas<'a, T>(&'a self) -> impl Iterator<Item = T> + 'a
    where
        T: Ast,
    {
        let goal_size = self.get_size() as usize;
        let z3_ctx = self.ctx.z3_ctx.as_ptr();
        let z3_goal = self.z3_goal;
        (0..goal_size).map(move |i| {
            let formula = unsafe { Z3_goal_formula(z3_ctx, z3_goal, i as u32).unwrap() };
            unsafe { T::wrap(&self.ctx, formula) }
        })
    }

    /// Return a vector of the formulas from the given goal.
    ///
    /// Though not guaranteed by Z3's type system, goals and subgoals are
    /// conceptually always going to be expressions of the [`Bool`] Sort.
    pub fn get_formulas(&self) -> Vec<Bool> {
        let goal_size = self.get_size() as usize;
        let mut formulas: Vec<Bool> = Vec::with_capacity(goal_size);

        for i in 0..goal_size {
            let formula = unsafe {
                Z3_goal_formula(self.ctx.z3_ctx.as_ptr(), self.z3_goal, i as u32).unwrap()
            };
            formulas.push(unsafe { Bool::wrap(&self.ctx, formula) });
        }
        formulas
    }

    /// Convert a model of the formulas of a goal to a model of an original goal.
    /// The model may be null, in which case the returned model is valid
    /// if the goal was established satisfiable.
    ///
    /// # NOTE:
    /// Only the `Goal`s constructed with model generation enabled
    /// can perform model conversion.
    /// (pass `/*models=*/true` into the initial [`Goal::new`] call.)
    ///
    /// When using this feature it is advisable to set the parameter `model`.compact to `false`.
    /// It is by default true, which erases variables created by the solver from models.
    /// Without access to model values for intermediary variables, values of other variables
    /// may end up having the wrong values.
    pub fn convert_model(&self, model: Model) -> Model {
        assert!(
            self.models,
            "Model conversion is only available for the `Goal`s that were constructed with model generation enabled.\nTIP: pass `/*models=*/true` into the initial `Goal::new()`."
        );
        unsafe {
            Model::wrap(
                &self.ctx,
                Z3_goal_convert_model(self.ctx.z3_ctx.as_ptr(), self.z3_goal, model.z3_mdl)
                    .unwrap(),
            )
        }
    }

    /// Consume this [`Goal`] and [`Solver`] and iterate over solutions to the given [`Solvable`].
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::{Goal, Solver, Tactic};
    /// # use z3::ast::*;
    ///  let g = Goal::new(/*models=*/true, false, false);
    ///  let a = Int::new_const("a");
    ///  let b = Int::new_const("b");
    ///  g.assert(&Bool::and(&[
    ///      Bool::or(&[a.eq(0), a.eq(1)]),
    ///      b.ge(0),
    ///      b.le(1),
    ///  ]));
    ///  let subgoals = Tactic::new("split-clause")
    ///      .and_then(&Tactic::new("solve-eqs"))
    ///      .apply(&g, None).unwrap();
    ///  assert_eq!(subgoals.num_subgoals(), 2);
    ///  let c = Int::new_const("c");
    ///  let s = Tactic::new("smt").solver();
    ///  s.assert(&c.ge(0x0));
    ///  s.assert(&c.le(0x1));
    ///  let mut solutions = subgoals
    ///      .into_solutions(s, [a, b, c], false)
    ///      .map(|r| r.iter().map(|e| e.as_i64().unwrap()).collect::<Vec<_>>())
    ///      .collect::<Vec<_>>();
    ///  assert_eq!(solutions.len(), 8);
    ///  solutions.sort();
    ///  assert_eq!(solutions,
    ///      [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1],
    ///      [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]);
    /// ```
    ///
    /// See also:
    /// - [`Solver::into_solutions`]
    /// - [`crate::ApplyResult::into_solutions`]
    pub fn into_solutions<T: Solvable>(
        self,
        solver: Solver,
        ast: T,
        model_completion: bool,
    ) -> impl FusedIterator<Item = T::ModelInstance> {
        self.into_solutions_(None, solver, ast, model_completion)
    }

    pub(crate) fn into_solutions_<T: Solvable>(
        self,
        counterexamples: Option<std::rc::Rc<std::cell::RefCell<Vec<ast::Bool>>>>,
        solver: Solver,
        ast: T,
        model_completion: bool,
    ) -> impl FusedIterator<Item = T::ModelInstance> {
        let interpretation = self.convert_model(Model::new_empty(&self.ctx));
        self.iter_formulas().for_each(|f: Bool| solver.assert(f));
        if let Some(counterexamples) = &counterexamples {
            let counterexamples = ast::Bool::and(&counterexamples.borrow());
            let counterexamples = interpretation.eval(&counterexamples, false).unwrap();
            solver.assert(counterexamples);
        }
        GoalSolverIterator {
            counterexamples,
            interpretation,
            goal: self,
            subgoal_solver: solver,
            ast,
            model_completion,
        }
        .fuse()
    }
}

impl fmt::Display for Goal {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_goal_to_string(self.ctx.z3_ctx.as_ptr(), self.z3_goal) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl fmt::Debug for Goal {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Drop for Goal {
    fn drop(&mut self) {
        unsafe {
            Z3_goal_dec_ref(self.ctx.z3_ctx.as_ptr(), self.z3_goal);
        };
    }
}

unsafe impl Translate for Goal {
    fn translate(&self, ctx: &Context) -> Goal {
        unsafe {
            Goal::wrap(
                ctx,
                Z3_goal_translate(self.ctx.z3_ctx.as_ptr(), self.z3_goal, ctx.z3_ctx.as_ptr())
                    .unwrap(),
                self.models,
            )
        }
    }
}

struct GoalSolverIterator<T: Solvable> {
    counterexamples: Option<std::rc::Rc<std::cell::RefCell<Vec<ast::Bool>>>>,
    goal: Goal,
    interpretation: Model,
    subgoal_solver: Solver,
    ast: T,
    model_completion: bool,
}

impl<T: Solvable> Iterator for GoalSolverIterator<T> {
    type Item = T::ModelInstance;

    fn next(&mut self) -> Option<Self::Item> {
        match self.subgoal_solver.check() {
            SatResult::Sat => {
                let model = {
                    let subgoal_model = self.subgoal_solver.get_model()?;
                    self.goal.convert_model(subgoal_model)
                };
                let instance = self.ast.read_from_model(&model, self.model_completion)?;
                let subgoal_counterexample = {
                    let counterexample = self.ast.generate_constraint(&instance);
                    let subgoal_counterexample =
                        self.interpretation.eval(&counterexample, false).unwrap();
                    if let Some(counterexamples) = &mut self.counterexamples {
                        counterexamples.borrow_mut().push(counterexample);
                    }
                    subgoal_counterexample
                };
                self.subgoal_solver.assert(subgoal_counterexample);
                Some(instance)
            }
            _ => None,
        }
    }
}
