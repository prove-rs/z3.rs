use log::debug;
use std::ffi::{CStr, CString};
use std::fmt;

use z3_sys::*;

use std::ops::AddAssign;

use crate::{ast, ast::Ast, Context, Model, Params, SatResult, Solver, Statistics, Symbol};

impl<'ctx> Solver<'ctx> {
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_slv: Z3_solver) -> Solver<'ctx> {
        Z3_solver_inc_ref(ctx.z3_ctx, z3_slv);
        Solver { ctx, z3_slv }
    }

    /// Create a new solver. This solver is a "combined solver"
    /// that internally uses a non-incremental (`solver1`) and an
    /// incremental solver (`solver2`). This combined solver changes
    /// its behaviour based on how it is used and how its parameters are set.
    ///
    /// If the solver is used in a non incremental way (i.e. no calls to
    /// [`Solver::push()`] or [`Solver::pop()`], and no calls to
    /// [`Solver::assert()`] or [`Solver::assert_and_track()`] after checking
    /// satisfiability without an intervening [`Solver::reset()`]) then `solver1`
    /// will be used. This solver will apply Z3's "default" tactic.
    ///
    /// The "default" tactic will attempt to probe the logic used by the
    /// assertions and will apply a specialized tactic if one is supported.
    /// Otherwise the general `(and-then simplify smt)` tactic will be used.
    ///
    /// If the solver is used in an incremental way then the combined solver
    /// will switch to using `solver2` (which behaves similarly to the general
    /// "smt" tactic).
    ///
    /// Note however it is possible to set the `solver2_timeout`,
    /// `solver2_unknown`, and `ignore_solver1` parameters of the combined
    /// solver to change its behaviour.
    ///
    /// The function [`Solver::get_model()`] retrieves a model if the
    /// assertions is satisfiable (i.e., the result is
    /// `SatResult::Sat`) and [model construction is enabled].
    /// The function [`Solver::get_model()`] can also be used even
    /// if the result is `SatResult::Unknown`, but the returned model
    /// is not guaranteed to satisfy quantified assertions.
    ///
    /// [model construction is enabled]: crate::Config::set_model_generation
    pub fn new(ctx: &'ctx Context) -> Solver<'ctx> {
        unsafe { Self::wrap(ctx, Z3_mk_solver(ctx.z3_ctx)) }
    }

    /// Parse an SMT-LIB2 string with assertions, soft constraints and optimization objectives.
    /// Add the parsed constraints and objectives to the solver.
    pub fn from_string<T: Into<Vec<u8>>>(&self, source_string: T) {
        let source_cstring = CString::new(source_string).unwrap();
        unsafe {
            Z3_solver_from_string(self.ctx.z3_ctx, self.z3_slv, source_cstring.as_ptr());
        }
    }

    /// Create a new solver customized for the given logic.
    /// It returns `None` if the logic is unknown or unsupported.
    pub fn new_for_logic<S: Into<Symbol>>(ctx: &'ctx Context, logic: S) -> Option<Solver<'ctx>> {
        unsafe {
            let s = Z3_mk_solver_for_logic(ctx.z3_ctx, logic.into().as_z3_symbol(ctx));
            if s.is_null() {
                None
            } else {
                Some(Self::wrap(ctx, s))
            }
        }
    }

    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Solver<'dest_ctx> {
        unsafe {
            Solver::wrap(
                dest,
                Z3_solver_translate(self.ctx.z3_ctx, self.z3_slv, dest.z3_ctx),
            )
        }
    }

    /// Get this solver's context.
    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Assert a constraint into the solver.
    ///
    /// The functions [`Solver::check()`] and [`Solver::check_assumptions()`]
    /// should be used to check whether the logical context is consistent
    /// or not.
    ///
    /// ```rust
    /// use z3::{Config, Context, Solver, ast, SatResult, ast::Bool};
    /// let cfg = Config::new();
    /// let ctx = Context::new(&cfg);
    /// let mut solver = Solver::new(&ctx);
    ///
    /// solver.assert(&Bool::from_bool(&ctx, true));
    /// solver += &Bool::from_bool(&ctx, false);
    /// solver += Bool::fresh_const(&ctx, "");
    ///
    /// assert_eq!(solver.check(), SatResult::Unsat);
    /// ````
    ///
    /// # See also:
    ///
    /// - [`Solver::assert_and_track()`]
    pub fn assert(&self, ast: &ast::Bool<'ctx>) {
        debug!("assert: {:?}", ast);
        unsafe { Z3_solver_assert(self.ctx.z3_ctx, self.z3_slv, ast.z3_ast) };
    }

    /// Assert a constraint `a` into the solver, and track it (in the
    /// unsat) core using the Boolean constant `p`.
    ///
    /// This API is an alternative to
    /// [`Solver::check_assumptions()`]
    /// for extracting unsat cores. Both APIs can be used in the same solver.
    /// The unsat core will contain a combination of the Boolean variables
    /// provided using [`Solver::assert_and_track()`]
    /// and the Boolean literals provided using
    /// [`Solver::check_assumptions()`].
    ///
    /// # See also:
    ///
    /// - [`Solver::assert()`]
    pub fn assert_and_track(&self, ast: &ast::Bool<'ctx>, p: &ast::Bool<'ctx>) {
        debug!("assert_and_track: {:?}", ast);
        unsafe { Z3_solver_assert_and_track(self.ctx.z3_ctx, self.z3_slv, ast.z3_ast, p.z3_ast) };
    }

    /// Remove all assertions from the solver.
    pub fn reset(&self) {
        unsafe { Z3_solver_reset(self.ctx.z3_ctx, self.z3_slv) };
    }

    /// Check whether the assertions in a given solver are consistent or not.
    ///
    /// The function [`Solver::get_model()`]
    /// retrieves a model if the assertions is satisfiable (i.e., the
    /// result is [`SatResult::Sat`]) and [model construction is enabled].
    /// Note that if the call returns `SatResult::Unknown`, Z3 does not
    /// ensure that calls to [`Solver::get_model()`]
    /// succeed and any models produced in this case are not guaranteed
    /// to satisfy the assertions.
    ///
    /// The function [`Solver::get_proof()`]
    /// retrieves a proof if [proof generation was enabled] when the context
    /// was created, and the assertions are unsatisfiable (i.e., the result
    /// is [`SatResult::Unsat`]).
    ///
    /// # See also:
    ///
    /// - [`Config::set_model_generation()`](crate::Config::set_model_generation)
    /// - [`Config::set_proof_generation()`](crate::Config::set_proof_generation)
    /// - [`Solver::check_assumptions()`]
    ///
    /// [model construction is enabled]: crate::Config::set_model_generation
    /// [proof generation was enabled]: crate::Config::set_proof_generation
    pub fn check(&self) -> SatResult {
        match unsafe { Z3_solver_check(self.ctx.z3_ctx, self.z3_slv) } {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    /// Check whether the assertions in the given solver and
    /// optional assumptions are consistent or not.
    ///
    /// The function [`Solver::get_unsat_core()`]
    /// retrieves the subset of the assumptions used in the
    /// unsatisfiability proof produced by Z3.
    ///
    /// # See also:
    ///
    /// - [`Solver::check()`]
    pub fn check_assumptions(&self, assumptions: &[ast::Bool<'ctx>]) -> SatResult {
        let a: Vec<Z3_ast> = assumptions.iter().map(|a| a.z3_ast).collect();
        match unsafe {
            Z3_solver_check_assumptions(self.ctx.z3_ctx, self.z3_slv, a.len() as u32, a.as_ptr())
        } {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    // Return a vector of assumptions in the solver.
    pub fn get_assertions(&self) -> Vec<ast::Bool<'ctx>> {
        let z3_vec = unsafe { Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_slv) };

        (0..unsafe { Z3_ast_vector_size(self.ctx.z3_ctx, z3_vec) })
            .map(|i| unsafe {
                let z3_ast = Z3_ast_vector_get(self.ctx.z3_ctx, z3_vec, i);
                ast::Bool::wrap(self.ctx, z3_ast)
            })
            .collect()
    }

    /// Return a subset of the assumptions provided to either the last
    ///
    /// * [`Solver::check_assumptions`] call, or
    /// * sequence of [`Solver::assert_and_track`] calls followed
    ///   by a [`Solver::check`] call.
    ///
    /// These are the assumptions Z3 used in the unsatisfiability proof.
    /// Assumptions are available in Z3. They are used to extract unsatisfiable
    /// cores.  They may be also used to "retract" assumptions. Note that,
    /// assumptions are not really "soft constraints", but they can be used to
    /// implement them.
    ///
    /// By default, the unsat core will not be minimized. Generation of a minimized
    /// unsat core can be enabled via the `"sat.core.minimize"` and `"smt.core.minimize"`
    /// settings for SAT and SMT cores respectively. Generation of minimized unsat cores
    /// will be more expensive.
    ///
    /// # See also:
    ///
    /// - [`Solver::check_assumptions`]
    /// - [`Solver::assert_and_track`]
    pub fn get_unsat_core(&self) -> Vec<ast::Bool<'ctx>> {
        let z3_unsat_core = unsafe { Z3_solver_get_unsat_core(self.ctx.z3_ctx, self.z3_slv) };
        if z3_unsat_core.is_null() {
            return vec![];
        }

        let len = unsafe { Z3_ast_vector_size(self.ctx.z3_ctx, z3_unsat_core) };

        let mut unsat_core = Vec::with_capacity(len as usize);

        for i in 0..len {
            let elem = unsafe { Z3_ast_vector_get(self.ctx.z3_ctx, z3_unsat_core, i) };
            let elem = unsafe { ast::Bool::wrap(self.ctx, elem) };
            unsat_core.push(elem);
        }

        unsat_core
    }

    /// Retrieve consequences from the solver given a set of assumptions.
    pub fn get_consequences(
        &self,
        assumptions: &[ast::Bool<'ctx>],
        variables: &[ast::Bool<'ctx>],
    ) -> Vec<ast::Bool<'ctx>> {
        unsafe {
            let _assumptions = Z3_mk_ast_vector(self.ctx.z3_ctx);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, _assumptions);
            assumptions.iter().for_each(|x| {
                Z3_ast_vector_push(self.ctx.z3_ctx, _assumptions, x.z3_ast);
            });

            let _variables = Z3_mk_ast_vector(self.ctx.z3_ctx);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, _variables);
            variables.iter().for_each(|x| {
                Z3_ast_vector_push(self.ctx.z3_ctx, _variables, x.z3_ast);
            });
            let consequences = Z3_mk_ast_vector(self.ctx.z3_ctx);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, consequences);

            Z3_solver_get_consequences(
                self.ctx.z3_ctx,
                self.z3_slv,
                _assumptions,
                _variables,
                consequences,
            );
            let mut cons = vec![];
            for i in 0..Z3_ast_vector_size(self.ctx.z3_ctx, consequences) {
                let val = Z3_ast_vector_get(self.ctx.z3_ctx, consequences, i);
                cons.push(ast::Bool::wrap(self.ctx, val));
            }
            cons
        }
    }

    /// Create a backtracking point.
    ///
    /// The solver contains a stack of assertions.
    ///
    /// # See also:
    ///
    /// - [`Solver::pop()`]
    pub fn push(&self) {
        unsafe { Z3_solver_push(self.ctx.z3_ctx, self.z3_slv) };
    }

    /// Backtrack `n` backtracking points.
    ///
    /// # See also:
    ///
    /// - [`Solver::push()`]
    pub fn pop(&self, n: u32) {
        unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_slv, n) };
    }

    /// Retrieve the model for the last [`Solver::check()`]
    /// or [`Solver::check_assumptions()`].
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given solver, or if
    /// the result was [`SatResult::Unsat`].
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        Model::of_solver(self)
    }

    /// Retrieve the proof for the last [`Solver::check()`]
    /// or [`Solver::check_assumptions()`].
    ///
    /// The error handler is invoked if [proof generation is not enabled],
    /// or if the commands above were not invoked for the given solver,
    /// or if the result was different from [`SatResult::Unsat`].
    ///
    /// # See also:
    ///
    /// - [`Config::set_proof_generation()`](crate::Config::set_proof_generation)
    ///
    /// [proof generation is not enabled]: crate::Config::set_proof_generation
    //
    // This seems to actually return an Ast with kind `SortKind::Unknown`, which we don't
    // have an Ast subtype for yet.
    pub fn get_proof(&self) -> Option<impl Ast<'ctx>> {
        let m = unsafe { Z3_solver_get_proof(self.ctx.z3_ctx, self.z3_slv) };
        if !m.is_null() {
            Some(unsafe { ast::Dynamic::wrap(self.ctx, m) })
        } else {
            None
        }
    }

    /// Return a brief justification for an "unknown" result (i.e.,
    /// [`SatResult::Unknown`]) for the commands [`Solver::check()`]
    /// and [`Solver::check_assumptions()`].
    pub fn get_reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_solver_get_reason_unknown(self.ctx.z3_ctx, self.z3_slv) };
        if p.is_null() {
            return None;
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
    }

    /// Set the current solver using the given parameters.
    pub fn set_params(&self, params: &Params<'ctx>) {
        unsafe { Z3_solver_set_params(self.ctx.z3_ctx, self.z3_slv, params.z3_params) };
    }

    /// Retrieve the statistics for the last [`Solver::check()`].
    pub fn get_statistics(&self) -> Statistics<'ctx> {
        unsafe {
            Statistics::wrap(
                self.ctx,
                Z3_solver_get_statistics(self.ctx.z3_ctx, self.z3_slv),
            )
        }
    }

    pub fn to_smt2(&self) -> String {
        let name = CString::new("benchmark generated from rust API").unwrap();
        let logic = CString::new("").unwrap();
        let status = CString::new("unknown").unwrap();
        let attributes = CString::new("").unwrap();
        let assumptions = self.get_assertions();
        let mut num_assumptions = assumptions.len() as u32;
        let formula = if num_assumptions > 0 {
            num_assumptions -= 1;
            assumptions[num_assumptions as usize].z3_ast
        } else {
            ast::Bool::from_bool(self.ctx, true).z3_ast
        };
        let z3_assumptions = assumptions.iter().map(|a| a.z3_ast).collect::<Vec<_>>();

        let p = unsafe {
            Z3_benchmark_to_smtlib_string(
                self.ctx.z3_ctx,
                name.as_ptr(),
                logic.as_ptr(),
                status.as_ptr(),
                attributes.as_ptr(),
                num_assumptions,
                z3_assumptions.as_ptr(),
                formula,
            )
        };
        if p.is_null() {
            return String::new();
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
            .unwrap_or_else(String::new)
    }
}

impl<'ctx> fmt::Display for Solver<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_solver_to_string(self.ctx.z3_ctx, self.z3_slv) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Solver<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Solver<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_slv) };
    }
}

impl<'ctx> Clone for Solver<'ctx> {
    // Cloning using routines suggested by the author of Z3: https://stackoverflow.com/questions/16516337/copying-z3-solver
    fn clone(self: &Solver<'ctx>) -> Self {
        let new_solver = Solver::new(self.ctx);

        self.get_assertions().iter().for_each(|a| {
            new_solver.assert(a);
        });

        new_solver
    }
}

impl<'ctx> AddAssign<&ast::Bool<'ctx>> for Solver<'ctx> {
    fn add_assign(&mut self, rhs: &ast::Bool<'ctx>) {
        self.assert(rhs);
    }
}

impl<'ctx> AddAssign<ast::Bool<'ctx>> for Solver<'ctx> {
    fn add_assign(&mut self, rhs: ast::Bool<'ctx>) {
        self.assert(&rhs);
    }
}
