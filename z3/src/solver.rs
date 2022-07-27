use ast;
use ast::Ast;
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Params;
use SatResult;
use Solver;
use Symbol;
use Z3_MUTEX;

impl<'ctx> Solver<'ctx> {
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
    /// [model construction is enabled]: struct.Config.html#method.set_model_generation
    /// [`Solver::assert()`]: #method.assert
    /// [`Solver::assert_and_track()`]: #method.assert_and_track
    /// [`Solver::get_model()`]: #method.get_model
    /// [`Solver::pop()`]: #method.pop
    /// [`Solver::push()`]: #method.push
    /// [`Solver::reset()`]: #method.reset
    ///
    pub fn new(ctx: &Context) -> Solver {
        Solver {
            ctx,
            z3_slv: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let s = Z3_mk_solver(ctx.z3_ctx);
                Z3_solver_inc_ref(ctx.z3_ctx, s);
                s
            },
        }
    }

    /// Create a new solver customized for the given logic.
    /// It returns `None` if the logic is unknown or unsupported.
    pub fn new_for_logic<S: Into<Symbol>>(ctx: &Context, logic: S) -> Option<Solver> {
        Some(Solver {
            ctx,
            z3_slv: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let s = Z3_mk_solver_for_logic(ctx.z3_ctx, logic.into().as_z3_symbol(ctx));
                if s.is_null() {
                    return None;
                }
                Z3_solver_inc_ref(ctx.z3_ctx, s);
                s
            },
        })
    }

    pub fn translate<'dest_ctx>(&self, dest: &'dest_ctx Context) -> Solver<'dest_ctx> {
        Solver {
            ctx: dest,
            z3_slv: unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                let s = Z3_solver_translate(self.ctx.z3_ctx, self.z3_slv, dest.z3_ctx);
                Z3_solver_inc_ref(dest.z3_ctx, s);
                s
            },
        }
    }

    /// Get this solver's context.
    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Assert a constraint into the solver.
    ///
    /// The functions [`Solver::check()`](#method.check) and
    /// [`Solver::check_assumptions()`](#method.check_assumptions) should be
    /// used to check whether the logical context is consistent or not.
    ///
    /// # See also:
    ///
    /// - [`Solver::assert_and_track()`](#method.assert_and_track)
    pub fn assert(&self, ast: &ast::Bool<'ctx>) {
        debug!("assert: {:?}", ast);
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_assert(self.ctx.z3_ctx, self.z3_slv, ast.z3_ast) };
    }

    /// Assert a constraint `a` into the solver, and track it (in the
    /// unsat) core using the Boolean constant `p`.
    ///
    /// This API is an alternative to
    /// [`Solver::check_assumptions()`](#method.check_assumptions)
    /// for extracting unsat cores. Both APIs can be used in the same solver.
    /// The unsat core will contain a combination of the Boolean variables
    /// provided using [`Solver::assert_and_track()`](#method.assert_and_track)
    /// and the Boolean literals provided using
    /// [`Solver::check_assumptions()`](#method.check_assumptions).
    ///
    /// # See also:
    ///
    /// - [`Solver::assert()`](#method.assert)
    pub fn assert_and_track(&self, ast: &ast::Bool<'ctx>, p: &ast::Bool<'ctx>) {
        debug!("assert_and_track: {:?}", ast);
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_assert_and_track(self.ctx.z3_ctx, self.z3_slv, ast.z3_ast, p.z3_ast) };
    }

    /// Remove all assertions from the solver.
    pub fn reset(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_reset(self.ctx.z3_ctx, self.z3_slv) };
    }

    /// Check whether the assertions in a given solver are consistent or not.
    ///
    /// The function [`Solver::get_model()`](#method.get_model)
    /// retrieves a model if the assertions is satisfiable (i.e., the
    /// result is `SatResult::Sat`) and [model construction is enabled].
    /// Note that if the call returns `SatResult::Unknown`, Z3 does not
    /// ensure that calls to [`Solver::get_model()`](#method.get_model)
    /// succeed and any models produced in this case are not guaranteed
    /// to satisfy the assertions.
    ///
    /// The function [`Solver::get_proof()`](#method.get_proof)
    /// retrieves a proof if [proof generation was enabled] when the context
    /// was created, and the assertions are unsatisfiable (i.e., the result
    /// is `SatResult::Unsat`).
    ///
    /// # See also:
    ///
    /// - [`Config::set_model_generation()`](struct.Config.html#method.set_model_generation)
    /// - [`Config::set_proof_generation()`](struct.Config.html#method.set_proof_generation)
    /// - [`Solver::check_assumptions()`](#method.check_assumptions)
    ///
    /// [model construction is enabled]: struct.Config.html#method.set_model_generation
    /// [proof generation was enabled]: struct.Config.html#method.set_proof_generation
    pub fn check(&self) -> SatResult {
        let _guard = Z3_MUTEX.lock().unwrap();
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
    /// The function
    /// [`Solver::get_unsat_core()`](#method.get_unsat_core)
    /// retrieves the subset of the assumptions used in the
    /// unsatisfiability proof produced by Z3.
    ///
    /// # See also:
    ///
    /// - [`Solver::check()`](#method.check)
    pub fn check_assumptions(&self, assumptions: &[ast::Bool<'ctx>]) -> SatResult {
        let _guard = Z3_MUTEX.lock().unwrap();
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

    /// Return a subset of the assumptions provided to either the last
    ///
    /// * `check_assumptions` call, or
    /// * sequence of `assert_and_track` calls followed by a `check` call.
    ///
    /// These are the assumptions Z3 used in the unsatisfiability proof.
    /// Assumptions are available in Z3. They are used to extract unsatisfiable
    /// cores.  They may be also used to "retract" assumptions. Note that,
    /// assumptions are not really "soft constraints", but they can be used to
    /// implement them.
    ///
    /// # See also:
    ///
    /// - [`Solver::check_assumptions`](#method.check_assumptions)
    /// - [`Solver::assert_and_track`](#method.assert_and_track)
    pub fn get_unsat_core(&self) -> Vec<ast::Bool<'ctx>> {
        let z3_unsat_core = unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_get_unsat_core(self.ctx.z3_ctx, self.z3_slv)
        };
        if z3_unsat_core.is_null() {
            return vec![];
        }

        let len = unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_ast_vector_size(self.ctx.z3_ctx, z3_unsat_core)
        };

        let mut unsat_core = Vec::with_capacity(len as usize);

        for i in 0..len {
            let elem = unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                Z3_ast_vector_get(self.ctx.z3_ctx, z3_unsat_core, i)
            };
            let elem = unsafe { ast::Bool::new(self.ctx, elem) };
            unsat_core.push(elem);
        }

        unsat_core
    }

    /// Create a backtracking point.
    ///
    /// The solver contains a stack of assertions.
    ///
    /// # See also:
    ///
    /// - [`Solver::pop()`](#method.pop)
    pub fn push(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_push(self.ctx.z3_ctx, self.z3_slv) };
    }

    /// Backtrack `n` backtracking points.
    ///
    /// # See also:
    ///
    /// - [`Solver::push()`](#method.push)
    pub fn pop(&self, n: u32) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_pop(self.ctx.z3_ctx, self.z3_slv, n) };
    }

    /// Retrieve the model for the last [`Solver::check()`](#method.check)
    /// or [`Solver::check_assumptions()`](#method.check_assumptions)
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given solver, or if
    /// the result was `Z3_L_FALSE`.
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        Model::of_solver(self)
    }

    /// Retrieve the proof for the last [`Solver::check()`](#method.check)
    /// or [`Solver::check_assumptions()`](#method.check_assumptions)
    ///
    /// The error handler is invoked if [proof generation is not enabled],
    /// or if the commands above were not invoked for the given solver,
    /// or if the result was different from `Z3_L_FALSE`.
    ///
    /// # See also:
    ///
    /// - [`Config::set_proof_generation()`](struct.Config.html#method.set_proof_generation)
    ///
    /// [proof generation is not enabled]: struct.Config.html#method.set_proof_generation
    //
    // This seems to actually return an Ast with kind `SortKind::Unknown`, which we don't
    // have an Ast subtype for yet.
    pub fn get_proof(&self) -> Option<impl Ast<'ctx>> {
        let m = unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            Z3_solver_get_proof(self.ctx.z3_ctx, self.z3_slv)
        };
        if !m.is_null() {
            return Some(unsafe { ast::Dynamic::new(self.ctx, m) });
        } else {
            None
        }
    }

    /// Return a brief justification for an "unknown" result (i.e., `SatResult::Unknown`) for
    /// the commands [`Solver::check()`](#method.check) and
    /// [`Solver::check_assumptions()`](#method.check_assumptions)
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
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_set_params(self.ctx.z3_ctx, self.z3_slv, params.z3_params) };
    }
}

impl<'ctx> fmt::Display for Solver<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_solver_to_string(self.ctx.z3_ctx, self.z3_slv) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
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
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_slv) };
    }
}
