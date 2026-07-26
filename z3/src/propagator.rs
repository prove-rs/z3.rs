use std::cell::RefCell;
use std::ffi::c_void;
use std::marker::PhantomData;
use std::ptr::NonNull;
use z3_sys::*;

use crate::ast::{Ast, Dynamic};
use crate::callbacks::FfiState;
use crate::{Context, Solver};

type FreshFactory = Box<dyn Fn() -> Box<dyn UserPropagator> + Send + Sync>;

// ──────────────────────────────────────────────────────────────
// Public trait
// ──────────────────────────────────────────────────────────────

/// Trait for implementing a custom propagator that intercepts Z3's CDCL search loop.
///
/// Register an implementation with [`Solver::set_propagator`], then call
/// [`Solver::propagate_register`] for each expression you want to track.
///
/// ## Lifecycle
///
/// - **push** / **pop**: called when the solver opens/closes backtracking scopes.
///   Maintain a scope stack to undo state changes on `pop`.
///
/// ## Fresh instances for parallel search
///
/// Z3's parallel solver creates one propagator instance per background thread by
/// calling the `fresh_factory` closure supplied to [`Solver::set_propagator`].
/// The factory is required to be `Send + Sync` so that it cannot accidentally
/// capture Z3 ASTs (which are `!Send + !Sync`) from the outer scope — doing so
/// would silently use an AST from the wrong context on a background thread,
/// causing Z3 to return null and a subsequent `.unwrap()` to panic.
///
/// ## Optional event callbacks
///
/// Override any of the optional event methods to receive those events.
/// All events are registered with Z3 when [`Solver::set_propagator`] is called.
///
/// ## Consequence injection
///
/// Inside any callback, use [`PropagatorCallbackHandle::propagate_consequence`]
/// to assert deductions or conflicts back into the solver.
///
/// ## Example: minimal propagator
///
/// The two required methods are `push` and `pop`. Everything else is optional
/// and defaults to a no-op. A `Send + Sync` factory closure is passed as the
/// second argument to [`Solver::set_propagator`] to create fresh instances for
/// parallel solver threads.
///
/// ```
/// use z3::{UserPropagator, PropagatorCallbackHandle, Solver, SatResult};
/// use z3::ast::{Bool, Dynamic, Ast};
///
/// struct NoPropagation;
///
/// impl UserPropagator for NoPropagation {
///     fn push(&mut self) {}
///     fn pop(&mut self, _num_scopes: u32) {}
/// }
///
/// let solver = Solver::new();
/// let x = Bool::new_const("x");
/// solver.set_propagator(NoPropagation, || NoPropagation);
/// solver.propagate_register(&Dynamic::from_ast(&x));
/// solver.assert(&x);
/// assert_eq!(solver.check(), SatResult::Sat);
/// ```
///
/// ## Example: observing fixed assignments
///
/// Override `fixed` to react when a tracked expression receives a definite value.
/// Here the propagator uses the assignment to inject an implication directly into
/// the solver: when `x` is fixed to `true`, force `y` to be `true` as well.
///
/// The factory must satisfy `Send + Sync` and return the same propagator type,
/// which prevents Z3 ASTs (which are `!Send + !Sync`) from being captured directly.
/// To carry an AST into a fresh instance, wrap it with
/// [`PrepareSynchronized::synchronized`] and call `.recover()` inside the factory —
/// `recover()` translates the AST into the thread-local context, which the
/// `fresh_eh` trampoline has already set to the fresh thread's Z3 context.
///
/// ```
/// use z3::{UserPropagator, PropagatorCallbackHandle, PrepareSynchronized, Solver, SatResult};
/// use z3::ast::{Bool, Dynamic, Ast};
///
/// struct ImplyY {
///     y: Dynamic,
///     scope_stack: Vec<usize>,
/// }
///
/// impl UserPropagator for ImplyY {
///     fn push(&mut self) { self.scope_stack.push(0); }
///     fn pop(&mut self, n: u32) {
///         for _ in 0..n { self.scope_stack.pop(); }
///     }
///
///     fn fixed(&mut self, cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, value: &Dynamic) {
///         // When x is fixed to true, propagate y = true as a consequence.
///         if let Some(b) = value.as_bool().and_then(|b| b.as_bool()) {
///             if b {
///                 cb.propagate_consequence(&[ast], &[], &self.y);
///             }
///         }
///     }
/// }
///
/// let solver = Solver::new();
/// let x = Bool::new_const("x");
/// let y = Bool::new_const("y");
/// let y_dyn = Dynamic::from_ast(&y);
/// let x_dyn = Dynamic::from_ast(&x);
///
/// // Wrap y_dyn in a Synchronized handle so the factory closure can be Send+Sync.
/// // .recover() translates y into the fresh thread's context when the factory runs.
/// let y_sync = y_dyn.synchronized();
/// solver.set_propagator(
///     ImplyY { y: y_dyn, scope_stack: vec![] },
///     move || ImplyY { y: y_sync.recover(), scope_stack: vec![] },
/// );
/// solver.propagate_register(&x_dyn);
/// // Assert x = true; the propagator will then force y = true.
/// solver.assert(&x);
/// assert_eq!(solver.check(), SatResult::Sat);
/// // The model must have y = true because the propagator derived it.
/// let model = solver.get_model().unwrap();
/// assert_eq!(model.eval(&y, true).and_then(|b| b.as_bool()), Some(true));
/// ```
pub trait UserPropagator: 'static {
    /// Called when the solver opens a new backtracking scope.
    fn push(&mut self);

    /// Called when the solver backtracks `num_scopes` levels.
    fn pop(&mut self, num_scopes: u32);

    // ── optional events — override to receive them ──

    /// Called when a registered expression is assigned a fixed value.
    fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, _ast: &Dynamic, _value: &Dynamic) {}

    /// Called when all registered expressions have been assigned.
    /// Use this for branch-and-bound or final consistency checks.
    fn final_check(&mut self, _cb: &PropagatorCallbackHandle<'_>) {}

    /// Called when two registered expressions are found to be equal.
    fn eq(&mut self, _cb: &PropagatorCallbackHandle<'_>, _s: &Dynamic, _t: &Dynamic) {}

    /// Called when two registered expressions are found to be disequal.
    fn diseq(&mut self, _cb: &PropagatorCallbackHandle<'_>, _s: &Dynamic, _t: &Dynamic) {}

    /// Called when the solver creates a new term whose top-level symbol was registered
    /// via [`Solver::propagate_declare`].
    fn created(&mut self, _cb: &PropagatorCallbackHandle<'_>, _t: &Dynamic) {}

    /// Called when the solver is about to make a split decision on a registered expression.
    /// Call [`PropagatorCallbackHandle::next_split`] to override the choice.
    fn decide(
        &mut self,
        _cb: &PropagatorCallbackHandle<'_>,
        _t: &Dynamic,
        _idx: u32,
        _phase: bool,
    ) {
    }

    /// Called when the solver instantiates a quantifier. Return `false` to block the
    /// instantiation.
    fn on_binding(
        &mut self,
        _cb: &PropagatorCallbackHandle<'_>,
        _q: &Dynamic,
        _inst: &Dynamic,
    ) -> bool {
        true
    }
}

// ──────────────────────────────────────────────────────────────
// Callback handle
// ──────────────────────────────────────────────────────────────

/// A handle available only within a [`UserPropagator`] callback.
///
/// Use it to inject consequences, register new expressions to track, or override
/// the next split decision. The `'cb` lifetime prevents this handle from escaping
/// the callback scope.
#[derive(Debug)]
pub struct PropagatorCallbackHandle<'cb> {
    cb: Z3_solver_callback,
    /// Non-owning view of the current Z3 context (valid for the callback duration).
    pub(crate) ctx: Context,
    _marker: PhantomData<&'cb ()>,
}

impl<'cb> PropagatorCallbackHandle<'cb> {
    /// Inject a propagated consequence into the solver.
    ///
    /// - `fixed`: registered expressions currently fixed to specific values. Their
    ///   current assignments become the premise of the consequence clause.
    /// - `eq_pairs`: equality justifications as `(lhs, rhs)` pairs.
    /// - `conseq`: the AST to assert conditional on the premises.
    ///
    /// Returns `true` if the consequence was new; `false` if it was already known.
    ///
    /// ## Conditional vs. unconditional conflicts
    ///
    /// Passing a non-empty `fixed` slice makes the conflict *conditional*: Z3 only
    /// rules out the specific model where those expressions have their current values,
    /// allowing the search to continue with other assignments.
    ///
    /// Passing an empty `fixed` slice asserts `conseq` *globally* (unconditional),
    /// which immediately makes the solver UNSAT if `conseq` is `false`.
    ///
    /// ## Example: enumerate all Bool models via `final_check`
    ///
    /// ```
    /// use z3::{UserPropagator, PropagatorCallbackHandle, Solver, SatResult};
    /// use z3::ast::{Bool, Dynamic, Ast};
    ///
    /// /// Blocks every complete model in `final_check`, forcing Z3 to enumerate them all.
    /// struct BlockEachModel {
    ///     fixed: Vec<Dynamic>,
    ///     scope_stack: Vec<usize>,
    /// }
    ///
    /// impl UserPropagator for BlockEachModel {
    ///     fn push(&mut self) { self.scope_stack.push(self.fixed.len()); }
    ///     fn pop(&mut self, n: u32) {
    ///         for _ in 0..n {
    ///             if let Some(len) = self.scope_stack.pop() { self.fixed.truncate(len); }
    ///         }
    ///     }
    ///
    ///     fn fixed(&mut self, _: &PropagatorCallbackHandle<'_>, ast: &Dynamic, _: &Dynamic) {
    ///         self.fixed.push(ast.clone());
    ///     }
    ///
    ///     fn final_check(&mut self, cb: &PropagatorCallbackHandle<'_>) {
    ///         let false_dyn = Dynamic::from_ast(&Bool::from_bool(false));
    ///         // Premise = currently-fixed expressions → this blocks only THIS model,
    ///         // not all models (conditional conflict).
    ///         let premises: Vec<&Dynamic> = self.fixed.iter().collect();
    ///         cb.propagate_consequence(&premises, &[], &false_dyn);
    ///     }
    /// }
    ///
    /// // A free Bool has exactly two models (true and false). BlockEachModel blocks
    /// // each one in final_check; once both are exhausted, check() returns UNSAT.
    /// let solver = Solver::new();
    /// let x = Bool::new_const("x");
    /// let x_dyn = Dynamic::from_ast(&x);
    /// // The factory creates fresh background-thread instances without carrying
    /// // any captured ASTs — enforced at compile time by the Send+Sync bound.
    /// solver.set_propagator(
    ///     BlockEachModel { fixed: vec![], scope_stack: vec![] },
    ///     || BlockEachModel { fixed: vec![], scope_stack: vec![] },
    /// );
    /// solver.propagate_register(&x_dyn);
    ///
    /// // Enumerate all models until UNSAT.
    /// loop {
    ///     if solver.check() == SatResult::Unsat { break; }
    /// }
    /// ```
    pub fn propagate_consequence(
        &self,
        fixed: &[&Dynamic],
        eq_pairs: &[(&Dynamic, &Dynamic)],
        conseq: &Dynamic,
    ) -> bool {
        let fixed_asts: Vec<Z3_ast> = fixed.iter().map(|d| d.z3_ast).collect();
        let eq_lhs: Vec<Z3_ast> = eq_pairs.iter().map(|(l, _)| l.z3_ast).collect();
        let eq_rhs: Vec<Z3_ast> = eq_pairs.iter().map(|(_, r)| r.z3_ast).collect();
        unsafe {
            Z3_solver_propagate_consequence(
                self.ctx.z3_ctx.as_ptr(),
                self.cb,
                fixed_asts.len() as u32,
                fixed_asts.as_ptr(),
                eq_pairs.len() as u32,
                eq_lhs.as_ptr(),
                eq_rhs.as_ptr(),
                conseq.z3_ast,
            )
        }
    }

    /// Register a new expression for tracking. Can be called from within any callback.
    pub fn register(&self, expr: &Dynamic) {
        unsafe {
            Z3_solver_propagate_register_cb(self.ctx.z3_ctx.as_ptr(), self.cb, expr.z3_ast);
        }
    }

    /// Override the next split target. Only effective when called from [`UserPropagator::decide`].
    ///
    /// `phase` follows the Z3 lbool convention: negative = false, zero = undef, positive = true.
    ///
    /// Returns `false` if the expression is already assigned.
    pub fn next_split(&self, t: &Dynamic, idx: u32, phase: i32) -> bool {
        unsafe { Z3_solver_next_split(self.ctx.z3_ctx.as_ptr(), self.cb, t.z3_ast, idx, phase) }
    }

    /// The Z3 context associated with this callback invocation.
    pub fn context(&self) -> &Context {
        &self.ctx
    }
}

// ──────────────────────────────────────────────────────────────
// Internal state
// ──────────────────────────────────────────────────────────────

/// Heap-allocated state pinned by [`FfiState`] and passed to Z3 as `user_context`.
///
/// The allocation lives for the lifetime of the solver. [`Solver::set_propagator`] replaces
/// the inner propagator in-place on subsequent calls rather than re-initialising Z3.
pub(crate) struct PropagatorState {
    /// Owning or borrowed context for this propagator instance.
    ctx: Context,
    /// The user's propagator implementation; wrapped in `RefCell` for interior mutability
    /// since trampolines receive only a shared reference via `FfiState::borrow_raw`.
    propagator: RefCell<Box<dyn UserPropagator>>,
    /// Factory for creating fresh instances on background solver threads.
    ///
    /// `None` for fresh instances themselves — Z3 never calls `fresh_eh` on a fresh
    /// instance, so they never need their own factory.
    ///
    /// Required to be `Send + Sync` so that capturing a Z3 AST (which is
    /// `!Send + !Sync`) is a compile error, preventing wrong-context ASTs from
    /// silently ending up in background-thread callbacks.
    fresh_factory: Option<RefCell<FreshFactory>>,
}

// ──────────────────────────────────────────────────────────────
// Context guard for trampolines
// ──────────────────────────────────────────────────────────────

/// RAII guard that restores the thread-local Z3 context on drop.
///
/// ## Why this exists
///
/// Z3 AST factory functions (`Bool::from_bool`, variadic ops like `Bool::and`, etc.)
/// read [`Context::thread_local()`] internally. Callbacks invoked by Z3 on a
/// background solver thread (the `fresh_eh` path) run on a thread whose thread-local
/// context is a freshly-initialized default — not the propagator's context. Without
/// this guard, a user who calls `Bool::from_bool(true)` inside a `fixed` callback on
/// a fresh instance would create an AST in the wrong context. Combining that AST with
/// one passed into the callback would call a Z3 function with mismatched `Z3_context`s;
/// Z3 returns null and the `.unwrap()` inside the crate's macro expansions panics.
///
/// ## Why `with_z3_context` is not used here
///
/// [`crate::with_z3_context`] provides the same save/restore semantics but requires
/// `T: FnOnce() -> R + Send + Sync`. Those bounds are intentional: they prevent Z3
/// ASTs (which are `!Send + !Sync`) from being smuggled across context boundaries
/// without going through the [`crate::Translate`] / `Synchronize` machinery. Trampoline
/// closures capture `&PropagatorState`, which holds a `RefCell<Box<dyn UserPropagator>>`
/// — `RefCell` is `!Sync`, so the closure cannot satisfy the bound. Relaxing the bound
/// would silently permit capturing a wrong-context AST, defeating the safety guarantee.
/// This guard replicates the same save/restore logic without the closure restriction.
struct CtxGuard(Context);

impl Drop for CtxGuard {
    fn drop(&mut self) {
        Context::set_thread_local(&self.0);
    }
}

fn enter_callback_ctx(state_ctx: &Context) -> CtxGuard {
    let prev = Context::thread_local();
    Context::set_thread_local(state_ctx);
    CtxGuard(prev)
}

// ──────────────────────────────────────────────────────────────
// Trampolines
// ──────────────────────────────────────────────────────────────

unsafe extern "C" fn push_trampoline(ctx: *mut c_void, _cb: Z3_solver_callback) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    state.propagator.borrow_mut().push();
}

unsafe extern "C" fn pop_trampoline(
    ctx: *mut c_void,
    _cb: Z3_solver_callback,
    num_scopes: ::core::ffi::c_uint,
) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    state.propagator.borrow_mut().pop(num_scopes);
}

/// Creates a fresh propagator state for a new Z3 background thread.
///
/// # Known limitation
///
/// Z3 does not call a "destroy" callback for fresh instances, so the returned
/// allocation is intentionally leaked. Each parallel solver thread creates at most
/// one fresh instance; the number of leaks is bounded by the thread count (typically ≤ 8).
unsafe extern "C" fn fresh_trampoline(ctx: *mut c_void, new_ctx: Z3_context) -> *mut c_void {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let fresh_ctx = unsafe { Context::borrow_context(new_ctx) };
    let _guard = enter_callback_ctx(&fresh_ctx);
    let factory = state
        .fresh_factory
        .as_ref()
        .expect("Z3 called fresh_eh on a fresh instance — this is a Z3 invariant violation");
    let fresh_propagator = (factory.borrow())();
    FfiState::new(PropagatorState {
        ctx: fresh_ctx,
        propagator: RefCell::new(fresh_propagator),
        fresh_factory: None,
    })
    .into_raw()
}

unsafe extern "C" fn fixed_trampoline(
    ctx: *mut c_void,
    cb: Z3_solver_callback,
    t: Z3_ast,
    value: Z3_ast,
) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let t_dyn = unsafe { Dynamic::wrap(&state.ctx, t) };
    let v_dyn = unsafe { Dynamic::wrap(&state.ctx, value) };
    state.propagator.borrow_mut().fixed(&handle, &t_dyn, &v_dyn);
}

unsafe extern "C" fn final_trampoline(ctx: *mut c_void, cb: Z3_solver_callback) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    state.propagator.borrow_mut().final_check(&handle);
}

unsafe extern "C" fn eq_trampoline(ctx: *mut c_void, cb: Z3_solver_callback, s: Z3_ast, t: Z3_ast) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let s_dyn = unsafe { Dynamic::wrap(&state.ctx, s) };
    let t_dyn = unsafe { Dynamic::wrap(&state.ctx, t) };
    state.propagator.borrow_mut().eq(&handle, &s_dyn, &t_dyn);
}

unsafe extern "C" fn diseq_trampoline(
    ctx: *mut c_void,
    cb: Z3_solver_callback,
    s: Z3_ast,
    t: Z3_ast,
) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let s_dyn = unsafe { Dynamic::wrap(&state.ctx, s) };
    let t_dyn = unsafe { Dynamic::wrap(&state.ctx, t) };
    state.propagator.borrow_mut().diseq(&handle, &s_dyn, &t_dyn);
}

unsafe extern "C" fn created_trampoline(ctx: *mut c_void, cb: Z3_solver_callback, t: Z3_ast) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let t_dyn = unsafe { Dynamic::wrap(&state.ctx, t) };
    state.propagator.borrow_mut().created(&handle, &t_dyn);
}

unsafe extern "C" fn decide_trampoline(
    ctx: *mut c_void,
    cb: Z3_solver_callback,
    t: Z3_ast,
    idx: ::core::ffi::c_uint,
    phase: bool,
) {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let t_dyn = unsafe { Dynamic::wrap(&state.ctx, t) };
    state
        .propagator
        .borrow_mut()
        .decide(&handle, &t_dyn, idx, phase);
}

unsafe extern "C" fn on_binding_trampoline(
    ctx: *mut c_void,
    cb: Z3_solver_callback,
    q: Z3_ast,
    inst: Z3_ast,
) -> bool {
    let state = unsafe { FfiState::<PropagatorState>::borrow_raw(ctx) };
    let _guard = enter_callback_ctx(&state.ctx);
    let handle = PropagatorCallbackHandle {
        cb,
        ctx: state.ctx.clone(),
        _marker: PhantomData,
    };
    let q_dyn = unsafe { Dynamic::wrap(&state.ctx, q) };
    let inst_dyn = unsafe { Dynamic::wrap(&state.ctx, inst) };
    state
        .propagator
        .borrow_mut()
        .on_binding(&handle, &q_dyn, &inst_dyn)
}

// ──────────────────────────────────────────────────────────────
// Solver integration
// ──────────────────────────────────────────────────────────────

impl Solver {
    /// Attach a user propagator to this solver.
    ///
    /// The propagator intercepts the CDCL search loop. Call
    /// [`Solver::propagate_register`] for each expression you want to track.
    ///
    /// `fresh_factory` is called by Z3 once per background solver thread to create
    /// an independent propagator instance for that thread. It must be `Send + Sync`,
    /// which prevents accidentally capturing Z3 ASTs (which are `!Send + !Sync`) —
    /// doing so would silently carry a main-thread AST into a background-thread
    /// callback where it would cause a Z3 context mismatch.
    ///
    /// If called a second time (before [`Solver::check`]), the previous propagator
    /// and factory are replaced in-place without re-initialising Z3's internal state.
    /// All optional event callbacks are registered unconditionally; override the
    /// relevant `UserPropagator` methods to receive them.
    ///
    /// ## Example
    ///
    /// ```
    /// use z3::{UserPropagator, PropagatorCallbackHandle, Solver, SatResult};
    /// use z3::ast::{Bool, Dynamic, Ast};
    ///
    /// struct NoPropagation;
    ///
    /// impl UserPropagator for NoPropagation {
    ///     fn push(&mut self) {}
    ///     fn pop(&mut self, _: u32) {}
    /// }
    ///
    /// let solver = Solver::new();
    /// let x = Bool::new_const("x");
    /// let x_dyn = Dynamic::from_ast(&x);
    ///
    /// solver.set_propagator(NoPropagation, || NoPropagation);
    /// solver.propagate_register(&x_dyn);
    /// solver.assert(&x);
    /// assert_eq!(solver.check(), SatResult::Sat);
    ///
    /// // A second call replaces the propagator without re-initialising Z3 internals.
    /// solver.set_propagator(NoPropagation, || NoPropagation);
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// ```
    pub fn set_propagator<P, F>(&self, propagator: P, fresh_factory: F)
    where
        P: UserPropagator,
        F: Fn() -> P + Send + Sync + 'static,
    {
        // Erase the concrete return type into the dyn-boxed FreshFactory used for storage.
        let erased: FreshFactory = Box::new(move || Box::new(fresh_factory()));

        if let Some(existing_nn) = self.propagator.get() {
            // Z3_solver_propagate_init may only be called once per solver.
            // On subsequent calls, swap the inner propagator and factory in-place.
            let state = unsafe { FfiState::<PropagatorState>::borrow_raw(existing_nn.as_ptr()) };
            *state.propagator.borrow_mut() = Box::new(propagator);
            *state
                .fresh_factory
                .as_ref()
                .expect("main PropagatorState must have a factory")
                .borrow_mut() = erased;
            return;
        }

        // First call: heap-pin state and initialise Z3's propagation hooks.
        let raw = FfiState::new(PropagatorState {
            ctx: self.ctx.clone(),
            propagator: RefCell::new(Box::new(propagator)),
            fresh_factory: Some(RefCell::new(erased)),
        })
        .into_raw();
        // SAFETY: FfiState::into_raw wraps a Box, which is always non-null.
        let new_nn = unsafe { NonNull::new_unchecked(raw) };

        unsafe {
            Z3_solver_propagate_init(
                self.ctx.z3_ctx.as_ptr(),
                self.z3_slv,
                raw,
                Some(push_trampoline),
                Some(pop_trampoline),
                Some(fresh_trampoline),
            );
            // Register all optional trampolines unconditionally. The default trait
            // implementations are no-ops, so there is no cost for unneeded events.
            Z3_solver_propagate_fixed(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(fixed_trampoline));
            Z3_solver_propagate_final(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(final_trampoline));
            Z3_solver_propagate_eq(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(eq_trampoline));
            Z3_solver_propagate_diseq(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(diseq_trampoline));
            Z3_solver_propagate_created(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(created_trampoline));
            Z3_solver_propagate_decide(self.ctx.z3_ctx.as_ptr(), self.z3_slv, Some(decide_trampoline));
            Z3_solver_propagate_on_binding(
                self.ctx.z3_ctx.as_ptr(),
                self.z3_slv,
                Some(on_binding_trampoline),
            );
        }

        self.propagator.set(Some(new_nn));
    }

    /// Register an expression for tracking by the attached propagator.
    ///
    /// Must be called after [`Solver::set_propagator`] and before (or during) [`Solver::check`].
    /// Only Bool and Bit-Vector expressions can be registered.
    pub fn propagate_register(&self, expr: &Dynamic) {
        unsafe {
            Z3_solver_propagate_register(self.ctx.z3_ctx.as_ptr(), self.z3_slv, expr.z3_ast);
        }
    }
}
