use log::debug;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::convert::TryInto;
use std::ffi::{CStr, CString, c_void};
use std::fmt;
use std::iter::FusedIterator;
use std::sync::atomic::AtomicU32;
use z3_sys::*;

#[cfg(feature = "z3_4_16")]
use crate::Translate;
use crate::solver::Solvable;
use crate::{
    AstVector, Context, Model, Optimize, Params, SatResult, Statistics, Symbol,
    ast::{Ast, Bool, Dynamic},
};

#[cfg(feature = "num")]
use num::{
    bigint::{BigInt, BigUint, Sign},
    rational::BigRational,
};

impl Optimize {
    unsafe fn wrap(ctx: &Context, z3_opt: Z3_optimize) -> Optimize {
        unsafe {
            Z3_optimize_inc_ref(ctx.z3_ctx.0, z3_opt);
        }
        Optimize {
            ctx: ctx.clone(),
            z3_opt,
            registered_model_handler: Default::default(),
        }
    }

    /// Create a new optimize context.
    pub fn new() -> Optimize {
        let ctx = &Context::thread_local();
        unsafe { Self::wrap(ctx, Z3_mk_optimize(ctx.z3_ctx.0).unwrap()) }
    }

    /// Parse an SMT-LIB2 string with assertions, soft constraints and optimization objectives.
    /// Add the parsed constraints and objectives to the optimizer.
    pub fn from_string<T: Into<Vec<u8>>>(&self, source_string: T) {
        let source_cstring = CString::new(source_string).unwrap();
        unsafe {
            Z3_optimize_from_string(self.ctx.z3_ctx.0, self.z3_opt, source_cstring.as_ptr());
        }
    }

    /// Get this optimizers 's context.
    pub fn get_context(&self) -> &Context {
        &self.ctx
    }

    /// Add a hard constraint to the optimization context.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert_soft()`]
    /// - [`Optimize::maximize()`]
    /// - [`Optimize::minimize()`]
    pub fn assert<T: Borrow<Bool>>(&self, ast: T) {
        let ast = ast.borrow();
        unsafe { Z3_optimize_assert(self.ctx.z3_ctx.0, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Assert a constraint `a` into the solver, and track it (in the
    /// unsat) core using the Boolean constant `p`.
    ///
    /// This API is an alternative to
    /// [`Optimize::check()`]
    /// for extracting unsat cores. Both APIs can be used in the same solver.
    /// The unsat core will contain a combination of the Boolean variables
    /// provided using [`Optimize::assert_and_track()`]
    /// and the Boolean literals provided using
    /// [`Optimize::check()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::assert_soft()`]
    pub fn assert_and_track(&self, ast: &Bool, p: &Bool) {
        debug!("assert_and_track: {ast:?}");
        unsafe {
            Z3_optimize_assert_and_track(self.ctx.z3_ctx.0, self.z3_opt, ast.z3_ast, p.z3_ast)
        };
    }

    /// Assert soft constraint to the optimization context.
    /// Weight is a positive, rational penalty for violating the constraint.
    /// Group is an optional identifier to group soft constraints.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::maximize()`]
    /// - [`Optimize::minimize()`]
    pub fn assert_soft(&self, ast: &impl Ast, weight: impl Weight, group: Option<Symbol>) {
        let weight_string = weight.to_string();
        let weight_cstring = CString::new(weight_string).unwrap();
        let group = group.map(|g| g.as_z3_symbol());

        unsafe {
            Z3_optimize_assert_soft(
                self.ctx.z3_ctx.0,
                self.z3_opt,
                ast.get_z3_ast(),
                weight_cstring.as_ptr(),
                group,
            )
        };
    }

    /// Add a maximization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::minimize()`]
    pub fn maximize(&self, ast: &impl Ast) {
        // https://github.com/Z3Prover/z3/blob/09f911d8a84cd91988e5b96b69485b2a9a2edba3/src/opt/opt_context.cpp#L118-L120
        assert!(matches!(
            ast.get_sort().kind(),
            SortKind::Int | SortKind::Real | SortKind::Bv
        ));
        unsafe { Z3_optimize_maximize(self.ctx.z3_ctx.0, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Add a minimization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`]
    /// - [`Optimize::maximize()`]
    pub fn minimize(&self, ast: &impl Ast) {
        assert!(matches!(
            ast.get_sort().kind(),
            SortKind::Int | SortKind::Real | SortKind::Bv
        ));
        unsafe { Z3_optimize_minimize(self.ctx.z3_ctx.0, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Return a subset of the assumptions provided to either the last
    ///
    /// * [`Optimize::check`] call, or
    /// * sequence of [`Optimize::assert_and_track`] calls followed
    ///   by an [`Optimize::check`] call.
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
    /// - [`Optimize::check`]
    pub fn get_unsat_core(&self) -> Vec<Bool> {
        let Some(raw) = (unsafe { Z3_optimize_get_unsat_core(self.ctx.z3_ctx.0, self.z3_opt) })
        else {
            return vec![];
        };
        let av = unsafe { AstVector::wrap(&self.ctx, raw) };
        av.try_into().expect("unsat core contains only Bool")
    }

    /// Create a backtracking point.
    ///
    /// The optimize solver contains a set of rules, added facts and assertions.
    /// The set of rules, facts and assertions are restored upon calling
    /// [`Optimize::pop()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::pop()`]
    pub fn push(&self) {
        unsafe { Z3_optimize_push(self.ctx.z3_ctx.0, self.z3_opt) };
    }

    /// Backtrack one level.
    ///
    /// # Preconditions:
    ///
    /// - The number of calls to [`Optimize::pop`] cannot exceed the number of calls to
    ///   [`Optimize::push()`].
    ///
    /// # See also:
    ///
    /// - [`Optimize::push()`]
    pub fn pop(&self) {
        unsafe { Z3_optimize_pop(self.ctx.z3_ctx.0, self.z3_opt) };
    }

    /// Check consistency and produce optimal values.
    ///
    /// # See also:
    ///
    /// - [`Optimize::get_model()`]
    pub fn check(&self, assumptions: &[Bool]) -> SatResult {
        let assumptions: Vec<Z3_ast> = assumptions.iter().map(|a| a.z3_ast).collect();
        match unsafe {
            Z3_optimize_check(
                self.ctx.z3_ctx.0,
                self.z3_opt,
                assumptions.len().try_into().unwrap(),
                assumptions.as_ptr(),
            )
        } {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    /// Retrieve the model for the last [`Optimize::check()`].
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given optimization
    /// solver, or if the result was [`SatResult::Unsat`].
    pub fn get_model(&self) -> Option<Model> {
        Model::of_optimize(self)
    }

    /// Retrieve the objectives for the last [`Optimize::check()`].
    ///
    /// This contains maximize/minimize objectives and grouped soft constraints.
    pub fn get_objectives(&self) -> Vec<Dynamic> {
        let raw = unsafe { Z3_optimize_get_objectives(self.ctx.z3_ctx.0, self.z3_opt).unwrap() };
        unsafe { AstVector::wrap(&self.ctx, raw) }.to_vec()
    }

    /// Retrieve a string that describes the last status returned by [`Optimize::check()`].
    ///
    /// Use this method when [`Optimize::check()`] returns [`SatResult::Unknown`].
    pub fn get_reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_optimize_get_reason_unknown(self.ctx.z3_ctx.0, self.z3_opt) };
        if p.is_null() {
            return None;
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
    }

    /// Configure the parameters for this Optimize.
    pub fn set_params(&self, params: &Params) {
        unsafe { Z3_optimize_set_params(self.ctx.z3_ctx.0, self.z3_opt, params.z3_params) };
    }

    /// Retrieve the statistics for the last [`Optimize::check()`].
    pub fn get_statistics(&self) -> Statistics {
        unsafe {
            Statistics::wrap(
                &self.ctx,
                Z3_optimize_get_statistics(self.ctx.z3_ctx.0, self.z3_opt).unwrap(),
            )
        }
    }

    /// Iterate over solutions to the given [`Solvable`], cloning this [`Optimize`].
    ///
    /// The [`Optimize`] given to this method is [`Clone`]'d when producing the iterator: no change
    /// is made to the optimizer passed to the function.
    ///
    /// Each iteration calls [`Optimize::check`] with no assumptions and asserts a counterexample
    /// constraint to exclude the current solution, yielding distinct model instances until the
    /// optimizer returns `UNSAT` or `UNKNOWN`.
    ///
    /// # Example
    ///
    /// ```
    /// # use z3::Optimize;
    /// # use z3::ast::*;
    ///  let opt = Optimize::new();
    ///  let a = Int::new_const("a");
    ///  opt.assert(a.le(4));
    ///  opt.assert(a.ge(0));
    ///  let solutions: Vec<_> = opt.solutions(a, true).collect();
    ///  let mut values: Vec<_> = solutions.into_iter().map(|a| a.as_u64().unwrap()).collect();
    ///  values.sort();
    ///  assert_eq!(vec![0, 1, 2, 3, 4], values);
    /// ```
    ///
    /// # See also
    ///
    /// - [`Optimize::into_solutions`]
    /// - [`Optimize::check_and_get_model`]
    // Requires the `z3_4_16` feature (Z3 >= 4.16.0). This gate is temporary and will
    // be removed once the minimum supported Z3 version is bumped to 4.16.0.
    #[cfg(feature = "z3_4_16")]
    pub fn solutions<T: Solvable>(
        &self,
        t: T,
        model_completion: bool,
    ) -> impl FusedIterator<Item = T::ModelInstance> {
        OptimizeIterator {
            optimize: self.clone(),
            ast: t,
            model_completion,
        }
        .fuse()
    }

    /// Consume this [`Optimize`] and iterate over solutions to the given [`Solvable`].
    ///
    /// Each iteration calls [`Optimize::check`] with no assumptions and asserts a
    /// counterexample constraint to exclude the current solution, yielding all
    /// distinct model instances until the optimizer returns `UNSAT` or `UNKNOWN`.
    ///
    /// # See also
    ///
    /// - [`Optimize::solutions`]
    /// - [`Optimize::check_and_get_model`]
    pub fn into_solutions<T: Solvable>(
        self,
        t: T,
        model_completion: bool,
    ) -> impl FusedIterator<Item = T::ModelInstance> {
        OptimizeIterator {
            optimize: self,
            ast: t,
            model_completion,
        }
        .fuse()
    }

    /// Check the optimizer and, if satisfiable, return a single model instance for `t`.
    ///
    /// Combines `check(&[])` + `get_model()` + `Solvable::read_from_model`.
    /// Returns `Some(instance)` on `Sat` with successful model extraction; `None` otherwise.
    ///
    /// # See also
    ///
    /// - [`Optimize::into_solutions`]
    pub fn check_and_get_model<T: Solvable>(
        &self,
        t: T,
        model_completion: bool,
    ) -> Option<T::ModelInstance> {
        match self.check(&[]) {
            SatResult::Sat => {
                let model = self.get_model()?;
                t.read_from_model(&model, model_completion)
            }
            _ => None,
        }
    }

    /// Return all assertions currently in the optimizer.
    pub fn get_assertions(&self) -> Vec<Bool> {
        let av = unsafe {
            AstVector::wrap(
                &self.ctx,
                Z3_optimize_get_assertions(self.ctx.z3_ctx.0, self.z3_opt).unwrap(),
            )
        };
        av.try_into().expect("solver assertions are always Bool")
    }

    /// Retrieve the lower bound value or approximation for the i-th optimization objective.
    pub fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        unsafe {
            Z3_optimize_get_lower(self.ctx.z3_ctx.0, self.z3_opt, objective_id)
                .map(|ast| Dynamic::wrap(&self.ctx, ast))
        }
    }

    /// Retrieve the upper bound value or approximation for the i-th optimization objective.
    pub fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        unsafe {
            Z3_optimize_get_upper(self.ctx.z3_ctx.0, self.z3_opt, objective_id)
                .map(|ast| Dynamic::wrap(&self.ctx, ast))
        }
    }

    /// Register a model handler that is invoked for every incrementally improved model
    /// produced by the optimization process. Only one model handler can be registered within
    /// each optimization solver.
    ///
    /// Note that the [`Model`] instance received by the handler is always the same object,
    /// internally mutated by the solver. There is no risk of concurrent reads and writes; the
    /// model is only modified by the solver, running on the same thread as the handler. But
    /// to save each model returned by individual handler invocations, you need some kind
    /// of deep copy mechanism (otherwise all models that you'll save will just
    /// be the same model instance).
    pub fn set_model_handler<F: Fn(&Model) + 'static>(&self, callback: F) {
        /*
           Implementation notes: The C handler cannot be `Fn` (must be `fn`). As such,
           we instead register a single "global handler" (`global_model_callback`),
           and then forward the callback to the right handler saved within
           a thread local map. Because the callback will be called by the solver on the same
           thread as other Z3 methods, we know there won't be any concurrent access to these
           data structures and the handler will be present in the thread local map.
           To support interior mutability, we thus rely on `RefCell`, but we don't need
           additional synchronization. When the solver is dropped, we remove
           the handler from the thread local map.
        */

        self.clear_model_handler(); // First, remove any pre-existing handler.

        unsafe {
            // Make an "empty" model into which the result will be placed. The model lives
            // as long as the handler is registered.
            let model = Model::new_empty(&self.ctx);
            let z3_model = model.z3_mdl;

            // Register the given handler within the thread-local map so that it can be
            // accessed by the global handler.
            let id = THREAD_MODEL_HANDLER_COUNTER
                .with(|it| it.fetch_add(1, std::sync::atomic::Ordering::SeqCst));
            let callback: DynamicModelHandler = Box::new(callback);
            THREAD_MODEL_HANDLER_REGISTRY.with_borrow_mut(|map| {
                if let Some(_old) = map.insert(id, (callback, model)) {
                    panic!("Correctness violation: Callback with this ID was already registered.");
                }
            });

            // Register the callback within solver-specific map (to allow eventual deallocation).
            {
                let mut registered_id = self
                    .registered_model_handler
                    .try_borrow_mut()
                    .expect("Correctness violation: Concurrent access to handler registrations.");
                // Invariant: at this point, the `registered_id` should be `None`.
                *registered_id = Some(id);
            }

            // Register the callback internally within Z3
            Z3_optimize_register_model_eh(
                self.ctx.z3_ctx.0,
                self.z3_opt,
                z3_model,
                id as *mut c_void,
                Some(global_model_callback),
            );
        }
    }

    /// Clear a model handler previously set by [`Optimize::set_model_handler`]
    /// (assuming it exists).
    pub fn clear_model_handler(&self) {
        let mut registered_id = self
            .registered_model_handler
            .try_borrow_mut()
            .expect("Correctness violation: Concurrent access to handler registrations.");

        if let Some(id) = *registered_id {
            *registered_id = None;
            THREAD_MODEL_HANDLER_REGISTRY.with_borrow_mut(|map| {
                map.remove(&id);
            });
        }
    }
}

struct OptimizeIterator<T> {
    optimize: Optimize,
    ast: T,
    model_completion: bool,
}

impl<T: Solvable> Iterator for OptimizeIterator<T> {
    type Item = T::ModelInstance;

    fn next(&mut self) -> Option<Self::Item> {
        match self.optimize.check(&[]) {
            SatResult::Sat => {
                let model = self.optimize.get_model()?;
                let instance = self.ast.read_from_model(&model, self.model_completion)?;
                let counterexample = self.ast.generate_constraint(&instance);
                self.optimize.assert(&counterexample);
                Some(instance)
            }
            _ => None,
        }
    }
}

impl Default for Optimize {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Optimize {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_optimize_to_string(self.ctx.z3_ctx.0, self.z3_opt) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl fmt::Debug for Optimize {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl Drop for Optimize {
    fn drop(&mut self) {
        // Drop model handler from the global handler registry.
        self.clear_model_handler();

        unsafe { Z3_optimize_dec_ref(self.ctx.z3_ctx.0, self.z3_opt) };
    }
}

// Z3_optimize_translate was added in Z3 4.16.0. This feature gate is temporary
// and will be removed once the minimum supported Z3 version is bumped to 4.16.0.
#[cfg(feature = "z3_4_16")]
unsafe impl Translate for Optimize {
    fn translate(&self, dest: &Context) -> Optimize {
        unsafe {
            Optimize::wrap(
                dest,
                Z3_optimize_translate(self.ctx.z3_ctx.0, self.z3_opt, dest.z3_ctx.0).unwrap(),
            )
        }
    }
}

/// Creates a new [`Optimize`] with the same assertions, objectives, and parameters
/// as the original
// Requires the `z3_4_16` feature (Z3 >= 4.16.0). This gate is temporary and will
// be removed once the minimum supported Z3 version is bumped to 4.16.0.
#[cfg(feature = "z3_4_16")]
impl Clone for Optimize {
    fn clone(&self) -> Self {
        self.translate(&Context::thread_local())
    }
}

/// A rational non-negative weight for soft assertions.
/// This trait is sealed and cannot be implemented for types outside of
/// `z3`.
///
/// # See also:
///
/// - [`Optimize::assert_soft()`]
pub trait Weight: private::Sealed {
    /// This is purposefully distinct from `ToString` to allow
    /// specifying a `to_string` for tuples.
    fn to_string(&self) -> String;
}

macro_rules! impl_weight {
    ($($ty: ty),*) => {
        $(
            impl Weight for $ty {
                fn to_string(&self) -> String {
                    ToString::to_string(&self)
                }
            }

            impl Weight for ($ty, $ty) {
                fn to_string(&self) -> String {
                    format!("{} / {}", self.0, self.1)
                }
            }
        )*
    };
}

impl_weight! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}

#[cfg(feature = "num")]
impl Weight for BigInt {
    fn to_string(&self) -> String {
        assert_ne!(self.sign(), Sign::Minus);
        self.to_str_radix(10)
    }
}

#[cfg(feature = "num")]
impl Weight for BigUint {
    fn to_string(&self) -> String {
        self.to_str_radix(10)
    }
}

#[cfg(feature = "num")]
impl Weight for BigRational {
    fn to_string(&self) -> String {
        assert_ne!(self.numer().sign(), Sign::Minus);
        assert_ne!(self.denom().sign(), Sign::Minus);
        format!(
            "{} / {}",
            self.numer().to_str_radix(10),
            self.denom().to_str_radix(10)
        )
    }
}

macro_rules! impl_sealed {
    ($($ty: ty),*) => {
        mod private {
            #[allow(unused_imports)]
            use super::*;
            pub trait Sealed {}
            $(
                impl Sealed for $ty {}
                impl Sealed for ($ty, $ty) {}
            )*

            #[cfg(feature = "num")]
            impl Sealed for BigInt {}
            #[cfg(feature = "num")]
            impl Sealed for BigUint {}
            #[cfg(feature = "num")]
            impl Sealed for BigRational {}
        }
    };
}

impl_sealed! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}

/// The type of model handlers that can be registered in [`THREAD_MODEL_HANDLER_REGISTRY`].
type DynamicModelHandler = Box<dyn Fn(&Model) + 'static>;

thread_local! {
    /// A global thread safe registry for storing all model handlers that are currently registered.
    static THREAD_MODEL_HANDLER_REGISTRY: RefCell<BTreeMap<u32, (DynamicModelHandler, Model)>> = RefCell::new(BTreeMap::new());
    /// A utility counter used to assign unique IDs to model handlers in the thread model registry.
    static THREAD_MODEL_HANDLER_COUNTER: AtomicU32 = const { AtomicU32::new(0) };
}

/// A global model handler which is called via registrations from
/// [`Optimize::register_model_callback`] and dispatches the callback to
/// the respective anonymous functions.
extern "C" fn global_model_callback(ctx: *mut c_void) {
    // Invariant: global_model_callback is always called with `ctx` being an u32 callback ID,
    // as long as handlers are registered by our code.
    let id = ctx as u32;
    THREAD_MODEL_HANDLER_REGISTRY.with_borrow(|map| {
        let Some((callback, model)) = map.get(&id) else {
            panic!("Correctness violation: Callback `ID={id}` called but not registered.")
        };
        callback(model);
    });
}
