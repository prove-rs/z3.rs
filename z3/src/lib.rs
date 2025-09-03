//! # Z3
//!
//! Z3 is a theorem prover [from Microsoft Research](https://github.com/Z3Prover/z3/).

#![allow(clippy::unreadable_literal)]
#![warn(clippy::doc_markdown)]
#![deny(missing_debug_implementations)]

use std::ffi::CString;
use z3_sys::*;
pub use z3_sys::{AstKind, GoalPrec, SortKind};

pub mod ast;
mod config;
mod context;
pub mod datatype_builder;
mod func_decl;
mod func_entry;
mod func_interp;
mod goal;
mod model;
mod ops;
mod optimize;
mod params;
mod pattern;
mod probe;
mod rec_func_decl;
mod solver;
mod sort;
mod statistics;
mod symbol;
mod tactic;
mod translate;
mod version;

pub use crate::params::{get_global_param, reset_all_global_params, set_global_param};
pub use crate::statistics::{StatisticsEntry, StatisticsValue};
pub use crate::translate::Translate;
pub use crate::translate::synchronization::*;
pub use crate::version::{Version, full_version, version};
pub use context::Context;
pub use datatype_builder::DatatypeAccessor;
pub use solver::Solvable;
/// Configuration used to initialize [logical contexts](Context).
///
/// # See also:
///
/// - [`Context::new()`]
#[derive(Debug)]
pub struct Config {
    kvs: Vec<(CString, CString)>,
    z3_cfg: Z3_config,
}

/// Handle that can be used to interrupt a computation from another thread.
///
/// # See also:
///
/// - [`Context::interrupt()`]
/// - [`Context::handle()`]
/// - [`ContextHandle::interrupt()`]
#[derive(PartialEq, Eq, Debug)]
pub struct ContextHandle<'ctx> {
    ctx: &'ctx Context,
}

/// Symbols are used to name several term and type constructors.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Symbol {
    Int(u32),
    String(String),
}

/// Sorts represent the various 'types' of [`Ast`s](ast::Ast).
//
// Note for in-crate users: Never construct a `Sort` directly; only use
// `Sort::new()` which handles Z3 refcounting properly.
pub struct Sort {
    ctx: Context,
    z3_sort: Z3_sort,
}

/// A struct to represent when two sorts are of different types.
#[derive(Debug)]
pub struct SortDiffers {
    left: Sort,
    right: Sort,
}

/// A struct to represent when an ast is not a function application.
#[derive(Debug)]
pub struct IsNotApp {
    kind: AstKind,
}

/// (Incremental) solver, possibly specialized by a particular tactic or logic.
//
// Note for in-crate users: Never construct a `Solver` directly; only use
// `Solver::new()` which handles Z3 refcounting properly.
pub struct Solver {
    ctx: Context,
    z3_slv: Z3_solver,
}

/// Model for the constraints inserted into the logical context.
//
// Note for in-crate users: Never construct a `Model` directly; only use
// `Model::new()` which handles Z3 refcounting properly.
pub struct Model {
    ctx: Context,
    z3_mdl: Z3_model,
}

/// Context for solving optimization queries.
//
// Note for in-crate users: Never construct an `Optimize` directly; only use
// `Optimize::new()` which handles Z3 refcounting properly.
pub struct Optimize {
    ctx: Context,
    z3_opt: Z3_optimize,
}

/// Function declaration. Every constant and function have an associated declaration.
///
/// The declaration assigns a name, a sort (i.e., type), and for function
/// the sort (i.e., type) of each of its arguments. Note that, in Z3,
/// a constant is a function with 0 arguments.
///
/// # See also:
///
/// - [`RecFuncDecl`]
//
// Note for in-crate users: Never construct a `FuncDecl` directly; only use
// `FuncDecl::new()` which handles Z3 refcounting properly.
pub struct FuncDecl {
    ctx: Context,
    z3_func_decl: Z3_func_decl,
}

/// Stores the interpretation of a function in a Z3 model.
/// <https://z3prover.github.io/api/html/classz3py_1_1_func_interp.html>
pub struct FuncInterp {
    ctx: Context,
    z3_func_interp: Z3_func_interp,
}

/// Store the value of the interpretation of a function in a particular point.
/// <https://z3prover.github.io/api/html/classz3py_1_1_func_entry.html>
pub struct FuncEntry {
    ctx: Context,
    z3_func_entry: Z3_func_entry,
}

/// Recursive function declaration. Every function has an associated declaration.
///
/// The declaration assigns a name, a return sort (i.e., type), and
/// the sort (i.e., type) of each of its arguments. This is the function declaration type
/// you should use if you want to add a definition to your function, recursive or not.
///
/// This struct can dereference into a [`FuncDecl`] to access its methods.
///
/// # See also:
///
/// - [`RecFuncDecl::add_def`]
// Note for in-crate users: Never construct a `RecFuncDecl` directly; only use
// `RecFuncDecl::new()` which handles Z3 refcounting properly.
pub struct RecFuncDecl {
    ctx: Context,
    z3_func_decl: Z3_func_decl,
}

pub use z3_sys::DeclKind;

/// Build a custom [datatype sort](DatatypeSort).
///
/// Example:
/// ```
/// # use z3::{ Config, Context, DatatypeAccessor, DatatypeBuilder, SatResult, Solver, Sort, ast::{Ast, Datatype, Int}};
/// # let cfg = Config::new();
/// # let ctx = Context::new(&cfg);
/// # let solver = Solver::new();
/// // Like Rust's Option<int> type
/// let option_int = DatatypeBuilder::new("OptionInt")
/// .variant("None", vec![])
/// .variant(
///     "Some",
///     vec![("value", DatatypeAccessor::Sort(Sort::int()))],
/// )
/// .finish();
///
/// // Assert x.is_none()
/// let x = Datatype::new_const("x", &option_int.sort);
/// solver.assert(&option_int.variants[0].tester.apply(&[&x]).as_bool().unwrap());
///
/// // Assert y == Some(3)
/// let y = Datatype::new_const("y", &option_int.sort);
/// let value = option_int.variants[1].constructor.apply(&[&Int::from_i64(3)]);
/// solver.assert(&y._eq(&value.as_datatype().unwrap()));
///
/// assert_eq!(solver.check(), SatResult::Sat);
/// let model = solver.get_model().unwrap();
///
/// // Get the value out of Some(3)
/// let ast = option_int.variants[1].accessors[0].apply(&[&y]);
/// assert_eq!(3, model.eval(&ast.as_int().unwrap(), true).unwrap().as_i64().unwrap());
/// ```
#[derive(Debug)]
pub struct DatatypeBuilder {
    ctx: Context,
    name: Symbol,
    constructors: Vec<(String, Vec<(String, DatatypeAccessor)>)>,
}

/// Inner variant for a custom [datatype sort](DatatypeSort).
#[derive(Debug)]
pub struct DatatypeVariant {
    pub constructor: FuncDecl,
    pub tester: FuncDecl,
    pub accessors: Vec<FuncDecl>,
}

/// A custom datatype sort.
#[derive(Debug)]
pub struct DatatypeSort {
    pub sort: Sort,
    pub variants: Vec<DatatypeVariant>,
}

/// Parameter set used to configure many components (simplifiers, tactics, solvers, etc).
pub struct Params {
    ctx: Context,
    z3_params: Z3_params,
}

/// Result of a satisfiability query.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// The query is unsatisfiable.
    Unsat,
    /// The query was interrupted, timed out or otherwise failed.
    Unknown,
    /// The query is satisfiable.
    Sat,
}

/// A pattern for quantifier instantiation, used to guide quantifier instantiation.
pub struct Pattern {
    ctx: Context,
    z3_pattern: Z3_pattern,
}

/// Collection of subgoals resulting from applying of a tactic to a goal.
#[derive(Clone, Debug)]
pub struct ApplyResult {
    ctx: Context,
    z3_apply_result: Z3_apply_result,
}

/// Basic building block for creating custom solvers for specific problem domains.
///
/// Z3 provides a variety of tactics, which can be queried via
/// [`Tactic::list_all()`]. Individual tactics can be created via
/// [`Tactic::new()`].
///
/// Various combinators are available to combine tactics:
///
/// - [`Tactic::repeat()`]
/// - [`Tactic::try_for()`]
/// - [`Tactic::and_then()`]
/// - [`Tactic::or_else()`]
/// - [`Tactic::probe_or_else()`]
/// - [`Tactic::when()`]
/// - [`Tactic::cond()`]
///
/// Finally, a solver utilizing a tactic can be created via
/// [`Tactic::solver()`].
pub struct Tactic {
    ctx: Context,
    z3_tactic: Z3_tactic,
}

/// Set of formulas that can be solved and/or transformed using tactics and solvers.
pub struct Goal {
    ctx: Context,
    z3_goal: Z3_goal,
}

/// Function/predicate used to inspect a goal and collect information
/// that may be used to decide which solver and/or preprocessing step
/// will be used.
///
/// Z3 provides a variety of probes, which can be queried via
/// [`Probe::list_all()`].
pub struct Probe {
    ctx: Context,
    z3_probe: Z3_probe,
}

/// Statistical data about a solver.
///
/// # See also:
///
/// - [`Optimize::get_statistics()`]
/// - [`Solver::get_statistics()`]
pub struct Statistics {
    ctx: Context,
    z3_stats: Z3_stats,
}

/// Runs the provided callback with all inner Z3 calls using the provided [`Context`].
///
/// Requires that the closure and return type be [`Send`] and [`Sync`] to prevent
/// mixing Z3 objects belonging to multiple [`Context`]s. If you need to move Z3 data
/// into or out of the closure, use [`PrepareSynchronized::synchronized()`].
/// # See also
///
/// [`with_z3_config`]
#[deprecated = "Use `with_z3_config` instead, which constructs a Context from a Config"]
pub fn with_z3_context<T: Fn() -> R + Send + Sync, R: Send + Sync>(
    ctx: &Context,
    callback: T,
) -> R {
    let old = Context::thread_local();
    Context::set_thread_local(ctx);
    let res = callback();
    Context::set_thread_local(&old);
    res
}

/// Runs the provided callback with all inner Z3 calls using a [`Context`] derived
/// from the provided [`Config`].
///
/// Requires that the closure and return type be [`Send`] and [`Sync`] to prevent
/// mixing Z3 objects belonging to multiple [`Context`]s. If you need to move Z3 data
/// into or out of the closure, use [`PrepareSynchronized::synchronized()`].
#[allow(deprecated)]
pub fn with_z3_config<T: Fn() -> R + Send + Sync, R: Send + Sync>(cfg: &Config, callback: T) -> R {
    with_z3_context(&Context::new(cfg), callback)
}
