#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(clippy::unreadable_literal)]

#[macro_use]
extern crate log;

#[macro_use]
extern crate lazy_static;

extern crate z3_sys;

use std::ffi::CString;
use std::sync::Mutex;
use z3_sys::*;

pub mod ast;
mod config;
mod context;
mod func_decl;
mod model;
mod optimize;
mod solver;
mod sort;
mod symbol;

// Z3 appears to be only mostly-threadsafe, a few initializers
// and such race; so we mutex-guard all access to the library.
lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

/// Configuration used to initialize [logical contexts].
///
/// [logical contexts]: struct.Context.html
pub struct Config {
    kvs: Vec<(CString, CString)>,
    z3_cfg: Z3_config,
}

/// Manager of all other Z3 objects, global configuration options, etc.
///
/// An application may use multiple Z3 contexts. Objects created in one context
/// cannot be used in another one. However, several objects may be "translated" from
/// one context to another. It is not safe to access Z3 objects from multiple threads.
/// The only exception is the method [`interrupt()`] that can be used to interrupt a long
/// computation.
///
/// # Examples:
///
/// Creating a context with the default configuration:
///
/// ```
/// use z3::{Config, Context};
/// let cfg = Config::new();
/// let ctx = Context::new(&cfg);
/// ```
///
/// [`interrupt()`]: #method.interrupt
pub struct Context {
    z3_ctx: Z3_context,
}

/// Symbols are used to name several term and type constructors.
pub enum Symbol {
    Int(u32),
    String(String),
}

/// Sorts represent the various 'types' of [`Ast`s](trait.Ast.html).
pub struct Sort<'ctx> {
    ctx: &'ctx Context,
    z3_sort: Z3_sort,
}

/// (Incremental) solver, possibly specialized by a particular tactic or logic.
pub struct Solver<'ctx> {
    ctx: &'ctx Context,
    z3_slv: Z3_solver,
}

/// Model for the constraints inserted into the logical context.
pub struct Model<'ctx> {
    ctx: &'ctx Context,
    z3_mdl: Z3_model,
}

/// Context for solving optimization queries.
pub struct Optimize<'ctx> {
    ctx: &'ctx Context,
    z3_opt: Z3_optimize,
}

/// Function declaration. Every constant and function have an associated declaration.
///
/// The declaration assigns a name, a sort (i.e., type), and for function
/// the sort (i.e., type) of each of its arguments. Note that, in Z3,
/// a constant is a function with 0 arguments.
pub struct FuncDecl<'ctx> {
    ctx: &'ctx Context,
    z3_func_decl: Z3_func_decl,
}
