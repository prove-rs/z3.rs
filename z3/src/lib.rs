#![allow(dead_code)]
#![allow(unused_variables)]

#[macro_use]
extern crate log;

#[macro_use]
extern crate lazy_static;

extern crate z3_sys;
extern crate libc;

use std::sync::Mutex;
use std::ffi::CString;
use z3_sys::*;

mod sort;
mod config;
mod context;
mod symbol;
mod ast;
mod solver;
mod optimize;
mod model;

// Z3 appears to be only mostly-threadsafe, a few initializers
// and such race; so we mutex-guard all access to the library.
lazy_static! {
    static ref Z3_MUTEX: Mutex<()> = Mutex::new(());
}

pub struct Config {
    kvs: Vec<(CString,CString)>,
    z3_cfg: Z3_config
}

pub struct Context {
    z3_ctx: Z3_context
}

pub struct Symbol<'ctx>
{
    ctx: &'ctx Context,
    cst: Option<CString>,
    z3_sym: Z3_symbol
}

pub struct Sort<'ctx>
{
    ctx: &'ctx Context,
    z3_sort: Z3_sort
}

pub struct Ast<'ctx>
{
    ctx: &'ctx Context,
    z3_ast: Z3_ast
}

pub struct Solver<'ctx>
{
    ctx: &'ctx Context,
    z3_slv: Z3_solver
}

pub struct Model<'ctx>
{
    ctx: &'ctx Context,
    z3_mdl: Z3_model
}

pub struct Optimize<'ctx>
{
    ctx: &'ctx Context,
    z3_opt: Z3_optimize
}

