use crate::ast::{Ast, Bool};
use crate::{Context, Statistics, Params};
use std::ffi::CString;
use z3_sys::*;

/// Fixedpoint context for Horn clause solving.
/// 
/// Fixedpoint provides facilities for solving Horn clauses and recursive predicates.
/// It supports both bottom-up (Datalog) and top-down (PDR/IC3) solving strategies.
#[derive(Debug)]
pub struct Fixedpoint {
    pub(crate) ctx: Context,
    pub(crate) z3_fp: Z3_fixedpoint,
}

impl Drop for Fixedpoint {
    fn drop(&mut self) {
        unsafe {
            Z3_fixedpoint_dec_ref(self.ctx.z3_ctx.0, self.z3_fp);
        }
    }
}

impl Fixedpoint {
    /// Create a new fixedpoint context.
    pub fn new() -> Fixedpoint {
        let ctx = Context::thread_local();
        unsafe {
            let fp = Z3_mk_fixedpoint(ctx.z3_ctx.0);
            Z3_fixedpoint_inc_ref(ctx.z3_ctx.0, fp);
            Fixedpoint {
                ctx: ctx.clone(),
                z3_fp: fp,
            }
        }
    }

    /// Add a Horn clause rule to the fixedpoint context.
    /// 
    /// # Example
    /// ```ignore
    /// let fp = Fixedpoint::new();
    /// let p = Bool::new_const("p");
    /// let q = Bool::new_const("q");
    /// 
    /// // Add rule: p => q
    /// fp.add_rule(&p.implies(&q), None);
    /// ```
    pub fn add_rule(&self, rule: &impl Ast, name: Option<&str>) {
        unsafe {
            let name_sym = match name {
                Some(n) => {
                    let cname = CString::new(n).unwrap();
                    Z3_mk_string_symbol(self.ctx.z3_ctx.0, cname.as_ptr())
                },
                None => std::ptr::null_mut(),
            };
            Z3_fixedpoint_add_rule(self.ctx.z3_ctx.0, self.z3_fp, rule.get_z3_ast(), name_sym);
        }
    }

    /// Add a fact (ground assertion) to the fixedpoint context.
    pub fn add_fact(&self, pred: &impl Ast, args: &[&dyn Ast]) {
        let args_z3: Vec<Z3_ast> = args.iter().map(|a| a.get_z3_ast()).collect();
        unsafe {
            Z3_fixedpoint_add_fact(
                self.ctx.z3_ctx.0,
                self.z3_fp,
                pred.get_z3_ast(),
                args_z3.len() as u32,
                args_z3.as_ptr(),
            );
        }
    }

    /// Assert a formula in the fixedpoint context.
    pub fn assert(&self, axiom: &impl Ast) {
        unsafe {
            Z3_fixedpoint_assert(self.ctx.z3_ctx.0, self.z3_fp, axiom.get_z3_ast());
        }
    }

    /// Query the fixedpoint context for satisfiability.
    /// 
    /// Returns the result of the query (satisfiable, unsatisfiable, or unknown).
    pub fn query(&self, query: &impl Ast) -> Z3_lbool {
        unsafe { Z3_fixedpoint_query(self.ctx.z3_ctx.0, self.z3_fp, query.get_z3_ast()) }
    }

    /// Query the fixedpoint context with multiple relations.
    pub fn query_relations(&self, relations: &[&dyn Ast]) -> Z3_lbool {
        let relations_z3: Vec<Z3_ast> = relations.iter().map(|r| r.get_z3_ast()).collect();
        unsafe {
            Z3_fixedpoint_query_relations(
                self.ctx.z3_ctx.0,
                self.z3_fp,
                relations_z3.len() as u32,
                relations_z3.as_ptr(),
            )
        }
    }

    /// Get the answer substitution after a successful query.
    /// This provides the concrete values that make the query satisfiable.
    pub fn get_answer(&self) -> Option<Bool> {
        unsafe {
            let answer = Z3_fixedpoint_get_answer(self.ctx.z3_ctx.0, self.z3_fp);
            if answer.is_some() {
                Some(Bool::wrap(&self.ctx, answer.unwrap()))
            } else {
                None
            }
        }
    }

    /// Get the reason (core) for unsatisfiability after an unsuccessful query.
    pub fn get_reason_unknown(&self) -> String {
        unsafe {
            let reason = Z3_fixedpoint_get_reason_unknown(self.ctx.z3_ctx.0, self.z3_fp);
            std::ffi::CStr::from_ptr(reason).to_string_lossy().into_owned()
        }
    }

    /// Update a named parameter in the fixedpoint context.
    pub fn update_rule(&self, rule: &impl Ast, name: &str) {
        unsafe {
            let cname = CString::new(name).unwrap();
            let name_sym = Z3_mk_string_symbol(self.ctx.z3_ctx.0, cname.as_ptr());
            Z3_fixedpoint_update_rule(self.ctx.z3_ctx.0, self.z3_fp, rule.get_z3_ast(), name_sym);
        }
    }

    /// Get the number of levels explored during the last query.
    pub fn get_num_levels(&self) -> u32 {
        unsafe { Z3_fixedpoint_get_num_levels(self.ctx.z3_ctx.0, self.z3_fp) }
    }

    /// Get the cover (approximation) at a given level.
    pub fn get_cover_delta(&self, level: i32, predicate: &impl Ast) -> Option<Bool> {
        unsafe {
            let delta = Z3_fixedpoint_get_cover_delta(
                self.ctx.z3_ctx.0,
                self.z3_fp,
                level,
                predicate.get_z3_ast(),
            );
            if delta.is_some() {
                Some(Bool::wrap(&self.ctx, delta.unwrap()))
            } else {
                None
            }
        }
    }

    /// Add a cover for a predicate at a given level.
    pub fn add_cover(&self, level: i32, predicate: &impl Ast, property: &impl Ast) {
        unsafe {
            Z3_fixedpoint_add_cover(
                self.ctx.z3_ctx.0,
                self.z3_fp,
                level,
                predicate.get_z3_ast(),
                property.get_z3_ast(),
            );
        }
    }

    /// Get statistics about the last query.
    pub fn get_statistics(&self) -> Statistics {
        unsafe {
            Statistics::wrap(
                &self.ctx,
                Z3_fixedpoint_get_statistics(self.ctx.z3_ctx.0, self.z3_fp).unwrap(),
            )
        }
    }

    /// Set parameters for the fixedpoint context.
    pub fn set_params(&self, params: &Params) {
        unsafe {
            Z3_fixedpoint_set_params(self.ctx.z3_ctx.0, self.z3_fp, params.z3_params);
        }
    }

    /// Get the help string for fixedpoint parameters.
    pub fn get_help() -> String {
        let ctx = Context::thread_local();
        let fp = unsafe { Z3_mk_fixedpoint(ctx.z3_ctx.0) };
        unsafe {
            let help = Z3_fixedpoint_get_help(ctx.z3_ctx.0, fp);
            std::ffi::CStr::from_ptr(help).to_string_lossy().into_owned()
        }
    }

    /// Convert the fixedpoint context to a string representation.
    /// This includes all rules, facts, and assertions.
    pub fn to_string(&self) -> String {
        unsafe {
            let s = Z3_fixedpoint_to_string(self.ctx.z3_ctx.0, self.z3_fp, 0, std::ptr::null_mut());
            std::ffi::CStr::from_ptr(s).to_string_lossy().into_owned()
        }
    }

    /// Parse a fixedpoint problem from a string in SMT-LIB format.
    pub fn from_string(&self, s: &str) -> Result<(), String> {
        let cs = CString::new(s).map_err(|_| "String contains null byte")?;
        unsafe {
            let result = Z3_fixedpoint_from_string(self.ctx.z3_ctx.0, self.z3_fp, cs.as_ptr());
            match result {
                Some(_) => Ok(()),
                None => Err("Failed to parse fixedpoint from string".to_string()),
            }
        }
    }

    /// Parse a file containing a fixedpoint problem.
    pub fn from_file(&self, filename: &str) -> Result<(), String> {
        let cs = CString::new(filename).map_err(|_| "Filename contains null byte")?;
        unsafe {
            let result = Z3_fixedpoint_from_file(self.ctx.z3_ctx.0, self.z3_fp, cs.as_ptr());
            match result {
                Some(_) => Ok(()),
                None => Err("Failed to parse fixedpoint from file".to_string()),
            }
        }
    }

}

impl Default for Fixedpoint {
    fn default() -> Self {
        Self::new()
    }
}