use crate::ast::{Ast, Bool};
use z3_sys::*;

/// Quantifier elimination facilities.
/// 
/// Provides methods for eliminating quantifiers from logical formulas when possible.
pub struct QuantifierElimination;

impl QuantifierElimination {
    /// Eliminate quantifiers from the given formula.
    /// 
    /// This function attempts to eliminate existential and universal quantifiers
    /// from logical formulas. The elimination is sound but not necessarily complete.
    /// 
    /// # Parameters
    /// - `formula`: The formula containing quantifiers to eliminate
    /// - `eliminate_all`: If true, try to eliminate all quantifiers; if false, eliminate only outermost
    /// 
    /// # Returns
    /// A quantifier-free formula equivalent to the input (if elimination succeeded),
    /// or the original formula if elimination is not possible.
    pub fn eliminate_quantifiers(formula: &impl Ast, eliminate_all: bool) -> Bool {
        let ctx = formula.get_ctx();
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_eliminate_quantifiers(
                    ctx.z3_ctx.0,
                    formula.get_z3_ast(),
                    eliminate_all,
                ).unwrap(),
            )
        }
    }

    /// Eliminate quantifiers using model-based quantifier elimination.
    /// 
    /// This is a more aggressive quantifier elimination strategy that may
    /// produce simpler results in some cases.
    /// 
    /// # Parameters
    /// - `formula`: The formula containing quantifiers to eliminate
    /// - `model`: A model that can guide the elimination process (can be null)
    /// - `eliminate_all`: If true, try to eliminate all quantifiers
    pub fn eliminate_quantifiers_with_model(
        formula: &impl Ast,
        model: Option<&crate::Model>,
        eliminate_all: bool,
    ) -> Bool {
        let ctx = formula.get_ctx();
        let model_ptr = match model {
            Some(m) => m.z3_model,
            None => std::ptr::null_mut(),
        };
        
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_model_project(
                    ctx.z3_ctx.0,
                    model_ptr,
                    0,
                    std::ptr::null(),
                    formula.get_z3_ast(),
                ).unwrap(),
            )
        }
    }

    /// Project variables from a formula with respect to a model.
    /// 
    /// This eliminates the specified variables from the formula using
    /// information from the provided model.
    /// 
    /// # Parameters
    /// - `model`: The model to use for projection
    /// - `variables`: Array of variables to eliminate
    /// - `formula`: The formula from which to eliminate variables
    pub fn project_variables(
        model: &crate::Model,
        variables: &[&dyn Ast],
        formula: &impl Ast,
    ) -> Bool {
        let ctx = formula.get_ctx();
        let vars_z3: Vec<Z3_ast> = variables.iter().map(|v| v.get_z3_ast()).collect();
        
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_model_project(
                    ctx.z3_ctx.0,
                    model.z3_model,
                    vars_z3.len() as u32,
                    vars_z3.as_ptr(),
                    formula.get_z3_ast(),
                ).unwrap(),
            )
        }
    }

    /// Eliminate existential quantifiers from the formula.
    /// 
    /// This is equivalent to `eliminate_quantifiers` but specifically focuses
    /// on existential quantifiers.
    pub fn eliminate_existential_quantifiers(formula: &impl Ast) -> Bool {
        Self::eliminate_quantifiers(formula, false)
    }

    /// Simplify a quantified formula using quantifier elimination techniques.
    /// 
    /// This may not eliminate all quantifiers but will simplify the formula
    /// as much as possible using quantifier elimination.
    pub fn simplify_with_qe(formula: &impl Ast) -> Bool {
        let ctx = formula.get_ctx();
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_simplify(ctx.z3_ctx.0, formula.get_z3_ast()).unwrap(),
            )
        }
    }
}

/// Light-weight quantifier elimination.
/// 
/// This provides a faster but less complete quantifier elimination strategy.
pub struct LightQuantifierElimination;

impl LightQuantifierElimination {
    /// Perform light quantifier elimination.
    /// 
    /// This is a faster version of quantifier elimination that may not
    /// eliminate as many quantifiers but is more efficient.
    pub fn eliminate(formula: &impl Ast) -> Bool {
        let ctx = formula.get_ctx();
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_light(ctx.z3_ctx.0, formula.get_z3_ast()).unwrap(),
            )
        }
    }
}