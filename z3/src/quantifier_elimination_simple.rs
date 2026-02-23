use crate::ast::{Ast, Bool};
use z3_sys::*;

/// Basic quantifier elimination using available Z3 functions.
#[derive(Debug)]
pub struct QuantifierElimination;

impl QuantifierElimination {
    /// Light quantifier elimination using Z3_qe_lite.
    pub fn lite(vars: &crate::AstVector, formula: &impl Ast) -> Bool {
        let ctx = formula.get_ctx();
        unsafe {
            Bool::wrap(
                ctx,
                Z3_qe_lite(ctx.z3_ctx.0, vars.z3_ast_vector, formula.get_z3_ast()).unwrap(),
            )
        }
    }
}