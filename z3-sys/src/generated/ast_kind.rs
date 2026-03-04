#[repr(u32)]
#[doc = "\\brief\nThe different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.\n\n- Z3_APP_AST:            constant and applications\n- Z3_NUMERAL_AST:        numeral constants\n- Z3_VAR_AST:            bound variables\n- Z3_QUANTIFIER_AST:     quantifiers\n- Z3_SORT_AST:           sort\n- Z3_FUNC_DECL_AST:      function declaration\n- Z3_UNKNOWN_AST:        internal"]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_ast_kind {
    Z3_NUMERAL_AST = 0,
    Z3_APP_AST = 1,
    Z3_VAR_AST = 2,
    Z3_QUANTIFIER_AST = 3,
    Z3_SORT_AST = 4,
    Z3_FUNC_DECL_AST = 5,
    Z3_UNKNOWN_AST = 1000,
}
