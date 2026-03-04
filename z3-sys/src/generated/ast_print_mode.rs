#[repr(u32)]
#[doc = "\\brief Z3 pretty printing modes (See #Z3_set_ast_print_mode).\n\n- Z3_PRINT_SMTLIB_FULL:   Print AST nodes in SMTLIB verbose format.\n- Z3_PRINT_LOW_LEVEL:     Print AST nodes using a low-level format.\n- Z3_PRINT_SMTLIB2_COMPLIANT: Print AST nodes in SMTLIB 2.x compliant format."]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_ast_print_mode {
    Z3_PRINT_SMTLIB_FULL = 0,
    Z3_PRINT_LOW_LEVEL = 1,
    Z3_PRINT_SMTLIB2_COMPLIANT = 2,
}
