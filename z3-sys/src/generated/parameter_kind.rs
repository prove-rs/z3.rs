#[repr(u32)]
#[doc = "\\brief The different kinds of parameters that can be associated with function symbols.\n\\sa Z3_get_decl_num_parameters\n\\sa Z3_get_decl_parameter_kind\n\n- Z3_PARAMETER_INT is used for integer parameters.\n- Z3_PARAMETER_DOUBLE is used for double parameters.\n- Z3_PARAMETER_RATIONAL is used for parameters that are rational numbers.\n- Z3_PARAMETER_SYMBOL is used for parameters that are symbols.\n- Z3_PARAMETER_SORT is used for sort parameters.\n- Z3_PARAMETER_AST is used for expression parameters.\n- Z3_PARAMETER_FUNC_DECL is used for function declaration parameters.\n- Z3_PARAMETER_INTERNAL is used for parameters that are private to Z3. They cannot be accessed.\n- Z3_PARAMETER_ZSTRING is used for string parameters."]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_parameter_kind {
    Z3_PARAMETER_INT = 0,
    Z3_PARAMETER_DOUBLE = 1,
    Z3_PARAMETER_RATIONAL = 2,
    Z3_PARAMETER_SYMBOL = 3,
    Z3_PARAMETER_SORT = 4,
    Z3_PARAMETER_AST = 5,
    Z3_PARAMETER_FUNC_DECL = 6,
    Z3_PARAMETER_INTERNAL = 7,
    Z3_PARAMETER_ZSTRING = 8,
}
