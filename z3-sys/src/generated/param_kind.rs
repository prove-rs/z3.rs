#[repr(u32)]
#[doc = "\\brief The different kinds of parameters that can be associated with parameter sets.\n(see #Z3_mk_params).\n\n- Z3_PK_UINT integer parameters.\n- Z3_PK_BOOL boolean parameters.\n- Z3_PK_DOUBLE double parameters.\n- Z3_PK_SYMBOL symbol parameters.\n- Z3_PK_STRING string parameters.\n- Z3_PK_OTHER all internal parameter kinds which are not exposed in the API.\n- Z3_PK_INVALID invalid parameter."]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_param_kind {
    Z3_PK_UINT = 0,
    Z3_PK_BOOL = 1,
    Z3_PK_DOUBLE = 2,
    Z3_PK_SYMBOL = 3,
    Z3_PK_STRING = 4,
    Z3_PK_OTHER = 5,
    Z3_PK_INVALID = 6,
}
