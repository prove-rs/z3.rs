#[repr(u32)]
#[doc = "\\brief The different kinds of symbol.\nIn Z3, a symbol can be represented using integers and strings (See #Z3_get_symbol_kind).\n\n\\sa Z3_mk_int_symbol\n\\sa Z3_mk_string_symbol"]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_symbol_kind {
    Z3_INT_SYMBOL = 0,
    Z3_STRING_SYMBOL = 1,
}
