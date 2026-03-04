#[repr(u32)]
#[doc = "\\brief Z3 error codes (See #Z3_get_error_code).\n\n- Z3_OK:            No error.\n- Z3_SORT_ERROR:    User tried to build an invalid (type incorrect) AST.\n- Z3_IOB:           Index out of bounds.\n- Z3_INVALID_ARG:   Invalid argument was provided.\n- Z3_PARSER_ERROR:  An error occurred when parsing a string or file.\n- Z3_NO_PARSER:     Parser output is not available, that is, user didn't invoke #Z3_parse_smtlib2_string or #Z3_parse_smtlib2_file.\n- Z3_INVALID_PATTERN: Invalid pattern was used to build a quantifier.\n- Z3_MEMOUT_FAIL:   A memory allocation failure was encountered.\n- Z3_FILE_ACCESS_ERROR: A file could not be accessed.\n- Z3_INVALID_USAGE:   API call is invalid in the current state.\n- Z3_INTERNAL_FATAL: An error internal to Z3 occurred.\n- Z3_DEC_REF_ERROR: Trying to decrement the reference counter of an AST that was deleted or the reference counter was not initialized with #Z3_inc_ref.\n- Z3_EXCEPTION:     Internal Z3 exception. Additional details can be retrieved using #Z3_get_error_msg."]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_error_code {
    Z3_OK = 0,
    Z3_SORT_ERROR = 1,
    Z3_IOB = 2,
    Z3_INVALID_ARG = 3,
    Z3_PARSER_ERROR = 4,
    Z3_NO_PARSER = 5,
    Z3_INVALID_PATTERN = 6,
    Z3_MEMOUT_FAIL = 7,
    Z3_FILE_ACCESS_ERROR = 8,
    Z3_INTERNAL_FATAL = 9,
    Z3_INVALID_USAGE = 10,
    Z3_DEC_REF_ERROR = 11,
    Z3_EXCEPTION = 12,
}
