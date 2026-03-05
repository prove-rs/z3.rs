use core::ptr::NonNull;

use crate::Z3_error_code;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_symbol {
    _unused: [u8; 0],
}
/// Lisp-like symbol used to name types, constants, and functions.
/// A symbol can be created using string or integers.
///
/// # See also:
///
/// - [`Z3_get_symbol_int`]
/// - [`Z3_get_symbol_kind`]
/// - [`Z3_get_symbol_string`]
/// - [`Z3_mk_int_symbol`]
/// - [`Z3_mk_string_symbol`]
pub type Z3_symbol = NonNull<_Z3_symbol>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_literals {
    _unused: [u8; 0],
}

pub type Z3_literals = NonNull<_Z3_literals>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_config {
    _unused: [u8; 0],
}
/// Configuration object used to initialize logical contexts.
pub type Z3_config = NonNull<_Z3_config>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_context {
    _unused: [u8; 0],
}
/// Manager of all other Z3 objects, global configuration options, etc.
pub type Z3_context = NonNull<_Z3_context>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_sort {
    _unused: [u8; 0],
}
/// Kind of AST used to represent types.
pub type Z3_sort = NonNull<_Z3_sort>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_func_decl {
    _unused: [u8; 0],
}
/// Kind of AST used to represent function symbols.
pub type Z3_func_decl = NonNull<_Z3_func_decl>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_ast {
    _unused: [u8; 0],
}
/// Abstract Syntax Tree node. That is, the data structure used in Z3
/// to represent terms, formulas, and types.
pub type Z3_ast = NonNull<_Z3_ast>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_app {
    _unused: [u8; 0],
}
/// Kind of AST used to represent function applications.
pub type Z3_app = NonNull<_Z3_app>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_pattern {
    _unused: [u8; 0],
}
/// Kind of AST used to represent pattern and multi-patterns used
/// to guide quantifier instantiation.
pub type Z3_pattern = NonNull<_Z3_pattern>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_model {
    _unused: [u8; 0],
}
/// Model for the constraints inserted into the logical context.
pub type Z3_model = NonNull<_Z3_model>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_constructor {
    _unused: [u8; 0],
}
/// Type constructor for a (recursive) datatype.
pub type Z3_constructor = NonNull<_Z3_constructor>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_constructor_list {
    _unused: [u8; 0],
}
/// List of constructors for a (recursive) datatype.
pub type Z3_constructor_list = NonNull<_Z3_constructor_list>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_params {
    _unused: [u8; 0],
}
/// Parameter set used to configure many components such as:
/// simplifiers, tactics, solvers, etc.
pub type Z3_params = NonNull<_Z3_params>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_param_descrs {
    _unused: [u8; 0],
}
/// Provides a collection of parameter names, their types,
/// default values and documentation strings. Solvers, tactics,
/// and other objects accept different collection of parameters.
pub type Z3_param_descrs = NonNull<_Z3_param_descrs>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_parser_context {
    _unused: [u8; 0],
}
/// Context for incrementally parsing SMTLIB2 strings.
pub type Z3_parser_context = NonNull<_Z3_parser_context>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_goal {
    _unused: [u8; 0],
}
/// Set of formulas that can be solved and/or transformed using
/// tactics and solvers.
pub type Z3_goal = NonNull<_Z3_goal>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_tactic {
    _unused: [u8; 0],
}
/// Basic building block for creating custom solvers for specific
/// problem domains.
pub type Z3_tactic = NonNull<_Z3_tactic>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_simplifier {
    _unused: [u8; 0],
}
/// Simplifier object.
pub type Z3_simplifier = NonNull<_Z3_simplifier>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_probe {
    _unused: [u8; 0],
}
/// Function/predicate used to inspect a goal and collect information
/// that may be used to decide which solver and/or preprocessing step
/// will be used.
pub type Z3_probe = NonNull<_Z3_probe>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_stats {
    _unused: [u8; 0],
}
/// Statistical data for a solver.
pub type Z3_stats = NonNull<_Z3_stats>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_solver {
    _unused: [u8; 0],
}
/// (Incremental) solver, possibly specialized by a particular
/// tactic or logic.
pub type Z3_solver = NonNull<_Z3_solver>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_solver_callback {
    _unused: [u8; 0],
}
/// Callback object for user-defined solver propagation.
pub type Z3_solver_callback = NonNull<_Z3_solver_callback>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_ast_vector {
    _unused: [u8; 0],
}
/// Vector of [`Z3_ast`] objects.
pub type Z3_ast_vector = NonNull<_Z3_ast_vector>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_ast_map {
    _unused: [u8; 0],
}
/// Mapping from [`Z3_ast`] to [`Z3_ast`] objects.
pub type Z3_ast_map = NonNull<_Z3_ast_map>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_apply_result {
    _unused: [u8; 0],
}
/// Collection of subgoals resulting from applying of a tactic
/// to a goal.
pub type Z3_apply_result = NonNull<_Z3_apply_result>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_func_interp {
    _unused: [u8; 0],
}
/// Interpretation of a function in a model.
pub type Z3_func_interp = NonNull<_Z3_func_interp>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_func_entry {
    _unused: [u8; 0],
}
/// Representation of the value of a [`Z3_func_interp`]
/// at a particular point.
pub type Z3_func_entry = NonNull<_Z3_func_entry>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_fixedpoint {
    _unused: [u8; 0],
}
/// Context for the recursive predicate solver.
pub type Z3_fixedpoint = NonNull<_Z3_fixedpoint>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_optimize {
    _unused: [u8; 0],
}
/// Context for solving optimization queries.
pub type Z3_optimize = NonNull<_Z3_optimize>;

#[doc(hidden)]
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct _Z3_rcf_num {
    _unused: [u8; 0],
}
pub type Z3_rcf_num = NonNull<_Z3_rcf_num>;

/// Z3 string type. It is just an alias for `const char *`.
pub type Z3_string = *const ::core::ffi::c_char;

pub type Z3_string_ptr = *mut Z3_string;

pub const Z3_L_FALSE: Z3_lbool = -1;
pub const Z3_L_UNDEF: Z3_lbool = 0;
pub const Z3_L_TRUE: Z3_lbool = 1;

/// Lifted Boolean type: `false`, `undefined`, `true`.
pub type Z3_lbool = i32;

/// Z3 custom error handler (See [`Z3_set_error_handler`]).
pub type Z3_error_handler =
    ::core::option::Option<unsafe extern "C" fn(c: Z3_context, e: Z3_error_code)>;

/// The following utilities allows adding user-defined domains.
pub type Z3_fixedpoint_reduce_assign_callback_fptr = ::core::option::Option<
    unsafe extern "C" fn(
        arg1: *mut ::core::ffi::c_void,
        arg2: Z3_func_decl,
        arg3: ::core::ffi::c_uint,
        arg4: *const Z3_ast,
        arg5: ::core::ffi::c_uint,
        arg6: *const Z3_ast,
    ),
>;
pub type Z3_fixedpoint_reduce_app_callback_fptr = ::core::option::Option<
    unsafe extern "C" fn(
        arg1: *mut ::core::ffi::c_void,
        arg2: Z3_func_decl,
        arg3: ::core::ffi::c_uint,
        arg4: *const Z3_ast,
        arg5: *mut Z3_ast,
    ),
>;

pub type Z3_fixedpoint_new_lemma_eh = ::core::option::Option<
    unsafe extern "C" fn(
        state: *mut ::core::ffi::c_void,
        lemma: Z3_ast,
        level: ::core::ffi::c_uint,
    ),
>;
pub type Z3_fixedpoint_predecessor_eh =
    ::core::option::Option<unsafe extern "C" fn(state: *mut ::core::ffi::c_void)>;
pub type Z3_fixedpoint_unfold_eh =
    ::core::option::Option<unsafe extern "C" fn(state: *mut ::core::ffi::c_void)>;

/// Pointer to a C string (same underlying type as [`Z3_string`] but used as output).
pub type Z3_char_ptr = *const ::core::ffi::c_char;

/// Callback invoked when a new scope is pushed during solver propagation.
pub type Z3_push_eh = ::core::option::Option<
    unsafe extern "C" fn(ctx: *mut ::core::ffi::c_void, cb: Z3_solver_callback),
>;

/// Callback invoked when scopes are popped during solver propagation.
pub type Z3_pop_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        cb: Z3_solver_callback,
        num_scopes: ::core::ffi::c_uint,
    ),
>;

/// Callback invoked to create a fresh user context for a new solver thread.
pub type Z3_fresh_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        new_context: Z3_context,
    ) -> *mut ::core::ffi::c_void,
>;

/// Callback invoked when a variable is fixed during solver propagation.
pub type Z3_fixed_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        cb: Z3_solver_callback,
        t: Z3_ast,
        value: Z3_ast,
    ),
>;

/// Callback invoked when all remaining assignments are final during solver propagation.
pub type Z3_final_eh = ::core::option::Option<
    unsafe extern "C" fn(ctx: *mut ::core::ffi::c_void, cb: Z3_solver_callback),
>;

/// Callback invoked when two terms are equated during solver propagation.
pub type Z3_eq_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        cb: Z3_solver_callback,
        s: Z3_ast,
        t: Z3_ast,
    ),
>;

/// Callback invoked when a new term is created during solver propagation.
pub type Z3_created_eh = ::core::option::Option<
    unsafe extern "C" fn(ctx: *mut ::core::ffi::c_void, cb: Z3_solver_callback, t: Z3_ast),
>;

/// Callback invoked when a clause is learned by the solver.
pub type Z3_on_clause_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        proof_hint: Z3_ast,
        n: ::core::ffi::c_uint,
        deps: *const ::core::ffi::c_uint,
        literals: Z3_ast_vector,
    ),
>;

/// Callback invoked when the solver makes a decision during propagation.
pub type Z3_decide_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        cb: Z3_solver_callback,
        t: Z3_ast,
        idx: ::core::ffi::c_uint,
        phase: bool,
    ),
>;

/// Callback invoked on binding during solver propagation; returns whether to keep the binding.
pub type Z3_on_binding_eh = ::core::option::Option<
    unsafe extern "C" fn(
        ctx: *mut ::core::ffi::c_void,
        cb: Z3_solver_callback,
        q: Z3_ast,
        inst: Z3_ast,
    ) -> bool,
>;

/// Callback invoked when an optimization model is found.
pub type Z3_model_eh = ::core::option::Option<unsafe extern "C" fn(ctx: *mut ::core::ffi::c_void)>;
