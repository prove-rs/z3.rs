// These files are pre-generated from the pinned Z3 source in z3-src/z3.
// To regenerate after bumping the z3-src submodule, run:
//   ./scripts/gen-bindings.sh
// Requires: cargo install bindgen-cli
#[allow(dead_code)]
mod ast_kind {
    include!("generated/ast_kind.rs");
}
#[allow(dead_code)]
mod ast_print_mode {
    include!("generated/ast_print_mode.rs");
}
#[allow(dead_code)]
mod decl_kind {
    include!("generated/decl_kind.rs");
}
#[allow(dead_code)]
mod error_code {
    include!("generated/error_code.rs");
}
#[allow(dead_code)]
mod goal_prec {
    include!("generated/goal_prec.rs");
}
#[allow(dead_code)]
mod param_kind {
    include!("generated/param_kind.rs");
}
#[allow(dead_code)]
mod parameter_kind {
    include!("generated/parameter_kind.rs");
}
#[allow(dead_code)]
mod sort_kind {
    include!("generated/sort_kind.rs");
}
#[allow(dead_code)]
mod symbol_kind {
    include!("generated/symbol_kind.rs");
}

pub use self::ast_kind::Z3_ast_kind;
pub use self::ast_print_mode::Z3_ast_print_mode;
pub use self::decl_kind::Z3_decl_kind;
pub use self::error_code::Z3_error_code;
pub use self::goal_prec::Z3_goal_prec;
pub use self::param_kind::Z3_param_kind;
pub use self::parameter_kind::Z3_parameter_kind;
pub use self::sort_kind::Z3_sort_kind;
pub use self::symbol_kind::Z3_symbol_kind;
