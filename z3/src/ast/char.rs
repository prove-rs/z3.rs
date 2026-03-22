use crate::ast::string::String as Z3String;
use crate::ast::{Ast, Bool, Int, BV, binop, unop};
use crate::{Context, Sort, Symbol};
use std::ffi::CString;
use z3_sys::*;

/// [`Ast`] node representing a Unicode character value.
pub struct Char {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Char {
    /// Creates a new constant using the built-in character sort.
    pub fn new_const<S: Into<Symbol>>(name: S) -> Char {
        let ctx = &Context::thread_local();
        let sort = Sort::char();
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(), sort.z3_sort).unwrap()
            })
        }
    }

    /// Creates a fresh constant using the built-in character sort.
    pub fn fresh_const(prefix: &str) -> Char {
        let ctx = &Context::thread_local();
        let sort = Sort::char();
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                Z3_mk_fresh_const(ctx.z3_ctx.0, pp.as_ptr(), sort.z3_sort).unwrap()
            })
        }
    }

    /// Creates a character literal from a Unicode code point.
    pub fn from_u32(ch: u32) -> Char {
        let ctx = &Context::thread_local();
        unsafe { Self::wrap(ctx, Z3_mk_char(ctx.z3_ctx.0, ch).unwrap()) }
    }

    /// Creates a character from a `char` value.
    pub fn from_char(ch: char) -> Char {
        Self::from_u32(ch as u32)
    }

    /// Converts this character to a unit string (a `String` of length 1).
    pub fn to_string(&self) -> Z3String {
        unsafe {
            Z3String::wrap(&self.ctx, Z3_mk_seq_unit(self.ctx.z3_ctx.0, self.z3_ast).unwrap())
        }
    }

    unop! {
        /// Converts this character to its integer code point.
        to_int(Z3_mk_char_to_int, Int);
        /// Converts this character to a bit-vector code point.
        to_bv(Z3_mk_char_to_bv, BV);
        /// Returns a Bool that is true iff this character is an ASCII decimal digit.
        is_digit(Z3_mk_char_is_digit, Bool);
    }

    binop! {
        /// Returns a Bool that is true iff this character is ≤ the other (Unicode order).
        char_le(Z3_mk_char_le, Bool);
    }

    /// Creates a `Char` from a `BV` code point.
    pub fn from_bv(bv: &BV) -> Char {
        unsafe {
            Self::wrap(
                bv.get_ctx(),
                Z3_mk_char_from_bv(bv.get_ctx().z3_ctx.0, bv.get_z3_ast()).unwrap(),
            )
        }
    }
}
