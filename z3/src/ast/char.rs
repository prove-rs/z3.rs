use crate::ast::string::String as Z3String;
use crate::ast::{Ast, BV, Bool, Int, binop, unop};
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
            Z3String::wrap(
                &self.ctx,
                Z3_mk_seq_unit(self.ctx.z3_ctx.0, self.z3_ast).unwrap(),
            )
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SatResult, Solver};

    #[test]
    fn test_from_char_is_digit() {
        let solver = Solver::new();
        solver.assert(Char::from_char('5').is_digit());
        assert_eq!(solver.check(), SatResult::Sat);

        let solver = Solver::new();
        solver.assert(Char::from_char('A').is_digit());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_from_u32_eq() {
        let solver = Solver::new();
        solver.assert(Char::from_u32('z' as u32).eq(Char::from_char('z')));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn test_new_const_and_fresh_const() {
        let solver = Solver::new();
        let a = Char::new_const("a");
        let b = Char::fresh_const("b");
        solver.assert(a.eq(b));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn test_to_int_roundtrip() {
        // 'A' has code point 65; to_int should equal Int 65.
        let solver = Solver::new();
        let a = Char::from_char('A');
        solver.assert(a.to_int().eq(crate::ast::Int::from_i64(65)));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn test_char_le() {
        let solver = Solver::new();
        solver.assert(Char::from_char('a').char_le(Char::from_char('z')));
        assert_eq!(solver.check(), SatResult::Sat);

        let solver = Solver::new();
        solver.assert(Char::from_char('z').char_le(Char::from_char('a')));
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_to_string_length_one() {
        // to_string() wraps the char in a unit string of length 1.
        let solver = Solver::new();
        let s = Char::from_char('x').to_string();
        solver.assert(s.length().eq(crate::ast::Int::from_i64(1)));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn test_from_bv_roundtrip() {
        // from_bv(to_bv(c)) should equal c.
        let solver = Solver::new();
        let c = Char::from_char('B');
        let roundtrip = Char::from_bv(&c.to_bv());
        solver.assert(c.eq(roundtrip));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn test_dynamic_as_char() {
        use crate::ast::Dynamic;
        let c = Char::from_char('X');
        let dyn_c = Dynamic::from_ast(&c);
        assert!(dyn_c.as_char().is_some());
        assert!(dyn_c.as_int().is_none());
    }
}
