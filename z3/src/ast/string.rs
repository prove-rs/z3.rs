use crate::ast::IntoAst;
use crate::ast::IntoAstCtx;
use crate::ast::regexp::Regexp;
use crate::ast::{Ast, Bool, Int, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::{CStr, CString};
use z3_macros::z3;
use z3_sys::*;

/// [`Ast`] node representing a string value.
pub struct String {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl String {
    /// Creates a new constant using the built-in string sort
    #[z3(Context::thread_local)]
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S) -> String {
        let sort = Sort::string_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol_in_ctx(ctx), sort.z3_sort)
            })
        }
    }

    /// Creates a fresh constant using the built-in string sort
    #[z3(Context::thread_local)]
    pub fn fresh_const(ctx: &Context, prefix: &str) -> String {
        let sort = Sort::string_in_ctx(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    /// Creates a Z3 constant string from a `&str`
    #[z3(Context::thread_local)]
    pub fn from_str(ctx: &Context, string: &str) -> Result<String, std::ffi::NulError> {
        let string = CString::new(string)?;
        Ok(unsafe {
            Self::wrap(ctx, {
                Z3_mk_string(ctx.z3_ctx.0, string.as_c_str().as_ptr())
            })
        })
    }

    /// Retrieves the underlying `std::string::String`
    ///
    /// If this is not a constant `z3::ast::String`, return `None`.
    ///
    /// Note that `to_string()` provided by `std::string::ToString` (which uses
    /// `std::fmt::Display`) returns an escaped string. In contrast,
    /// `z3::ast::String::from_str( s).unwrap().as_string()` returns a
    /// `String` equal to the original value.
    pub fn as_string(&self) -> Option<std::string::String> {
        let z3_ctx = self.get_ctx().z3_ctx.0;
        unsafe {
            let bytes = Z3_get_string(z3_ctx, self.get_z3_ast());
            if bytes.is_null() {
                None
            } else {
                Some(CStr::from_ptr(bytes).to_string_lossy().into_owned())
            }
        }
    }

    /// Retrieve the substring of length 1 positioned at `index`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Solver};
    /// # use z3::ast::{Ast as _, Int};
    /// #
    /// # let cfg = Config::new();
    /// #
    /// let s = z3::ast::String::fresh_const("");
    ///
    /// solver.assert(
    ///     &s.at(0)._eq("a")
    /// );
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn at<T: IntoAstCtx<Int>>(&self, index: T) -> Self {
        let index = index.into_ast_ctx(&self.ctx);
        unsafe {
            Self::wrap(
                &self.ctx,
                Z3_mk_seq_at(self.ctx.z3_ctx.0, self.z3_ast, index.z3_ast),
            )
        }
    }

    /// Retrieve the substring of length `length` starting at `offset`.
    ///
    /// # Examples
    /// ```
    /// # use z3::{Config, Context, Solver, SatResult};
    /// # use z3::ast::{Ast as _, Int, String};
    /// #
    /// # let solver = Solver::new();
    /// #
    /// let s = String::from_str("abc").unwrap();
    /// let sub = String::fresh_const( "");
    ///
    /// solver.assert(
    ///     &sub._eq(
    ///         &s.substr(1,2)
    ///     )
    /// );
    ///
    /// assert_eq!(solver.check(), SatResult::Sat);
    /// assert_eq!(
    ///     solver
    ///         .get_model()
    ///         .unwrap()
    ///         .eval(&sub, true)
    ///         .unwrap()
    ///         .as_string()
    ///         .unwrap()
    ///         .as_str(),
    ///     "bc",
    /// );
    /// ```
    pub fn substr<T: IntoAstCtx<Int>, R: IntoAstCtx<Int>>(&self, offset: T, length: R) -> Self {
        let offset = offset.into_ast_ctx(&self.ctx);
        let length = length.into_ast_ctx(&self.ctx);
        unsafe {
            Self::wrap(
                &self.ctx,
                Z3_mk_seq_extract(self.ctx.z3_ctx.0, self.z3_ast, offset.z3_ast, length.z3_ast),
            )
        }
    }

    /// Checks if this string matches a `z3::ast::Regexp`
    pub fn regex_matches(&self, regex: &Regexp) -> Bool {
        assert!(self.ctx == regex.ctx);
        unsafe {
            Bool::wrap(
                &self.ctx,
                Z3_mk_seq_in_re(self.ctx.z3_ctx.0, self.get_z3_ast(), regex.get_z3_ast()),
            )
        }
    }

    /// Greater than in lexicographic order (str.>  s1 s2)
    /// # Example
    /// ```
    /// use z3::{ast, Config, Context, Solver, Sort};
    /// use z3::ast::{Ast, String};
    ///
    /// let solver = Solver::new();
    ///
    /// let string1 = String::from_str("apple").unwrap();
    /// let string2 = String::from_str("apple juice").unwrap();
    ///
    /// solver.assert(&string1.str_gt("apple juice"));
    /// assert_eq!(solver.check(), z3::SatResult::Unsat);
    ///
    /// let solver = Solver::new();
    /// solver.assert(&string1.str_lt("apple juice"));
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn str_gt<T: IntoAst<Self>>(&self, other: T) -> Bool {
        let other = other.into_ast(self);
        other.str_lt(self)
    }

    /// Greater than or equal to in lexicographic order (str.>= s1 s2)
    /// Anything is greater or equal than itself (or less than equal itself).
    /// # Example
    /// ```
    /// use z3::{ast, Config, Context, Solver, Sort};
    /// use z3::ast::{Ast, String};
    ///
    /// let solver = Solver::new();
    ///
    /// let string1 = String::from_str("apple").unwrap();
    ///
    /// solver.assert(&string1.str_ge(&string1));
    /// solver.assert(&string1.str_le(&string1));
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn str_ge<T: IntoAst<Self>>(&self, other: T) -> Bool {
        let other = other.into_ast(self);
        other.str_le(self)
    }

    varop! {
        /// Appends the argument strings to `Self`
        concat(Z3_mk_seq_concat, String);
    }

    unop! {
        /// Gets the length of `Self`.
        length(Z3_mk_seq_length, Int);
    }

    binop! {
        /// Checks whether `Self` contains a substring
        contains(Z3_mk_seq_contains, Bool);
        /// Checks whether `Self` is a prefix of the argument
        prefix(Z3_mk_seq_prefix, Bool);
        /// Checks whether `Self` is a suffix of the argument
        suffix(Z3_mk_seq_suffix, Bool);
        /// Checks whether `Self` is less than the argument in lexicographic order (str.<  s1 s2)
        str_lt(Z3_mk_str_lt, Bool);
        /// Checks whether `Self` is less than or equal to the argument in lexicographic order (str.<= s1 s2)
        str_le(Z3_mk_str_le, Bool);
    }
}

impl<T: AsRef<str>> IntoAst<String> for T {
    fn into_ast(self, a: &String) -> String {
        String::from_str_in_ctx(&a.ctx, self.as_ref()).unwrap()
    }
}

impl<T: AsRef<str> + Clone> IntoAstCtx<String> for T {
    fn into_ast_ctx(self, ctx: &Context) -> String {
        String::from_str_in_ctx(ctx, self.as_ref()).unwrap()
    }
}
