use crate::ast::Borrow;
use crate::ast::regexp::Regexp;
use crate::ast::{Ast, Bool, Int, binop, unop, varop};
use crate::{Context, Sort, Symbol};
use std::ffi::{CStr, CString};
use z3_sys::*;

/// [`Ast`] node representing a string value.
pub struct String {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl String {
    /// Creates a new constant using the built-in string sort
    pub fn new_const<S: Into<Symbol>>(ctx: &Context, name: S) -> String {
        let sort = Sort::string(ctx);
        unsafe {
            Self::wrap(ctx, {
                Z3_mk_const(ctx.z3_ctx.0, name.into().as_z3_symbol(ctx), sort.z3_sort)
            })
        }
    }

    /// Creates a fresh constant using the built-in string sort
    pub fn fresh_const(ctx: &Context, prefix: &str) -> String {
        let sort = Sort::string(ctx);
        unsafe {
            Self::wrap(ctx, {
                let pp = CString::new(prefix).unwrap();
                let p = pp.as_ptr();
                Z3_mk_fresh_const(ctx.z3_ctx.0, p, sort.z3_sort)
            })
        }
    }

    /// Creates a Z3 constant string from a `&str`
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
    /// `z3::ast::String::from_str(&ctx, s).unwrap().as_string()` returns a
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
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// #
    /// let s = z3::ast::String::fresh_const(&ctx, "");
    ///
    /// solver.assert(
    ///     &s.at(&Int::from_u64(&ctx, 0))
    ///         ._eq(&z3::ast::String::from_str(&ctx, "a").unwrap())
    /// );
    /// assert_eq!(solver.check(), z3::SatResult::Sat);
    /// ```
    pub fn at(&self, index: &Int) -> Self {
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
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// # let solver = Solver::new(&ctx);
    /// #
    /// let s = String::from_str(&ctx, "abc").unwrap();
    /// let sub = String::fresh_const(&ctx, "");
    ///
    /// solver.assert(
    ///     &sub._eq(
    ///         &s.substr(
    ///             &Int::from_u64(&ctx, 1),
    ///             &Int::from_u64(&ctx, 2),
    ///         )
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
    pub fn substr(&self, offset: &Int, length: &Int) -> Self {
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
    }
}
