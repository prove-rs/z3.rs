use std::error::Error as StdError;
use std::ffi::{CStr, NulError};
use std::fmt;

use z3_sys::{
    AstKind, DeclKind, ErrorCode, GoalPrec, SortKind, SymbolKind, Z3_context, Z3_get_error_code,
    Z3_get_error_msg, Z3_set_error, Z3_string,
};

use crate::Context;

/// An error from a fallible Z3 operation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// Z3 rejected the call.
    ///
    /// This crate disables Z3's default error handler (which exits the process), so Z3 signals
    /// failures only through an error code that must be checked after each call.
    Z3 { code: ErrorCode, message: String },
    /// A string passed to Z3 contained an interior NUL byte.
    InteriorNul(NulError),
    /// Z3 returned a null handle without setting an error code.
    ///
    /// Z3 should always report why a call failed, so this indicates a bug in Z3 or in this crate.
    NullHandle,
    /// A function was given a different number of arguments than its declaration's arity.
    ArityMismatch {
        /// The arity of the function declaration.
        expected: usize,
        /// The number of arguments supplied.
        actual: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Z3 { code, message } => write!(f, "{message} ({code:?})"),
            Error::InteriorNul(err) => err.fmt(f),
            Error::NullHandle => f.write_str("Z3 returned null without reporting an error"),
            Error::ArityMismatch { expected, actual } => {
                write!(f, "expected {expected} arguments, got {actual}")
            }
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Error::Z3 { .. } | Error::NullHandle | Error::ArityMismatch { .. } => None,
            Error::InteriorNul(err) => Some(err),
        }
    }
}

impl From<NulError> for Error {
    fn from(err: NulError) -> Self {
        Error::InteriorNul(err)
    }
}

/// A value returned by a Z3 call, and what [`Context::checked`] hands back for it on success.
///
/// Nullable handles (`Option<T>`) are unwrapped, and null becomes [`Error::NullHandle`]
/// (Z3 normally sets an error code when it returns null, which `checked` reports first).
/// Do not pass calls through `checked` for which null is a normal answer
/// (e.g. `Z3_model_get_const_interp`).
pub(crate) trait Z3Return {
    type Output;
    fn into_result(self) -> Result<Self::Output, Error>;
}

impl<T> Z3Return for Option<T> {
    type Output = T;
    fn into_result(self) -> Result<T, Error> {
        self.ok_or(Error::NullHandle)
    }
}

/// Return types that are passed through unchanged.
macro_rules! z3_return_as_is {
    ($($t:ty),* $(,)?) => {
        $(
            impl Z3Return for $t {
                type Output = $t;
                fn into_result(self) -> Result<$t, Error> {
                    Ok(self)
                }
            }
        )*
    };
}

// `i32` also covers `Z3_lbool`, and `u32` covers `c_uint`.
z3_return_as_is!(
    (),
    bool,
    i32,
    u32,
    u64,
    f64,
    Z3_string,
    AstKind,
    DeclKind,
    ErrorCode,
    GoalPrec,
    SortKind,
    SymbolKind,
);

impl Context {
    /// Runs `f`, which should make a single Z3 call on the given context, and returns its result,
    /// or the error that call raised.
    ///
    /// The error code is cleared first because some Z3 functions (e.g. `Z3_solver_from_string`)
    /// never reset it, and would otherwise appear to fail with an earlier call's error.
    pub(crate) fn checked<R: Z3Return>(
        &self,
        f: impl FnOnce(Z3_context) -> R,
    ) -> Result<R::Output, Error> {
        let ctx = self.z3_ctx.as_ptr();
        unsafe { Z3_set_error(ctx, ErrorCode::Ok) };
        let result = f(ctx);
        let code = unsafe { Z3_get_error_code(ctx) };
        if code == ErrorCode::Ok {
            return result.into_result();
        }
        let msg = unsafe { Z3_get_error_msg(ctx, code) };
        let message = if msg.is_null() {
            String::new()
        } else {
            unsafe { CStr::from_ptr(msg) }
                .to_string_lossy()
                .into_owned()
        };
        Err(Error::Z3 { code, message })
    }
}
