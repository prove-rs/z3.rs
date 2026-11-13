use std::error::Error;
use std::ffi::{CStr, NulError};
use std::fmt;

use z3_sys::{ErrorCode, Z3_context, Z3_get_error_code, Z3_get_error_msg, Z3_set_error};

use crate::Context;

/// An error from a fallible Z3 operation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Z3Error {
    /// Z3 rejected the call.
    ///
    /// This crate disables Z3's default error handler (which exits the process), so Z3 signals
    /// failures only through an error code that must be checked after each call.
    Z3 { code: ErrorCode, message: String },
    /// A string passed to Z3 contained an interior NUL byte.
    InteriorNul(NulError),
}

impl fmt::Display for Z3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Z3Error::Z3 { code, message } => write!(f, "{message} ({code:?})"),
            Z3Error::InteriorNul(err) => err.fmt(f),
        }
    }
}

impl Error for Z3Error {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Z3Error::Z3 { .. } => None,
            Z3Error::InteriorNul(err) => Some(err),
        }
    }
}

impl From<NulError> for Z3Error {
    fn from(err: NulError) -> Self {
        Z3Error::InteriorNul(err)
    }
}

impl Context {
    /// Runs `f`, which should make a single Z3 call on the given context, and returns the error
    /// that call raised, if any.
    ///
    /// The error code is cleared first because some Z3 functions (e.g. `Z3_solver_from_string`)
    /// never reset it, and would otherwise appear to fail with an earlier call's error.
    pub(crate) fn checked<T>(&self, f: impl FnOnce(Z3_context) -> T) -> Result<T, Z3Error> {
        let ctx = self.z3_ctx.as_ptr();
        unsafe { Z3_set_error(ctx, ErrorCode::Ok) };
        let result = f(ctx);
        let code = unsafe { Z3_get_error_code(ctx) };
        if code == ErrorCode::Ok {
            return Ok(result);
        }
        let msg = unsafe { Z3_get_error_msg(ctx, code) };
        let message = if msg.is_null() {
            String::new()
        } else {
            unsafe { CStr::from_ptr(msg) }
                .to_string_lossy()
                .into_owned()
        };
        Err(Z3Error::Z3 { code, message })
    }

    /// Like [`Context::checked`], for Z3 calls that return null exactly when they fail.
    pub(crate) fn checked_some<T>(
        &self,
        f: impl FnOnce(Z3_context) -> Option<T>,
    ) -> Result<T, Z3Error> {
        self.checked(f)
            .map(|r| r.expect("Z3 returned null without reporting an error"))
    }
}
