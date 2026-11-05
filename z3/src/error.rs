use std::error::Error;
use std::ffi::{CStr, NulError};
use std::fmt;

use z3_sys::{ErrorCode, Z3_get_error_code, Z3_get_error_msg, Z3_set_error};

use crate::Context;

/// An error reported by Z3.
///
/// This crate disables Z3's default error handler (which exits the process), so Z3 signals
/// failures only through an error code that must be checked after each call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Z3Error {
    pub code: ErrorCode,
    pub message: String,
}

impl fmt::Display for Z3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({:?})", self.message, self.code)
    }
}

impl Error for Z3Error {}

impl From<NulError> for Z3Error {
    fn from(err: NulError) -> Self {
        Z3Error {
            code: ErrorCode::InvalidArg,
            message: err.to_string(),
        }
    }
}

impl Context {
    /// Runs `f`, which should make a single Z3 call on this context, and returns the error that
    /// call raised, if any.
    ///
    /// The error code is cleared first because some Z3 functions (e.g. `Z3_solver_from_string`)
    /// never reset it, and would otherwise appear to fail with an earlier call's error.
    pub(crate) fn checked<T>(&self, f: impl FnOnce() -> T) -> Result<T, Z3Error> {
        let ctx = self.z3_ctx.as_ptr();
        unsafe { Z3_set_error(ctx, ErrorCode::Ok) };
        let result = f();
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
        Err(Z3Error { code, message })
    }
}
