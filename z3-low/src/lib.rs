// Generated C API docs don't conform to Rust doc formatting conventions.
#![allow(clippy::doc_markdown)]
#![allow(clippy::doc_lazy_continuation)]

pub use ::z3_sys::types::*;

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Z3Error {
    err: Z3_error_code,
    msg: String,
}

impl Z3Error {
    fn new(ctx: Z3_context, err: Z3_error_code) -> Z3Error {
        let slice = unsafe { core::ffi::CStr::from_ptr(Z3_get_error_msg(ctx, err)) };
        let msg = slice.to_string_lossy().into_owned();
        Self { err, msg }
    }
}

impl core::fmt::Display for Z3Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Z3 error ({:?}): {}", self.err, self.msg)
    }
}

impl core::error::Error for Z3Error {}

#[cfg(not(feature = "bindgen"))]
include!("generated/functions.rs");

#[cfg(feature = "bindgen")]
include!(concat!(env!("OUT_DIR"), "/functions.rs"));

include!("functions_patched.rs");
