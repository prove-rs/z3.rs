use std::ffi::c_void;
use std::ptr::NonNull;

/// Heap-pins FFI callback state and manages its lifetime via Rust ownership.
///
/// Allocate with [`FfiState::new`], hand the void pointer to Z3 via
/// `into_non_null().as_ptr().cast::<c_void>()`, and reclaim ownership with
/// [`FfiState::from_non_null`] when the registration should be torn down.
/// Dropping the reclaimed [`FfiState`] frees the allocation.
pub(crate) struct FfiState<S: 'static>(NonNull<S>);

impl<S: 'static> FfiState<S> {
    pub fn new(state: S) -> Self {
        // SAFETY: Box::into_raw is always non-null.
        FfiState(unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(state))) })
    }

    /// Consume this wrapper and return a typed non-null pointer.
    ///
    /// The allocation is **not** freed automatically after this call.
    /// Reclaim ownership with [`Self::from_non_null`] to restore drop semantics.
    /// Cast to `*mut c_void` only at the Z3 FFI call site via `.as_ptr().cast()`.
    pub fn into_non_null(self) -> NonNull<S> {
        let nn = self.0;
        std::mem::forget(self);
        nn
    }

    /// Restore ownership of a typed pointer previously returned by [`Self::into_non_null`].
    ///
    /// # Safety
    /// `ptr` must originate from `FfiState::<S>::into_non_null` for the same `S`,
    /// and must not be used again after this call returns.
    pub unsafe fn from_non_null(ptr: NonNull<S>) -> Self {
        FfiState(ptr)
    }

    /// Borrow the state from an opaque pointer received from Z3 without taking ownership.
    ///
    /// # Safety
    /// `ptr` must have originated from `FfiState::<S>::into_non_null().as_ptr().cast::<c_void>()`
    /// for the same `S`, and the state must still be live.
    pub unsafe fn borrow_raw<'a>(ptr: *mut c_void) -> &'a S {
        // SAFETY: caller guarantees ptr is valid, correctly typed, and live.
        unsafe { &*(ptr.cast::<S>()) }
    }
}

impl<S: 'static> Drop for FfiState<S> {
    fn drop(&mut self) {
        // SAFETY: pointer was created by Box::into_raw in Self::new; we have unique ownership.
        unsafe { drop(Box::from_raw(self.0.as_ptr())); }
    }
}
