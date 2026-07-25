use std::ffi::c_void;
use std::ptr::NonNull;

/// Heap-pins FFI callback state and manages its lifetime via Rust ownership.
///
/// Allocate with [`FfiState::new`], hand the pointer to Z3 via [`FfiState::into_raw`],
/// and reclaim ownership with [`FfiState::from_raw`] when the registration should be
/// torn down. Dropping the reclaimed [`FfiState`] frees the allocation.
pub(crate) struct FfiState<S: 'static>(NonNull<S>);

impl<S: 'static> FfiState<S> {
    pub fn new(state: S) -> Self {
        // SAFETY: Box::into_raw is always non-null.
        FfiState(unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(state))) })
    }

    /// Consume this wrapper and return an opaque pointer suitable for passing to Z3 as `ctx`.
    ///
    /// The allocation is **not** freed automatically after this call.
    /// Reclaim ownership with [`Self::from_raw`] to restore drop semantics.
    pub fn into_raw(self) -> *mut c_void {
        let ptr = self.0.as_ptr().cast::<c_void>();
        std::mem::forget(self);
        ptr
    }

    /// Restore ownership of a pointer previously returned by [`Self::into_raw`].
    ///
    /// # Safety
    /// `ptr` must originate from `FfiState::<S>::into_raw` for the same `S`,
    /// and must not be used again after this call returns.
    pub unsafe fn from_raw(ptr: *mut c_void) -> Self {
        // SAFETY: ptr came from Box::into_raw (non-null) and is correctly typed.
        FfiState(unsafe { NonNull::new_unchecked(ptr.cast::<S>()) })
    }

    /// Borrow the state from a raw pointer without taking ownership.
    ///
    /// # Safety
    /// `ptr` must originate from `FfiState::<S>::into_raw` for the same `S`,
    /// and the state must still be live (i.e., not yet reclaimed by `from_raw`).
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
