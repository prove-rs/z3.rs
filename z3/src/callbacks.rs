use std::ffi::c_void;
use std::ptr::NonNull;
use std::rc::Rc;

/// Reference-counted FFI callback state whose lifetime is managed by Rust ownership.
///
/// Allocate with [`FfiState::new`], hand the void pointer to Z3 via
/// `into_non_null().as_ptr().cast::<c_void>()`, and reclaim ownership with
/// [`FfiState::from_non_null`] when the registration should be torn down.
/// Dropping the reclaimed [`FfiState`] releases the registration's reference.
///
/// Callbacks must access the state through [`FfiState::retain_raw`], which takes an
/// additional reference for the duration of the call. This keeps the state alive if the
/// callback itself tears down the registration (e.g. by registering a replacement handler),
/// in which case the state is freed when the callback returns rather than while it is running.
pub(crate) struct FfiState<S: 'static>(NonNull<S>);

impl<S: 'static> FfiState<S> {
    pub fn new(state: S) -> Self {
        // SAFETY: Rc::into_raw is always non-null.
        FfiState(unsafe { NonNull::new_unchecked(Rc::into_raw(Rc::new(state)).cast_mut()) })
    }

    /// Consume this wrapper and return a typed non-null pointer.
    ///
    /// The reference is **not** released automatically after this call.
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

    /// Take a new strong reference to the state from an opaque pointer received from Z3.
    ///
    /// The returned [`Rc`] keeps the state alive even if the registration is released while
    /// it is held, so callbacks can safely replace or tear down their own registration.
    ///
    /// # Safety
    /// `ptr` must have originated from `FfiState::<S>::into_non_null().as_ptr().cast::<c_void>()`
    /// for the same `S`, and the state must still be live.
    pub unsafe fn retain_raw(ptr: *mut c_void) -> Rc<S> {
        let ptr = ptr.cast::<S>().cast_const();
        // SAFETY: caller guarantees ptr came from Rc::into_raw for this `S` and is still live,
        // so the strong count is at least one and incrementing it is sound.
        unsafe {
            Rc::increment_strong_count(ptr);
            Rc::from_raw(ptr)
        }
    }
}

impl<S: 'static> Drop for FfiState<S> {
    fn drop(&mut self) {
        // SAFETY: pointer was created by Rc::into_raw in Self::new, and this wrapper owns
        // exactly one strong reference.
        unsafe {
            drop(Rc::from_raw(self.0.as_ptr().cast_const()));
        }
    }
}
