use crate::Context;

#[cfg(feature = "synchronization")]
pub mod synchronization;

/// Represents types that depend on a [`Context`] and can be translated to another [`Context`].
///
/// # Safety
///
/// Implementations of this trait must ensure that the `translate` method
/// translates _all_ contained z3 data into the new `Context`
pub unsafe trait Translate {
    fn translate(&self, dest: &Context) -> Self;
}

unsafe impl<T: Translate> Translate for Vec<T> {
    fn translate(&self, dest: &Context) -> Self {
        self.iter().map(|t| t.translate(dest)).collect()
    }
}
