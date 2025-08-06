use crate::Context;
use crate::ast::Translate;
use crate::translate::RecoverSendable;

/// This struct provides a way to send z3 structures
/// ([`Ast`](crate::ast::Ast), [`Solver`], etc)
/// to another thread safely. It wraps the Z3 structure you would like to send
/// combined with the [`Context`] it is associated with.
///
/// This structure is [`Send`] and so can be sent to another thread and then used to
/// recover the original Z3 structure by calling `translate` on it. The `translate`
/// method is furnished by implementations of [`RecoverSendable`] for specific inner
/// data types. The library implements this for all [`Ast`] types as well as [`Solver`],
/// [`Optimize`], and [`Model`], as well as for [`Vec`]s and slices of any type implementing
/// [`RecoverSendable`].
///
/// The advantage of implementing it for these collections is that it allows one to use
/// the same temporary context for a whole collection of objects, reducing the amount of
/// overhead in cases where lots of small pieces data needs to be passed to a thread.
///
/// Users wanting to allow their own structure wrapping Z3 types to work with [`SendableHandle`]
/// may unsafely construct a [`SendableHandle`] with [`SendableHandle::new`], and should
/// heed the notes below:
///
/// # Safety notes
///
/// The [`Context`] in this struct must NOT be referenced anywhere else. The safety of this structure
/// relies on the assumption that it holds the ONLY references to this [`Context`] AND to
/// the Z3 structures contained inside. It also assumes that all structures contained inside
/// are associated with its [`Context`].
///
/// This invariant is upheld in all constructions of this type in z3rs by ensuring the following:
/// * [`SendableHandle`] is always constructed with a new [`Context`]
/// * This [Context] is moved into the structure and no reference/copy of it is kept elsewhere
/// * All items of the struct are private and are only used to `translate` back into normal z3
///   structs
#[derive(Debug)]
pub struct SendableHandle<T> {
    pub(super) ctx: Context,
    pub(super) data: T,
}

impl<T> SendableHandle<T> {
    /// Make a Sendable handle for a Z3 structure. This is exposed to allow implementation of Sendable
    /// handles for user-provided types that use Z3 types. Most users will not need to use this
    /// function, as the built-in Z3 types already have ways to construct it.
    ///
    /// # Safety
    ///
    /// The [`Context`] given to this function must NOT be referenced anywhere else. The safety of this structure
    /// relies on the assumption that it holds the ONLY references to this [`Context`] AND to
    /// the Z3 structures contained inside. It also assumes that all structures contained inside
    /// are associated with its [`Context`].
    ///
    /// This invariant is upheld in all constructions of this type in z3.rs by ensuring the following:
    /// * [`SendableHandle`] is always constructed with a new [`Context`]
    /// * This [Context] is moved into the structure and no reference/copy of it is kept elsewhere
    /// * All items of the struct are private and are only used to `translate` back into normal z3
    ///   structs
    pub unsafe fn new(ctx: Context, ast: T) -> Self {
        Self { ctx, data: ast }
    }
}

unsafe impl<T> Send for SendableHandle<T> {}

unsafe impl<T: Translate> RecoverSendable for SendableHandle<Vec<T>> {
    type Target = Vec<T>;

    fn recover(&self, ctx: &Context) -> Self::Target {
        self.data.iter().map(|t| t.translate(ctx)).collect()
    }
}
