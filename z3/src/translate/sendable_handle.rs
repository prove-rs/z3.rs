use crate::Context;
use crate::translate::Translate;

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
/// may construct a [`SendableHandle`] with [`SendableHandle::new`].
///
/// # Safety notes
///
/// This structure is safe to use, the following properties are guaranteed through rust's
/// type system and package structure. The discussion below is just to clarify the intent.
///
/// The safety of this structure relies on the safety of implementations of the [`Translate`] trait.
///
/// The [`Context`] in this struct must NOT be referenced anywhere else. The safety of this structure
/// relies on the assumption that it holds the ONLY references to this [`Context`] AND to
/// the Z3 structures contained inside. It also assumes that all structures contained inside
/// are associated with its [`Context`].
///
/// This invariant is upheld in by ensuring the following:
/// * [`SendableHandle`] can only be constructed outside this crate through [`SendableHandle::new`],
///   which provides a fresh [`Context`]
/// * Direct instantiations of [`SendableHandle`] in this crate always use a new [`Context`]
/// * All items of the struct are private and are only used to `translate` back into normal z3
///   structs
#[derive(Debug)]
pub struct SendableHandle<T> {
    /// Since [`Context`] is refcounted, we actually don't need to keep this around.
    /// I'm leaving it in here for clarity for the time being but might take it out.
    #[expect(unused)]
    pub(super) ctx: Context,
    pub(super) data: T,
}

impl<T: Translate> SendableHandle<T> {
    pub fn new(data: &T) -> Self {
        let ctx = Context::default();
        let data = data.translate(&ctx);
        Self { ctx, data }
    }
}

/// If we have a `SendableHandle<T>` where `T: Translate`, we can recover the original data
/// We only allow construction of `SendableHandle` with `T: Translate` as the inner date is
/// private to z3.rs, and we manually ensure that it is only constructed for such types.
impl<T: Translate> SendableHandle<T> {
    /// Unwrap the `SendableHandle` and return the inner data.
    pub fn recover(self, ctx: &Context) -> T {
        self.data.translate(ctx)
    }
}

/// Cloning a `SendableHandle` will create a new `Context` and translate the data into it.
/// This allows a handle to be easily sent to multiple threads without violating context
/// memory safety, at the expense of some extra cloning.
impl<T: Translate> Clone for SendableHandle<T> {
    fn clone(&self) -> Self {
        let ctx = Context::default();
        let data = self.data.translate(&ctx);
        Self { ctx, data }
    }
}

unsafe impl<T> Send for SendableHandle<T> {}
