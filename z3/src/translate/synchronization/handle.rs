use crate::Context;
use crate::translate::Translate;
use std::sync::Mutex;

/// This struct provides a way to send z3 structures
/// ([`Ast`](crate::ast::Ast), [`Solver`](crate::Solver), etc)
/// to another thread safely. It wraps the Z3 structure you would like to send
/// combined with the [`Context`] it is associated with.
///
/// This structure is [`Send`] and so can be sent to another thread and then used to
/// recover the original Z3 structure by calling [`recover`](Synchronized::recover) on it.
///
/// Users wanting to allow their own structure wrapping Z3 types to work with [`Synchronized`]
/// should implement the [`Translate`] trait to benefit from the blanket implementation.
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
/// * [`Synchronized`] can only be constructed outside this crate through [`Synchronized::new`],
///   which provides a fresh [`Context`]
/// * Direct instantiations of [`Synchronized`] in this crate always use a new [`Context`]
/// * All items of the struct are private and are only used to `translate` back into normal z3
///   structs
#[derive(Debug)]
pub struct Synchronized<T> {
    /// Since [`Context`] is refcounted, we actually don't need to keep this around.
    /// I'm leaving it in here for clarity for the time being but might take it out.
    #[expect(unused)]
    pub(super) ctx: Context,
    pub(super) data: Mutex<T>,
}

impl<T: Translate> Synchronized<T> {
    /// Creates a new handle that is [`Send`] and [`Sync`], allowing for easily moving
    /// your z3 structs to other threads.
    /// Data passed in here is `translate`'d into a one-off `Context` and is then put in a `Mutex`,
    /// allowing it to be moved and referenced across threads
    /// soundly. None of this effects the original data.
    pub fn new(data: &T) -> Self {
        let ctx = Context::default();
        let data = data.translate(&ctx);
        Self {
            ctx,
            data: Mutex::new(data),
        }
    }
}

/// A fully thread-safe wrapper for Z3 structures (other than [`Context`]). This wrapper
/// takes in a Z3 type (or a user-defined type that uses Z3 types) and translates its contents
/// into a private "singleton" [`Context`]. Since this [`Context`] is unused elsewhere, it is safe
/// to [`Send`] it and its contents to other threads AND to have [`Sync`] accesses across threads.
/// The safety of the [`Sync`] is upheld through an inner [`Mutex`].
///
/// Inner data can only be accessed through [`Synchronized::recover`], which translates the contents
/// for the given [`Context`].
///
/// Initializing this type (usually done through
/// [`PrepareSynchronized::synchronized`](crate::PrepareSynchronized::synchronized)
/// will allocate
/// a new [`Context`] and [`Translate`] the provided `T` into it. This involves a non-zero amount of
/// overhead; if you are creating thousands of [`Synchronized`], you will see a performance impact.
///
/// If you need to move/reference a lot of data between threads, put it in a [`Vec`], which also
/// implements [`PrepareSynchronized`](crate::PrepareSynchronized), which will only create one [`Context`]. You can also
/// implement [`Translate`] on your own types, which will then inherit from a blanket impl of
/// [`PrepareSynchronized`](crate::PrepareSynchronized) for [`Translate`]. Note that this will
/// only alleviate the overhead of
/// allocating many [`Context`]s. There is still the unavoidable overhead of a single [`Context`]
/// allocation and the actual translation.
///
/// See also:
///
/// [`PrepareSendable`](crate::PrepareSynchronized)
/// [`Translate`]
impl<T: Translate> Synchronized<T> {
    /// Unwrap the `SendableHandle`, translate its contents for the given [`Context`]
    /// and return the inner data.
    pub fn recover(&self, ctx: &Context) -> T {
        self.data.lock().unwrap().translate(ctx)
    }
}

/// Cloning a [`Synchronized`] will create a new [`Context`] and translate the data into it.
/// This allows a handle to be easily sent to multiple threads without violating context
/// memory safety, at the expense of some extra cloning.
impl<T: Translate> Clone for Synchronized<T> {
    fn clone(&self) -> Self {
        let ctx = Context::default();
        let data = self.data.lock().unwrap().translate(&ctx);
        Self {
            ctx,
            data: Mutex::new(data),
        }
    }
}

/// The [`Context`] inside is only used with the [`Ast`](crate::ast::Ast) inside, so
/// it is sound to [`Send`]
unsafe impl<T> Send for Synchronized<T> {}
/// The only method access to the [`Ast`](crate::ast::Ast) or [`Context`] is guarded
/// by a [`Mutex`], so it is sound to [`Sync`]
unsafe impl<T> Sync for Synchronized<T> {}
