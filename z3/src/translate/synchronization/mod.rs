mod handle;

pub use crate::translate::synchronization::handle::Synchronized;
use crate::{Context, Translate};
use std::sync::Mutex;

/// This trait allows a type to opt-in to multithreading through [`Synchronized`]
pub trait PrepareSynchronized {
    type Inner;

    /// Creates a thread-safe wrapper that is both [`Send`] and [`Sync`].
    ///
    /// See also:
    ///
    /// [`Synchronized`]
    fn synchronized(&self) -> Synchronized<Self::Inner>;
}

/// Special implementation directly constructing the handle to avoid unnecessary allocations
impl<T: Translate> PrepareSynchronized for &[T] {
    type Inner = Vec<T>;

    fn synchronized(&self) -> Synchronized<Self::Inner> {
        let ctx = Context::default();
        let data: Vec<T> = self.iter().map(|t| t.translate(&ctx)).collect();
        Synchronized(Mutex::new(data))
    }
}

/// All `Translate` types are `PrepareSendable`. Users should implement `Translate`
/// in order to use `PrepareSendable` for their types.
impl<T: Translate> PrepareSynchronized for T {
    type Inner = T;

    fn synchronized(&self) -> Synchronized<Self::Inner> {
        Synchronized::new(self)
    }
}

/// Test using standard threads
#[cfg(test)]
#[cfg(not(target_arch = "wasm32"))]
mod thread_tests {
    use crate::ast::{Ast, Bool};
    use crate::translate::synchronization::PrepareSynchronized;
    use crate::{Context, Solver};

    #[test]
    fn test_send() {
        let ctx = Context::default();
        let bv = Bool::from_bool(&ctx, true);
        let sendable = bv.synchronized();
        std::thread::spawn(move || {
            let thread_ctx = Context::default();
            let moved = sendable.recover(&thread_ctx);
            assert_eq!(moved.as_bool(), Some(true));
        })
        .join()
        .expect("uh oh");
    }

    #[test]
    fn test_send_vec() {
        let ctx = Context::default();
        let bv = vec![Bool::from_bool(&ctx, true); 8];
        let sendable = bv.synchronized();
        std::thread::spawn(move || {
            let thread_ctx = Context::default();
            let moved = sendable.recover(&thread_ctx);
            for x in moved {
                assert_eq!(x.as_bool(), Some(true));
            }
        })
        .join()
        .expect("uh oh");
    }

    #[test]
    fn test_round_trip() {
        let ctx = Context::default();
        let bool = Bool::new_const(&ctx, "hello");
        let sendable = bool.synchronized();
        let model = std::thread::spawn(move || {
            let thread_ctx = Context::default();
            let moved = sendable.recover(&thread_ctx);
            let solver = Solver::new(&thread_ctx);
            solver.assert(&moved._eq(&Bool::from_bool(&thread_ctx, true)));
            solver.check();
            let model = solver.get_model().unwrap();
            model.synchronized()
        })
        .join()
        .expect("uh oh");
        let model = model.recover(&ctx);
        assert_eq!(model.eval(&bool, true), Some(Bool::from_bool(&ctx, true)));
    }
}

#[cfg(test)]
mod rayon_tests {
    use crate::ast::{Ast, Int};
    use crate::{Context, PrepareSynchronized, Solver};
    use std::ops::Add;

    #[test]
    fn test_rayon() {
        use rayon::prelude::*;
        let ctx = Context::default();
        let int = Int::fresh_const(&ctx, "hello").add(&Int::from_u64(&ctx, 2));
        let sendable = int.synchronized();
        (0..100).into_par_iter().for_each(|i| {
            let ctx = Context::default();
            let moved = sendable.recover(&ctx);
            let solver = Solver::new(&ctx);
            solver.assert(&moved._eq(&Int::from_i64(&ctx, i)));
            assert_eq!(solver.check(), crate::SatResult::Sat);
            let model = solver.get_model().unwrap();
            assert_eq!(model.eval(&moved, true), Some(Int::from_i64(&ctx, i)));
        })
    }
}
