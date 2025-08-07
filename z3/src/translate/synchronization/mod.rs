mod handle;

pub use crate::translate::synchronization::handle::SendableHandle;
use crate::{Context, Translate};
use std::sync::Mutex;

/// This trait allows a type to opt-in to multithreading through [`SendableHandle`]
pub trait PrepareSendable {
    type Inner;
    fn prepare_sendable(&self) -> SendableHandle<Self::Inner>;
}

/// Special implementation directly constructing the handle to avoid unnecessary allocations
impl<T: Translate> PrepareSendable for &[T] {
    type Inner = Vec<T>;

    fn prepare_sendable(&self) -> SendableHandle<Self::Inner> {
        let ctx = Context::default();
        let data: Vec<T> = self.iter().map(|t| t.translate(&ctx)).collect();
        SendableHandle {
            ctx,
            data: Mutex::new(data),
        }
    }
}

/// All `Translate` types are `PrepareSendable`. Users should implement `Translate`
/// in order to use `PrepareSendable` for their types.
impl<T: Translate> PrepareSendable for T {
    type Inner = T;

    fn prepare_sendable(&self) -> SendableHandle<Self::Inner> {
        SendableHandle::new(self)
    }
}
#[cfg(test)]
mod tests {
    use crate::ast::{Ast, Bool};
    use crate::translate::synchronization::PrepareSendable;
    use crate::{Context, Solver};

    #[test]
    fn test_send() {
        let ctx = Context::default();
        let bv = Bool::from_bool(&ctx, true);
        let sendable = bv.prepare_sendable();
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
        let sendable = bv.prepare_sendable();
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
        let sendable = bool.prepare_sendable();
        let model = std::thread::spawn(move || {
            let thread_ctx = Context::default();
            let moved = sendable.recover(&thread_ctx);
            let solver = Solver::new(&thread_ctx);
            solver.assert(&moved._eq(&Bool::from_bool(&thread_ctx, true)));
            solver.check();
            let model = solver.get_model().unwrap();
            model.prepare_sendable()
        })
        .join()
        .expect("uh oh");
        let model = model.recover(&ctx);
        assert_eq!(model.eval(&bool, true), Some(Bool::from_bool(&ctx, true)));
    }
}
