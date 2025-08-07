use crate::{Config, Context};

mod sendable_handle;

pub use sendable_handle::SendableHandle;

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
pub unsafe trait PrepareSendable {
    type Inner;
    fn prepare_sendable(&self) -> SendableHandle<Self::Inner>;
}

unsafe impl<T: Translate> PrepareSendable for &[T] {
    type Inner = Vec<T>;

    fn prepare_sendable(&self) -> SendableHandle<Self::Inner> {
        let ctx = Context::default();
        let data: Vec<T> = self.iter().map(|t| t.translate(&ctx)).collect();
        SendableHandle { ctx, data }
    }
}

/// All `Translate` types are `PrepareSendable`. Users must implement `Translate`
/// in order to use `PrepareSendable` for their types.
unsafe impl<T: Translate> PrepareSendable for T {
    type Inner = T;

    fn prepare_sendable(&self) -> SendableHandle<Self::Inner> {
        let ctx = Context::new(&Config::new());
        let ast = self.translate(&ctx);
        SendableHandle { ctx, data: ast }
    }
}
#[cfg(test)]
mod tests {
    use crate::ast::{Ast, Bool};
    use crate::translate::PrepareSendable;
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
        let bv = Bool::fresh_const(&ctx, "hello");
        let sendable = bv.prepare_sendable();
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
        assert_eq!(model.eval(&bv, true), Some(Bool::from_bool(&ctx, true)));
    }
}
