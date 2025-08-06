use crate::ast::{
    Array, Ast, BV, Bool, Datatype, Dynamic, Float, Int, Real, Seq, Set, String, Translate,
};
use crate::{Config, Context};
use z3_sys::Z3_translate;

mod sendable_handle;

pub use sendable_handle::SendableHandle;

/// This trait creates usable Z3 structures out of some type that is a
/// [`Send`] wrapper for the underlying C++ structure (usually
/// some parameterization of [`SendableHandle`]). Users may implement it
/// for their own types, though almost no users should need to.
///
/// # Safety
///
/// todo: maybe this should be a sealed trait; I can't think of many cases where someone should need to do this
pub unsafe trait RecoverSendable {
    type Target;
    fn recover(&self, ctx: &Context) -> Self::Target;
}
/// # Safety
/// todo: should this be sealed as well?
pub unsafe trait PrepareSendable {
    type SendWrapper;

    fn prepare_sendable(&self) -> Self::SendWrapper;
}

macro_rules! impl_translate_ast {
    ($ty:ident) => {
        unsafe impl RecoverSendable for SendableHandle<$ty> {
            type Target = $ty;
            fn recover(&self, ctx: &Context) -> $ty {
                let data = unsafe {
                    Z3_translate(self.ctx.z3_ctx.0, self.data.get_z3_ast(), ctx.z3_ctx.0)
                };
                unsafe { $ty::wrap(ctx, data) }
            }
        }
    };
}

impl_translate_ast!(Bool);
impl_translate_ast!(Int);
impl_translate_ast!(Real);
impl_translate_ast!(Float);
impl_translate_ast!(String);
impl_translate_ast!(BV);
impl_translate_ast!(Array);
impl_translate_ast!(Set);
impl_translate_ast!(Seq);
impl_translate_ast!(Datatype);
impl_translate_ast!(Dynamic);
unsafe impl<T: PrepareSendable + Translate> PrepareSendable for &[T] {
    type SendWrapper = SendableHandle<Vec<T>>;

    fn prepare_sendable(&self) -> Self::SendWrapper {
        let ctx = Context::new(&Config::new());
        let ast = self.iter().map(|t| t.translate(&ctx)).collect();
        SendableHandle { ctx, data: ast }
    }
}

unsafe impl<T: Translate> PrepareSendable for T {
    type SendWrapper = SendableHandle<T>;

    fn prepare_sendable(&self) -> Self::SendWrapper {
        let ctx = Context::new(&Config::new());
        let ast = self.translate(&ctx);
        SendableHandle { ctx, data: ast }
    }
}

unsafe impl<T: PrepareSendable + Translate> PrepareSendable for Vec<T> {
    type SendWrapper = SendableHandle<Vec<T>>;

    fn prepare_sendable(&self) -> Self::SendWrapper {
        self.as_slice().prepare_sendable()
    }
}

#[cfg(test)]
mod tests {
    use crate::Context;
    use crate::ast::Bool;
    use crate::translate::{PrepareSendable, RecoverSendable};

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
}
