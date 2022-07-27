use ast::{Ast, Bool, Dynamic};
use std::convert::TryInto;
use std::ffi::{CStr, CString};
use std::fmt;
use z3_sys::*;
use Context;
use Model;
use Optimize;
use SatResult;
use Symbol;
use Z3_MUTEX;

#[cfg(feature = "arbitrary-size-numeral")]
use num::{
    bigint::{BigInt, BigUint, Sign},
    rational::BigRational,
};

impl<'ctx> Optimize<'ctx> {
    unsafe fn wrap(ctx: &'ctx Context, z3_opt: Z3_optimize) -> Optimize<'ctx> {
        Z3_optimize_inc_ref(ctx.z3_ctx, z3_opt);
        Optimize { ctx, z3_opt }
    }

    /// Create a new optimize context.
    pub fn new(ctx: &'ctx Context) -> Optimize<'ctx> {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Self::wrap(ctx, Z3_mk_optimize(ctx.z3_ctx)) }
    }

    /// Get this optimizers 's context.
    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Assert hard constraint to the optimization context.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert_soft()`](#method.assert_soft)
    /// - [`Optimize::maximize()`](#method.maximize)
    /// - [`Optimize::minimize()`](#method.minimize)
    pub fn assert(&self, ast: &impl Ast<'ctx>) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_assert(self.ctx.z3_ctx, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Assert soft constraint to the optimization context.
    /// Weight is a positive, rational penalty for violating the constraint.
    /// Group is an optional identifier to group soft constraints.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`](#method.assert)
    /// - [`Optimize::maximize()`](#method.maximize)
    /// - [`Optimize::minimize()`](#method.minimize)
    pub fn assert_soft(&self, ast: &impl Ast<'ctx>, weight: impl Weight, group: Option<Symbol>) {
        let weight_string = weight.to_string();
        let weight_cstring = CString::new(weight_string).unwrap();
        let group = group
            .map(|g| g.as_z3_symbol(self.ctx))
            .unwrap_or_else(std::ptr::null_mut);
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe {
            Z3_optimize_assert_soft(
                self.ctx.z3_ctx,
                self.z3_opt,
                ast.get_z3_ast(),
                weight_cstring.as_ptr(),
                group,
            )
        };
    }

    /// Add a maximization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`](#method.assert)
    /// - [`Optimize::minimize()`](#method.minimize)
    pub fn maximize(&self, ast: &impl Ast<'ctx>) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_maximize(self.ctx.z3_ctx, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Add a minimization constraint.
    ///
    /// # See also:
    ///
    /// - [`Optimize::assert()`](#method.assert)
    /// - [`Optimize::maximize()`](#method.maximize)
    pub fn minimize(&self, ast: &impl Ast<'ctx>) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_minimize(self.ctx.z3_ctx, self.z3_opt, ast.get_z3_ast()) };
    }

    /// Create a backtracking point.
    ///
    /// The optimize solver contains a set of rules, added facts and assertions.
    /// The set of rules, facts and assertions are restored upon calling
    /// [`Optimize::pop()`](#method.pop).
    ///
    /// # See also:
    ///
    /// - [`Optimize::pop()`](#method.pop)
    pub fn push(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_push(self.ctx.z3_ctx, self.z3_opt) };
    }

    /// Backtrack one level.
    ///
    /// # Preconditions:
    ///
    /// - The number of calls to [`Optimize::pop`] cannot exceed the number of calls to
    ///   [`Optimize::push()`](#method.push).
    ///
    /// # See also:
    ///
    /// - [`Optimize::push()`](#method.push)
    pub fn pop(&self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_pop(self.ctx.z3_ctx, self.z3_opt) };
    }

    /// Check consistency and produce optimal values.
    ///
    /// # See also:
    ///
    /// - [`Optimize::get_model()`](#method.get_model)
    pub fn check(&self, assumptions: &[Bool<'ctx>]) -> SatResult {
        let _guard = Z3_MUTEX.lock().unwrap();
        let assumptions: Vec<Z3_ast> = assumptions.iter().map(|a| a.z3_ast).collect();
        match unsafe {
            Z3_optimize_check(
                self.ctx.z3_ctx,
                self.z3_opt,
                assumptions.len().try_into().unwrap(),
                assumptions.as_ptr(),
            )
        } {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    /// Retrieve the model for the last [`Optimize::check()`](#method.check)
    ///
    /// The error handler is invoked if a model is not available because
    /// the commands above were not invoked for the given optimization
    /// solver, or if the result was `Z3_L_FALSE`.
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        Model::of_optimize(self)
    }

    /// Retrieve the objectives for the last [`Optimize::check()`](#method.check)
    ///
    /// This contains maximize/minimize objectives and grouped soft constraints.
    pub fn get_objectives(&self) -> Vec<Dynamic<'ctx>> {
        let (z3_objectives, len) = unsafe {
            let _guard = Z3_MUTEX.lock().unwrap();
            let objectives = Z3_optimize_get_objectives(self.ctx.z3_ctx, self.z3_opt);
            let len = Z3_ast_vector_size(self.ctx.z3_ctx, objectives);
            (objectives, len)
        };

        let mut objectives = Vec::with_capacity(len as usize);

        for i in 0..len {
            let elem = unsafe {
                let _guard = Z3_MUTEX.lock().unwrap();
                Z3_ast_vector_get(self.ctx.z3_ctx, z3_objectives, i)
            };
            let elem = unsafe { Dynamic::new(self.ctx, elem) };
            objectives.push(elem);
        }

        objectives
    }

    /// Retrieve a string that describes the last status returned by [`Optimize::check()`](#method.check).
    ///
    /// Use this method when [`Optimize::check()`](#method.check) returns `SatResult::Unknown`.
    pub fn get_reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_optimize_get_reason_unknown(self.ctx.z3_ctx, self.z3_opt) };
        if p.is_null() {
            return None;
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(|s| s.to_string())
    }
}

impl<'ctx> fmt::Display for Optimize<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_optimize_to_string(self.ctx.z3_ctx, self.z3_opt) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for Optimize<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for Optimize<'ctx> {
    fn drop(&mut self) {
        let _guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_optimize_dec_ref(self.ctx.z3_ctx, self.z3_opt) };
    }
}

/// A rational non-negative weight for soft assertions.
/// This trait is sealed and cannot be implemented for types outside of
/// `z3`.
///
/// # See also:
///
/// - [`Optimize::assert_soft()`](#method.assert_soft)
pub trait Weight: private::Sealed {
    /// This is purposefully distinct from `ToString` to allow
    /// specifying a `to_string` for tuples.
    fn to_string(&self) -> String;
}

macro_rules! impl_weight {
    ($($ty: ty),*) => {
        $(
            impl Weight for $ty {
                fn to_string(&self) -> String {
                    ToString::to_string(&self)
                }
            }

            impl Weight for ($ty, $ty) {
                fn to_string(&self) -> String {
                    format!("{} / {}", self.0, self.1)
                }
            }
        )*
    };
}

impl_weight! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}

#[cfg(feature = "arbitrary-size-numeral")]
impl Weight for BigInt {
    fn to_string(&self) -> String {
        assert_ne!(self.sign(), Sign::Minus);
        self.to_str_radix(10)
    }
}

#[cfg(feature = "arbitrary-size-numeral")]
impl Weight for BigUint {
    fn to_string(&self) -> String {
        self.to_str_radix(10)
    }
}

#[cfg(feature = "arbitrary-size-numeral")]
impl Weight for BigRational {
    fn to_string(&self) -> String {
        assert_ne!(self.numer().sign(), Sign::Minus);
        assert_ne!(self.denom().sign(), Sign::Minus);
        format!(
            "{} / {}",
            self.numer().to_str_radix(10),
            self.denom().to_str_radix(10)
        )
    }
}

macro_rules! impl_sealed {
    ($($ty: ty),*) => {
        mod private {
            #[allow(unused_imports)]
            use super::*;
            pub trait Sealed {}
            $(
                impl Sealed for $ty {}
                impl Sealed for ($ty, $ty) {}
            )*

            #[cfg(feature = "arbitrary-size-numeral")]
            impl Sealed for BigInt {}
            #[cfg(feature = "arbitrary-size-numeral")]
            impl Sealed for BigUint {}
            #[cfg(feature = "arbitrary-size-numeral")]
            impl Sealed for BigRational {}
        }
    };
}

impl_sealed! {
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
}
