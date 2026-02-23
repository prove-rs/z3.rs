use crate::ast::{Ast, Real, Bool};
use crate::Context;
use z3_sys::*;

/// [`Ast`] node representing an algebraic number value.
pub struct Algebraic {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl Algebraic {
    /// Check if the given AST is a value in the Z3 real algebraic number package.
    pub fn is_value(ast: &impl Ast) -> bool {
        unsafe { Z3_algebraic_is_value(ast.get_ctx().z3_ctx.0, ast.get_z3_ast()) }
    }

    /// Check if the algebraic number is positive.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value (check with `is_value` first).
    pub fn is_positive(&self) -> bool {
        unsafe { Z3_algebraic_is_pos(self.ctx.z3_ctx.0, self.z3_ast) }
    }

    /// Check if the algebraic number is negative.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value (check with `is_value` first).
    pub fn is_negative(&self) -> bool {
        unsafe { Z3_algebraic_is_neg(self.ctx.z3_ctx.0, self.z3_ast) }
    }

    /// Check if the algebraic number is zero.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value (check with `is_value` first).
    pub fn is_zero(&self) -> bool {
        unsafe { Z3_algebraic_is_zero(self.ctx.z3_ctx.0, self.z3_ast) }
    }

    /// Return the sign of the algebraic number.
    /// Returns: -1 if negative, 0 if zero, 1 if positive.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value (check with `is_value` first).
    pub fn sign(&self) -> i32 {
        unsafe { Z3_algebraic_sign(self.ctx.z3_ctx.0, self.z3_ast) }
    }

    /// Add two algebraic numbers.
    /// 
    /// # Precondition
    /// Both `a` and `b` must be valid algebraic values.
    pub fn add(a: &impl Ast, b: &impl Ast) -> Real {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe {
            Real::wrap(
                ctx,
                Z3_algebraic_add(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()).unwrap(),
            )
        }
    }

    /// Subtract two algebraic numbers.
    /// 
    /// # Precondition
    /// Both `a` and `b` must be valid algebraic values.
    pub fn sub(a: &impl Ast, b: &impl Ast) -> Real {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe {
            Real::wrap(
                ctx,
                Z3_algebraic_sub(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()).unwrap(),
            )
        }
    }

    /// Multiply two algebraic numbers.
    /// 
    /// # Precondition
    /// Both `a` and `b` must be valid algebraic values.
    pub fn mul(a: &impl Ast, b: &impl Ast) -> Real {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe {
            Real::wrap(
                ctx,
                Z3_algebraic_mul(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()).unwrap(),
            )
        }
    }

    /// Divide two algebraic numbers.
    /// 
    /// # Precondition
    /// Both `a` and `b` must be valid algebraic values.
    pub fn div(a: &impl Ast, b: &impl Ast) -> Real {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe {
            Real::wrap(
                ctx,
                Z3_algebraic_div(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()).unwrap(),
            )
        }
    }

    /// Return the k-th root of the algebraic number.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value and k > 0.
    pub fn root(&self, k: u32) -> Real {
        unsafe {
            Real::wrap(
                &self.ctx,
                Z3_algebraic_root(self.ctx.z3_ctx.0, self.z3_ast, k).unwrap(),
            )
        }
    }

    /// Return the algebraic number that is the k-th power of the given number.
    /// 
    /// # Precondition
    /// The AST must be a valid algebraic value.
    pub fn power(&self, k: u32) -> Real {
        unsafe {
            Real::wrap(
                &self.ctx,
                Z3_algebraic_power(self.ctx.z3_ctx.0, self.z3_ast, k).unwrap(),
            )
        }
    }

    /// Compare two algebraic numbers for less-than.
    pub fn lt(a: &impl Ast, b: &impl Ast) -> bool {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe { Z3_algebraic_lt(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()) }
    }

    /// Compare two algebraic numbers for greater-than.
    pub fn gt(a: &impl Ast, b: &impl Ast) -> bool {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe { Z3_algebraic_gt(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()) }
    }

    /// Compare two algebraic numbers for equality.
    pub fn eq_algebraic(a: &impl Ast, b: &impl Ast) -> bool {
        assert_eq!(a.get_ctx().z3_ctx, b.get_ctx().z3_ctx);
        let ctx = a.get_ctx();
        unsafe { Z3_algebraic_eq(ctx.z3_ctx.0, a.get_z3_ast(), b.get_z3_ast()) }
    }


}

impl Ast for Algebraic {
    fn get_ctx(&self) -> &Context {
        &self.ctx
    }

    fn get_z3_ast(&self) -> Z3_ast {
        self.z3_ast
    }

    unsafe fn wrap(ctx: &Context, z3_ast: Z3_ast) -> Self {
        Self {
            ctx: ctx.clone(),
            z3_ast,
        }
    }

    fn eq<T: crate::ast::IntoAst<Self>>(&self, other: T) -> Bool
    where
        Self: Sized,
    {
        let other = other.into_ast(self);
        unsafe {
            Bool::wrap(
                &self.ctx,
                Z3_mk_eq(self.ctx.z3_ctx.0, self.z3_ast, other.z3_ast).unwrap(),
            )
        }
    }

    fn ne<T: crate::ast::IntoAst<Self>>(&self, other: T) -> Bool
    where
        Self: Sized,
    {
        self.eq(other).not()
    }
}

impl std::fmt::Display for Algebraic {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let s = unsafe { std::ffi::CStr::from_ptr(Z3_ast_to_string(self.ctx.z3_ctx.0, self.z3_ast)) };
        write!(f, "{}", s.to_string_lossy())
    }
}

impl std::fmt::Debug for Algebraic {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        <Self as std::fmt::Display>::fmt(self, f)
    }
}