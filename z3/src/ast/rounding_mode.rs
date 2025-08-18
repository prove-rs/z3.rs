use crate::Context;
use crate::ast::IntoAstFromCtx;
use crate::ast::{Ast, Float, trinop};
use z3_sys::*;

/// [`Ast`] node representing a rounding mode for [`Float`] operations.
pub struct RoundingMode {
    pub(crate) ctx: Context,
    pub(crate) z3_ast: Z3_ast,
}

impl RoundingMode {
    /// Create a numeral of [`RoundingMode`] sort which represents the `TowardZero` rounding mode.
    pub fn round_towards_zero(ctx: &Context) -> RoundingMode {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_zero(ctx.z3_ctx.0)) }
    }

    /// Create a numeral of [`RoundingMode`] sort which represents the `TowardNegative` rounding mode.
    pub fn round_towards_negative(ctx: &Context) -> RoundingMode {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_negative(ctx.z3_ctx.0)) }
    }

    /// Create a numeral of [`RoundingMode`] sort which represents the `TowardPositive` rounding mode.
    pub fn round_towards_positive(ctx: &Context) -> RoundingMode {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_toward_positive(ctx.z3_ctx.0)) }
    }

    /// Create a numeral of [`RoundingMode`] sort which represents the `NearestTiesToAway` rounding mode.
    pub fn round_nearest_ties_to_away(ctx: &Context) -> RoundingMode {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_nearest_ties_to_away(ctx.z3_ctx.0)) }
    }

    /// Create a numeral of [`RoundingMode`] sort which represents the `NearestTiesToEven` rounding mode.
    pub fn round_nearest_ties_to_even(ctx: &Context) -> RoundingMode {
        unsafe { Self::wrap(ctx, Z3_mk_fpa_round_nearest_ties_to_even(ctx.z3_ctx.0)) }
    }

    trinop! {
        add(Z3_mk_fpa_add, Float);
        sub(Z3_mk_fpa_sub, Float);
        mul(Z3_mk_fpa_mul, Float);
        div(Z3_mk_fpa_div, Float);
    }
}
