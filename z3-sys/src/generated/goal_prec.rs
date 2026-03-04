#[repr(u32)]
#[doc = "\\brief A Goal is essentially a set of formulas.\nZ3 provide APIs for building strategies/tactics for solving and transforming Goals.\nSome of these transformations apply under/over approximations.\n\n- Z3_GOAL_PRECISE:    Approximations/Relaxations were not applied on the goal (sat and unsat answers were preserved).\n- Z3_GOAL_UNDER:      Goal is the product of a under-approximation (sat answers are preserved).\n- Z3_GOAL_OVER:       Goal is the product of an over-approximation (unsat answers are preserved).\n- Z3_GOAL_UNDER_OVER: Goal is garbage (it is the product of over- and under-approximations, sat and unsat answers are not preserved)."]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Z3_goal_prec {
    Z3_GOAL_PRECISE = 0,
    Z3_GOAL_UNDER = 1,
    Z3_GOAL_OVER = 2,
    Z3_GOAL_UNDER_OVER = 3,
}
