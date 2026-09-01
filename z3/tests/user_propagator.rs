use std::cell::{Cell, RefCell};
use std::rc::Rc;
use z3::ast::{Ast, BV, Bool, Dynamic};
use z3::{
    Context, FuncDecl, PrepareSynchronized, PropagatorCallbackHandle, SatResult, Solver, Sort,
    Translate, UserPropagator,
};

// ── helpers ──────────────────────────────────────────────────────────────────

/// A minimal propagator that only implements the required lifecycle methods.
struct MinimalPropagator;

impl UserPropagator for MinimalPropagator {
    fn push(&mut self) {}
    fn pop(&mut self, _: u32) {}
}

/// A propagator that counts how many times `fixed` fires.
struct FixedCounter {
    count: Rc<Cell<u32>>,
    scope_stack: Vec<u32>,
}

impl FixedCounter {
    fn new(count: Rc<Cell<u32>>) -> Self {
        Self {
            count,
            scope_stack: Vec::new(),
        }
    }
}

impl UserPropagator for FixedCounter {
    fn push(&mut self) {
        self.scope_stack.push(self.count.get());
    }
    fn pop(&mut self, num_scopes: u32) {
        for _ in 0..num_scopes {
            if let Some(saved) = self.scope_stack.pop() {
                self.count.set(saved);
            }
        }
    }
    fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, _ast: &Dynamic, _val: &Dynamic) {
        self.count.set(self.count.get() + 1);
    }
}

/// A propagator that blocks every model it sees in `final_check`,
/// counting how many distinct models there were.
struct ModelCounter {
    model_count: Rc<Cell<u32>>,
    /// ASTs currently fixed — maintained across push/pop.
    fixed_exprs: Vec<Dynamic>,
    scope_stack: Vec<usize>,
}

impl ModelCounter {
    fn new(model_count: Rc<Cell<u32>>) -> Self {
        Self {
            model_count,
            fixed_exprs: Vec::new(),
            scope_stack: Vec::new(),
        }
    }
}

impl UserPropagator for ModelCounter {
    fn push(&mut self) {
        self.scope_stack.push(self.fixed_exprs.len());
    }
    fn pop(&mut self, num_scopes: u32) {
        for _ in 0..num_scopes {
            if let Some(saved_len) = self.scope_stack.pop() {
                self.fixed_exprs.truncate(saved_len);
            }
        }
    }
    fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, _val: &Dynamic) {
        self.fixed_exprs.push(ast.clone());
    }
    fn final_check(&mut self, cb: &PropagatorCallbackHandle<'_>) {
        self.model_count.set(self.model_count.get() + 1);
        // Block this model by asserting FALSE conditional on all current fixed exprs.
        let false_ast = Bool::from_bool(false);
        let false_dyn = Dynamic::from_ast(&false_ast);
        let premises: Vec<&Dynamic> = self.fixed_exprs.iter().collect();
        cb.propagate_consequence(&premises, &[], &false_dyn);
    }
}

/// N-Queens propagator that detects constraint violations immediately in `fixed`.
///
/// Mirrors the `user_propagator_with_theory` C++ example. When a queen is assigned
/// a column, it is checked against every already-fixed queen. If a same-column or
/// same-diagonal conflict is found, a conditional conflict is injected immediately
/// with only those two queens as premises — not the full assignment. This allows Z3
/// to prune the search branch before reaching a complete assignment, unlike
/// `NQueensPropagator` which waits until `final_check`.
struct TheoryNQueensPropagator {
    n: u32,
    solutions: Rc<RefCell<Vec<Vec<u64>>>>,
    queens: Vec<(Dynamic, Option<u64>)>,
    scope_stack: Vec<Vec<Option<u64>>>,
}

impl TheoryNQueensPropagator {
    fn new(n: u32, queens: &[BV], solutions: Rc<RefCell<Vec<Vec<u64>>>>) -> Self {
        Self {
            n,
            solutions,
            queens: queens
                .iter()
                .map(|q| (Dynamic::from_ast(q), None))
                .collect(),
            scope_stack: Vec::new(),
        }
    }

    fn is_valid(&self) -> bool {
        let vals: Vec<u64> = self.queens.iter().filter_map(|(_, v)| *v).collect();
        if vals.len() != self.n as usize {
            return false;
        }
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                if vals[i] == vals[j] {
                    return false;
                }
                let di = (i as i64) - (j as i64);
                let dc = (vals[i] as i64) - (vals[j] as i64);
                if di.abs() == dc.abs() {
                    return false;
                }
            }
        }
        true
    }
}

impl UserPropagator for TheoryNQueensPropagator {
    fn push(&mut self) {
        self.scope_stack
            .push(self.queens.iter().map(|(_, v)| *v).collect());
    }

    fn pop(&mut self, num_scopes: u32) {
        for _ in 0..num_scopes {
            if let Some(saved) = self.scope_stack.pop() {
                for (i, (_, val)) in self.queens.iter_mut().enumerate() {
                    *val = saved[i];
                }
            }
        }
    }

    fn fixed(&mut self, cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, value: &Dynamic) {
        let name = ast.decl().name().to_string();
        let idx = match name.strip_prefix('q').and_then(|s| s.parse::<usize>().ok()) {
            Some(i) if i < self.queens.len() => i,
            _ => return,
        };
        let pos = match value.as_bv().and_then(|bv| bv.as_u64()) {
            Some(p) => p,
            None => return,
        };

        // Check the new assignment against every already-fixed queen.
        // Inject a minimal conflict (just those two queens) rather than waiting for
        // final_check with all queens — this is the key difference from NQueensPropagator.
        let false_dyn = Dynamic::from_ast(&Bool::from_bool(false));
        for j in 0..self.queens.len() {
            let (prev_ast, prev_val) = &self.queens[j];
            let Some(prev_pos) = *prev_val else { continue };

            if pos == prev_pos {
                cb.propagate_consequence(&[ast, prev_ast], &[], &false_dyn);
                continue; // column conflict subsumes diagonal; skip diagonal check
            }
            let di = (idx as i64 - j as i64).abs();
            let dc = (pos as i64 - prev_pos as i64).abs();
            if di == dc {
                cb.propagate_consequence(&[ast, prev_ast], &[], &false_dyn);
            }
        }

        self.queens[idx].1 = Some(pos);
    }

    fn final_check(&mut self, cb: &PropagatorCallbackHandle<'_>) {
        // Only reachable when all queens are fixed with no conflicts detected in `fixed`.
        if self.is_valid() {
            let sol: Vec<u64> = self.queens.iter().filter_map(|(_, v)| *v).collect();
            self.solutions.borrow_mut().push(sol);
        }
        let false_dyn = Dynamic::from_ast(&Bool::from_bool(false));
        let premises: Vec<&Dynamic> = self.queens.iter().map(|(d, _)| d).collect();
        cb.propagate_consequence(&premises, &[], &false_dyn);
    }
}

/// Propagates `consequence = true` back into the solver whenever the single
/// registered expression is fixed to `true`, justified by that assignment.
///
/// This exercises the `propagate_consequence` path with a non-false consequent,
/// which is distinct from conflict injection.
struct PositiveConsequencePropagator {
    consequence: Dynamic,
}

impl UserPropagator for PositiveConsequencePropagator {
    fn push(&mut self) {}
    fn pop(&mut self, _: u32) {}

    fn fixed(&mut self, cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, value: &Dynamic) {
        if value.as_bool().and_then(|b| b.as_bool()) == Some(true) {
            cb.propagate_consequence(&[ast], &[], &self.consequence);
        }
    }
}

/// Records whether the `eq` and/or `diseq` callbacks have fired.
struct EqDiseqTracker {
    eq_fired: Rc<Cell<bool>>,
    diseq_fired: Rc<Cell<bool>>,
}

impl UserPropagator for EqDiseqTracker {
    fn push(&mut self) {}
    fn pop(&mut self, _: u32) {}

    fn eq(&mut self, _cb: &PropagatorCallbackHandle<'_>, _s: &Dynamic, _t: &Dynamic) {
        self.eq_fired.set(true);
    }

    fn diseq(&mut self, _cb: &PropagatorCallbackHandle<'_>, _s: &Dynamic, _t: &Dynamic) {
        self.diseq_fired.set(true);
    }
}

// ── basic lifecycle tests ─────────────────────────────────────────────────────

#[test]
fn minimal_push_pop_fresh_does_not_crash() {
    let solver = Solver::new();
    solver.set_propagator(MinimalPropagator, || MinimalPropagator);
    let x = Bool::new_const("x");
    solver.assert(&x);
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn fixed_callback_fires_for_asserted_bool() {
    let x = Bool::new_const("x");
    let count = Rc::new(Cell::new(0u32));
    let solver = Solver::new();

    solver.set_propagator(FixedCounter::new(count.clone()), || {
        FixedCounter::new(Rc::new(Cell::new(0)))
    });
    solver.propagate_register(&x);
    solver.assert(&x);

    assert_eq!(solver.check(), SatResult::Sat);
    assert!(count.get() >= 1, "fixed callback should have fired");
}

#[test]
fn fixed_callback_fires_for_bv() {
    let count = Rc::new(Cell::new(0u32));
    let solver = Solver::new();
    let x = BV::new_const("x", 8);
    let zero = BV::from_u64(0, 8);

    solver.set_propagator(FixedCounter::new(count.clone()), || {
        FixedCounter::new(Rc::new(Cell::new(0)))
    });
    solver.propagate_register(&x);
    solver.assert(x.eq(&zero));

    assert_eq!(solver.check(), SatResult::Sat);
    assert!(count.get() >= 1, "fixed callback should have fired for BV");
}

// ── final_check tests ─────────────────────────────────────────────────────────

#[test]
fn final_check_fires_and_blocks_one_model() {
    // A single unconstrained Bool has two models (x=true, x=false).
    // ModelCounter blocks each model as it's found.
    let count = Rc::new(Cell::new(0u32));
    let solver = Solver::new();
    let x = Bool::new_const("fc_x");

    solver.set_propagator(ModelCounter::new(count.clone()), || {
        ModelCounter::new(Rc::new(Cell::new(0)))
    });
    solver.propagate_register(&x);

    // Both models should be enumerated and blocked, so we eventually get UNSAT.
    // Run until UNSAT, capped at 10 iterations to avoid infinite loops in bad implementations.
    let mut iters = 0u32;
    loop {
        let result = solver.check();
        if result == SatResult::Unsat {
            break;
        }
        assert_eq!(result, SatResult::Sat);
        iters += 1;
        assert!(
            iters <= 10,
            "solver should have become UNSAT within a few iterations"
        );
    }
    // Bool has exactly 2 models; we should have blocked them both.
    assert_eq!(
        count.get(),
        2,
        "final_check should have been called for each model"
    );
}

// ── N-Queens integration test ─────────────────────────────────────────────────

/// N-Queens propagator using BV8 column variables.
///
/// Each queen's column is a BV8 variable q0..q(n-1). The propagator tracks
/// assignments via `fixed`, validates completeness in `final_check`, records
/// valid solutions, and injects a conditional conflict (premised on all currently
/// fixed queens) to force Z3 to enumerate further.
struct NQueensPropagator {
    n: u32,
    solutions: Rc<RefCell<Vec<Vec<u64>>>>,
    /// Per-queen: (expression_to_use_as_premise, current_fixed_value)
    queens: Vec<(Dynamic, Option<u64>)>,
    scope_stack: Vec<Vec<Option<u64>>>,
}

impl NQueensPropagator {
    fn new(n: u32, queens: &[BV], solutions: Rc<RefCell<Vec<Vec<u64>>>>) -> Self {
        Self {
            n,
            solutions,
            queens: queens
                .iter()
                .map(|q| (Dynamic::from_ast(q), None))
                .collect(),
            scope_stack: Vec::new(),
        }
    }

    fn is_valid(&self) -> bool {
        let vals: Vec<u64> = self.queens.iter().filter_map(|(_, v)| *v).collect();
        if vals.len() != self.n as usize {
            return false;
        }
        for i in 0..vals.len() {
            for j in (i + 1)..vals.len() {
                if vals[i] == vals[j] {
                    return false; // same column
                }
                let di = (i as i64) - (j as i64);
                let dc = (vals[i] as i64) - (vals[j] as i64);
                if di.abs() == dc.abs() {
                    return false; // same diagonal
                }
            }
        }
        true
    }
}

impl UserPropagator for NQueensPropagator {
    fn push(&mut self) {
        self.scope_stack
            .push(self.queens.iter().map(|(_, v)| *v).collect());
    }

    fn pop(&mut self, num_scopes: u32) {
        for _ in 0..num_scopes {
            if let Some(saved) = self.scope_stack.pop() {
                for (i, (_, val)) in self.queens.iter_mut().enumerate() {
                    *val = saved[i];
                }
            }
        }
    }

    fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, value: &Dynamic) {
        if let Some(bv) = value.as_bv() {
            if let Some(v) = bv.as_u64() {
                let name = ast.decl().name().to_string();
                if let Some(idx_str) = name.strip_prefix('q') {
                    if let Ok(idx) = idx_str.parse::<usize>() {
                        if idx < self.queens.len() {
                            self.queens[idx].1 = Some(v);
                        }
                    }
                }
            }
        }
    }

    fn final_check(&mut self, cb: &PropagatorCallbackHandle<'_>) {
        if self.is_valid() {
            let sol: Vec<u64> = self.queens.iter().filter_map(|(_, v)| *v).collect();
            self.solutions.borrow_mut().push(sol);
        }
        // Block this specific assignment: the conflict is conditional on all queen
        // expressions being fixed to their current values. This rules out exactly
        // this model, allowing Z3 to backtrack and find others.
        let false_ast = Bool::from_bool(false);
        let false_dyn = Dynamic::from_ast(&false_ast);
        let premises: Vec<&Dynamic> = self.queens.iter().map(|(d, _)| d).collect();
        cb.propagate_consequence(&premises, &[], &false_dyn);
    }
}

#[test]
fn nqueens_4_finds_two_solutions() {
    // 4-queens has exactly 2 distinct valid placements.
    let n: u32 = 4;
    let solutions = Rc::new(RefCell::new(Vec::<Vec<u64>>::new()));
    let solver = Solver::new();

    // BV8 column variables q0..q3, range-constrained to [0, n).
    let queens: Vec<BV> = (0..n).map(|i| BV::new_const(format!("q{i}"), 8)).collect();
    let n_bv = BV::from_u64(n as u64, 8);
    for q in &queens {
        solver.assert(q.bvuge(BV::from_u64(0, 8)));
        solver.assert(q.bvult(&n_bv));
    }

    solver.set_propagator(
        NQueensPropagator::new(n, &queens, solutions.clone()),
        move || NQueensPropagator::new(n, &[], Rc::new(RefCell::new(vec![]))),
    );
    for q in &queens {
        solver.propagate_register(q);
    }

    // Drive until UNSAT to enumerate all models.
    let mut iterations = 0u32;
    loop {
        if solver.check() == SatResult::Unsat {
            break;
        }
        iterations += 1;
        assert!(iterations <= 200, "solver should have terminated");
    }

    let found = solutions.borrow();
    assert_eq!(found.len(), 2, "4-queens has exactly 2 solutions");
}

#[test]
fn nqueens_theory_style_early_conflicts_find_same_solutions() {
    // Mirrors the `user_propagator_with_theory` C++ example from
    // z3-src/z3/examples/userPropagator/user_propagator_with_theory.h.
    //
    // Key difference from nqueens_4_finds_two_solutions: conflicts are injected
    // in `fixed` (as soon as an assignment violates a constraint) rather than in
    // `final_check` (after all queens are assigned). The conflict premise set is
    // minimal — just the two clashing queens, not the entire assignment — allowing
    // Z3 to prune invalid branches earlier.
    //
    // Observable outcome must be identical: 4-queens has exactly 2 solutions.
    let n: u32 = 4;
    let solutions = Rc::new(RefCell::new(Vec::<Vec<u64>>::new()));
    let solver = Solver::new();

    let queens: Vec<BV> = (0..n).map(|i| BV::new_const(format!("q{i}"), 8)).collect();
    let n_bv = BV::from_u64(n as u64, 8);
    for q in &queens {
        solver.assert(q.bvuge(BV::from_u64(0, 8)));
        solver.assert(q.bvult(&n_bv));
    }

    solver.set_propagator(
        TheoryNQueensPropagator::new(n, &queens, solutions.clone()),
        move || TheoryNQueensPropagator::new(n, &[], Rc::new(RefCell::new(vec![]))),
    );
    for q in &queens {
        solver.propagate_register(q);
    }

    let mut iterations = 0u32;
    loop {
        if solver.check() == SatResult::Unsat {
            break;
        }
        iterations += 1;
        assert!(iterations <= 200, "solver should have terminated");
    }

    let found = solutions.borrow();
    assert_eq!(
        found.len(),
        2,
        "theory-style early conflict propagator must find the same 2 solutions"
    );
}

// ── positive consequence ──────────────────────────────────────────────────────

#[test]
fn positive_consequence_propagates_into_model() {
    // Verify that propagate_consequence with a non-false consequent actually
    // affects the model. When `x` is fixed to true the propagator asserts `y`
    // (positive Bool, not false) back into the solver, justified by `x`. After
    // check(), the model must have y = true even though y was never directly
    // asserted.
    //
    // This exercises a distinct code path from conflict injection — all other
    // tests only propagate `false`.
    let solver = Solver::new();
    let x = Bool::new_const("pos_x");
    let y = Bool::new_const("pos_y");
    let y_dyn = Dynamic::from_ast(&y);

    // Use Synchronized to carry y_dyn across the Send+Sync factory boundary.
    let y_sync = y_dyn.synchronized();
    solver.set_propagator(
        PositiveConsequencePropagator { consequence: y_dyn },
        move || PositiveConsequencePropagator {
            consequence: y_sync.recover(),
        },
    );
    solver.propagate_register(&x);
    solver.assert(&x); // forces x = true, triggering the propagation

    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(
        model.eval(&y, true).and_then(|b| b.as_bool()),
        Some(true),
        "propagating y as a positive consequence of x=true should make y true in the model"
    );
}

// ── eq / diseq callbacks ──────────────────────────────────────────────────────

#[test]
fn eq_callback_fires_when_expressions_equated() {
    // When two registered BV expressions are determined to be equal (here via an
    // explicit equality assertion), Z3's congruence closure merges their e-nodes
    // and the `eq` callback fires.
    let eq_fired = Rc::new(Cell::new(false));
    let solver = Solver::new();
    let a = BV::new_const("eq_a", 8);
    let b = BV::new_const("eq_b", 8);

    solver.set_propagator(
        EqDiseqTracker {
            eq_fired: eq_fired.clone(),
            diseq_fired: Rc::new(Cell::new(false)),
        },
        || EqDiseqTracker {
            eq_fired: Rc::new(Cell::new(false)),
            diseq_fired: Rc::new(Cell::new(false)),
        },
    );
    solver.propagate_register(&a);
    solver.propagate_register(&b);

    // Assert a = b and pin a to a concrete value; Z3 must merge a and b.
    solver.assert(a.eq(&b));
    solver.assert(a.eq(BV::from_u64(42, 8)));

    assert_eq!(solver.check(), SatResult::Sat);
    assert!(
        eq_fired.get(),
        "eq callback must fire when two registered expressions are equated"
    );
}

#[test]
fn diseq_callback_fires_when_expressions_disequal() {
    // When two registered BV expressions are determined to be disequal, Z3 calls
    // the `diseq` callback.
    let diseq_fired = Rc::new(Cell::new(false));
    let solver = Solver::new();
    let a = BV::new_const("diseq_a", 8);
    let b = BV::new_const("diseq_b", 8);

    solver.set_propagator(
        EqDiseqTracker {
            eq_fired: Rc::new(Cell::new(false)),
            diseq_fired: diseq_fired.clone(),
        },
        || EqDiseqTracker {
            eq_fired: Rc::new(Cell::new(false)),
            diseq_fired: Rc::new(Cell::new(false)),
        },
    );
    solver.propagate_register(&a);
    solver.propagate_register(&b);

    // a = 5 and a ≠ b; Z3 must derive that a and b are disequal.
    solver.assert(a.eq(BV::from_u64(5, 8)));
    solver.assert(a.eq(&b).not());

    assert_eq!(solver.check(), SatResult::Sat);
    assert!(
        diseq_fired.get(),
        "diseq callback must fire when two registered expressions are found disequal"
    );
}

// ── set_propagator lifecycle ──────────────────────────────────────────────────

#[test]
fn second_set_propagator_replaces_first() {
    let first_fixed = Rc::new(Cell::new(0u32));
    let second_fixed = Rc::new(Cell::new(0u32));
    let solver = Solver::new();
    let x = BV::new_const("x_rp", 8);
    let zero = BV::from_u64(0, 8);

    solver.set_propagator(FixedCounter::new(first_fixed.clone()), || {
        FixedCounter::new(Rc::new(Cell::new(0)))
    });
    solver.set_propagator(FixedCounter::new(second_fixed.clone()), || {
        FixedCounter::new(Rc::new(Cell::new(0)))
    });

    solver.propagate_register(&x);
    solver.assert(x.eq(&zero));
    assert_eq!(solver.check(), SatResult::Sat);

    assert_eq!(
        first_fixed.get(),
        0,
        "first propagator should not fire after replacement"
    );
    assert!(second_fixed.get() >= 1, "second propagator should fire");
}

#[test]
fn drop_with_active_propagator_does_not_crash() {
    let solver = Solver::new();
    solver.set_propagator(MinimalPropagator, || MinimalPropagator);
    // Drop solver with an active propagator — should not double-free or crash.
    drop(solver);
}

// ── context sanity check ─────────────────────────────────────────────────────

#[test]
fn callback_thread_local_context_matches_propagator_context() {
    // Sanity check: inside a `fixed` callback the thread-local Z3 context must
    // equal the propagator's context. Z3 AST factory functions such as
    // `Bool::from_bool` and variadic operations like `Bool::and` read
    // `Context::thread_local()` internally. If that context differed from the
    // one that owns the `ast` argument, combining the two would call, e.g.,
    //   Z3_mk_implies(ast.ctx, ast.z3_ast, fresh.z3_ast)
    // with mismatched contexts; Z3 returns null and the `.unwrap()` inside the
    // macro expansion panics.
    //
    // The `enter_callback_ctx` guard in each trampoline must ensure this is true
    // on every thread, including Z3 background threads running fresh instances.
    let fired = Rc::new(Cell::new(false));

    struct ContextSanityChecker {
        fired: Rc<Cell<bool>>,
    }

    impl UserPropagator for ContextSanityChecker {
        fn push(&mut self) {}
        fn pop(&mut self, _: u32) {}

        fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, ast: &Dynamic, _: &Dynamic) {
            // Create a Bool via the thread-local context — the normal user pattern.
            let fresh_true = Bool::from_bool(true);

            // implies(ast, true) = true. The call internally does:
            //   Z3_mk_implies(ast.ctx.z3_ctx.0, ast.z3_ast, fresh_true.z3_ast).unwrap()
            // If ast.ctx != Context::thread_local(), Z3 returns null and .unwrap() panics,
            // failing the test. Success means the guard set the thread-local correctly.
            let ast_bool = ast.as_bool().expect("registered expr must be Bool");
            let _result = ast_bool.implies(&fresh_true);

            self.fired.set(true);
        }
    }

    let solver = Solver::new();
    let x = Bool::new_const("x_ctx_check");
    solver.set_propagator(
        ContextSanityChecker {
            fired: fired.clone(),
        },
        || ContextSanityChecker {
            fired: Rc::new(Cell::new(false)),
        },
    );
    solver.propagate_register(&x);
    solver.assert(&x);
    assert_eq!(solver.check(), SatResult::Sat);
    assert!(fired.get(), "fixed callback must have fired");
}

// ── compile-time context safety ───────────────────────────────────────────────

/// This test is intentionally left as a comment showing what SHOULD NOT compile.
///
/// The `Send + Sync` bound on `fresh_factory` prevents Z3 ASTs (which are
/// `!Send + !Sync`) from being captured in the factory closure. If a user tries:
///
/// ```compile_fail
/// use z3::{UserPropagator, Solver};
/// use z3::ast::{Bool, Dynamic, Ast};
///
/// struct MyProp { stored: Dynamic }
/// impl UserPropagator for MyProp {
///     fn push(&mut self) {}
///     fn pop(&mut self, _: u32) {}
/// }
///
/// let x = Bool::new_const("x");
/// let x_dyn = Dynamic::from_ast(&x);
/// let solver = Solver::new();
/// // ERROR: `Dynamic` is `!Sync`, so this closure cannot be `Sync`.
/// // Use x_dyn.synchronized() and .recover() inside the factory to cross the boundary.
/// solver.set_propagator(MyProp { stored: x_dyn.clone() }, move || {
///     MyProp { stored: x_dyn.clone() }
/// });
/// ```
///
/// The compiler rejects it because the closure captures `x_dyn: Dynamic` which
/// is `!Sync`, preventing it from satisfying `F: Sync`.
#[allow(dead_code)]
fn _compile_fail_doc() {}

// ── translate / clone ─────────────────────────────────────────────────────────

#[test]
fn translate_does_not_carry_propagator() {
    let solver = Solver::new();
    let count = Rc::new(Cell::new(0u32));

    solver.set_propagator(FixedCounter::new(count.clone()), || {
        FixedCounter::new(Rc::new(Cell::new(0)))
    });

    // Translating the solver should produce a fresh solver with no propagator.
    let translated = solver.translate(&Context::thread_local());

    let x = Bool::new_const("x_tr");
    translated.propagate_register(&x);
    translated.assert(&x);

    // If the propagator were carried, this line would trigger a second call on the
    // same state (stale pointer). The translated solver must start with no propagator.
    // (We just verify it doesn't crash; the count should stay at 0.)
    assert_eq!(translated.check(), SatResult::Sat);
    assert_eq!(count.get(), 0, "propagator must not carry across translate");
}

// ── decide callback ───────────────────────────────────────────────────────────

/// Sets a flag the first time `decide` fires.
struct DecideTracker {
    fired: Rc<Cell<bool>>,
}

impl UserPropagator for DecideTracker {
    fn push(&mut self) {}
    fn pop(&mut self, _: u32) {}
    fn decide(
        &mut self,
        _cb: &PropagatorCallbackHandle<'_>,
        _t: &Dynamic,
        _idx: u32,
        _phase: bool,
    ) {
        self.fired.set(true);
    }
}

#[test]
fn decide_callback_fires_for_registered_bv() {
    // Two BV8 variables constrained to non-singleton ranges; Z3 must make bit-level
    // case splits to determine their values, which causes `decide` to fire.
    let fired = Rc::new(Cell::new(false));
    let solver = Solver::new();
    let x = BV::new_const("x_dec", 8);
    let y = BV::new_const("y_dec", 8);

    solver.set_propagator(
        DecideTracker {
            fired: fired.clone(),
        },
        || DecideTracker {
            fired: Rc::new(Cell::new(false)),
        },
    );
    solver.propagate_register(&x);
    solver.propagate_register(&y);

    // x < 3 and y > 200: satisfiable but neither variable is uniquely determined,
    // so Z3 must split on at least one registered variable.
    solver.assert(x.bvult(BV::from_u64(3, 8)));
    solver.assert(y.bvugt(BV::from_u64(200, 8)));

    assert_eq!(solver.check(), SatResult::Sat);
    assert!(
        fired.get(),
        "decide callback must fire when Z3 splits on a registered expression"
    );
}

// ── created callback + propagate_declare ─────────────────────────────────────

/// Records when `created` and `fixed` fire; registers discovered terms mid-callback.
struct CreatedTracker {
    created_fired: Rc<Cell<bool>>,
    fixed_fired: Rc<Cell<bool>>,
}

impl UserPropagator for CreatedTracker {
    fn push(&mut self) {}
    fn pop(&mut self, _: u32) {}

    fn created(&mut self, cb: &PropagatorCallbackHandle<'_>, t: &Dynamic) {
        self.created_fired.set(true);
        // Register the newly created term so `fixed` will fire when Z3 assigns it.
        cb.register(t);
    }

    fn fixed(&mut self, _cb: &PropagatorCallbackHandle<'_>, _ast: &Dynamic, _val: &Dynamic) {
        self.fixed_fired.set(true);
    }
}

#[test]
fn created_callback_fires_for_propagate_declare_function() {
    // `propagate_declare` registers a function with Z3's user-propagator machinery.
    // When Z3 internalizes any term whose top-level symbol is that function,
    // `created` fires. We then call `cb.register(t)` inside `created` (exercising the
    // `register_cb` code path); `fixed` fires once Z3 assigns a value to the term.
    let created_fired = Rc::new(Cell::new(false));
    let fixed_fired = Rc::new(Cell::new(false));
    let solver = Solver::new();

    // Declare f : S -> Bool as a propagator-owned function.
    let s_sort = Sort::uninterpreted("S_created".into());
    let f = solver.propagate_declare("f_created", &[&s_sort], &Sort::bool());

    // x : S (an uninterpreted constant).
    let x = FuncDecl::new("x_created", &[], &s_sort).apply(&[]);

    // f(x) : Bool — asserting this forces Z3 to internalize the term, firing `created`.
    let fx = f.apply(&[&x]).as_bool().unwrap();

    solver.set_propagator(
        CreatedTracker {
            created_fired: created_fired.clone(),
            fixed_fired: fixed_fired.clone(),
        },
        || CreatedTracker {
            created_fired: Rc::new(Cell::new(false)),
            fixed_fired: Rc::new(Cell::new(false)),
        },
    );

    solver.assert(&fx);
    assert_eq!(solver.check(), SatResult::Sat);

    assert!(
        created_fired.get(),
        "created callback must fire when Z3 internalizes a propagate_declare term"
    );
    assert!(
        fixed_fired.get(),
        "fixed callback must fire for the term registered via cb.register() inside created"
    );
}
