use z3::ast::Int;
use z3::*;

#[test]
fn test_optimize_translate() {
    let x = Int::new_const("x");
    let sx = x.synchronized();

    // Build an optimizer in a fresh context, then translate it back to the
    // thread-local context via synchronized() / recover().
    let opt = with_z3_config(&Config::new(), || {
        let x = sx.recover();
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        assert_eq!(opt.check(&[]), SatResult::Sat);
        opt.synchronized()
    })
    .recover();

    // After translation, the optimizer should still be satisfiable.
    assert_eq!(opt.check(&[]), SatResult::Sat);

    // Adding a contradiction in the original context should make it unsat.
    opt.assert(x.gt(10));
    assert_eq!(opt.check(&[]), SatResult::Unsat);
}

#[test]
fn test_optimize_clone() {
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);

    let cloned = opt.clone();

    // Add a stricter lower bound only to the clone.
    cloned.assert(x.ge(5));

    // Original should minimize to 0.
    assert_eq!(opt.check(&[]), SatResult::Sat);
    assert_eq!(
        opt.get_model()
            .unwrap()
            .eval(&x, true)
            .unwrap()
            .as_i64()
            .unwrap(),
        0
    );

    // Clone should minimize to 5 (due to the extra constraint).
    assert_eq!(cloned.check(&[]), SatResult::Sat);
    assert_eq!(
        cloned
            .get_model()
            .unwrap()
            .eval(&x, true)
            .unwrap()
            .as_i64()
            .unwrap(),
        5
    );
}
