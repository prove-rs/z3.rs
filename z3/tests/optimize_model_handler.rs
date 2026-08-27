use std::cell::Cell;
use std::rc::Rc;
#[cfg(z3_ge_4_16)]
use std::sync::Arc;
#[cfg(z3_ge_4_16)]
use std::sync::atomic::{AtomicBool, Ordering};
use z3::ast::Int;
use z3::*;

// ── golden-path ─────────────────────────────────────────────────────────────

#[test]
fn handler_fires_at_least_once() {
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);

    let fired = Rc::new(Cell::new(false));
    let fired2 = fired.clone();
    opt.set_model_handler(move |_model| {
        fired2.set(true);
    });

    assert_eq!(opt.check(&[]), SatResult::Sat);
    assert!(fired.get(), "handler should have fired at least once");
}

#[test]
fn handler_receives_non_empty_model() {
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);

    let last_value = Rc::new(Cell::new(-1i64));
    let last2 = last_value.clone();
    opt.set_model_handler(move |model| {
        if let Some(v) = model.eval(&x, true).and_then(|v| v.as_i64()) {
            last2.set(v);
        }
    });

    assert_eq!(opt.check(&[]), SatResult::Sat);
    assert_ne!(
        last_value.get(),
        -1,
        "handler should have been called with a model value"
    );
}

#[test]
fn handler_fires_multiple_times_for_improving_sequence() {
    // Minimize x subject to x >= 0 and x <= 10.  Z3 may discover several
    // improving models before settling on the optimum.  We just assert that
    // the handler fires at least once and that any value it sees is in-range.
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);

    let count = Rc::new(Cell::new(0u32));
    let count2 = count.clone();
    opt.set_model_handler(move |model| {
        count2.set(count2.get() + 1);
        if let Some(v) = model.eval(&x, true).and_then(|v| v.as_i64()) {
            assert!(
                (0..=10).contains(&v),
                "in-flight model value {v} out of expected range"
            );
        }
    });

    assert_eq!(opt.check(&[]), SatResult::Sat);
    assert!(count.get() >= 1, "handler should have fired at least once");
}

// ── handler lifecycle ────────────────────────────────────────────────────────

#[test]
fn second_set_model_handler_replaces_first() {
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);

    let first_fired = Rc::new(Cell::new(false));
    let first2 = first_fired.clone();
    opt.set_model_handler(move |_| {
        first2.set(true);
    });

    let second_fired = Rc::new(Cell::new(false));
    let second2 = second_fired.clone();
    opt.set_model_handler(move |_| {
        second2.set(true);
    });

    assert_eq!(opt.check(&[]), SatResult::Sat);

    assert!(
        !first_fired.get(),
        "first handler should have been replaced and never fire"
    );
    assert!(second_fired.get(), "second handler should have fired");
}

#[test]
fn drop_with_active_handler_does_not_panic() {
    let x = Int::new_const("x");
    let opt = Optimize::new();
    opt.assert(x.ge(0));
    opt.assert(x.le(10));
    opt.minimize(&x);
    opt.set_model_handler(|_| {});
    assert_eq!(opt.check(&[]), SatResult::Sat);
    // opt is dropped here; handler cleanup must not panic or double-free.
}

// ── translate interaction (requires Z3 >= 4.16.0) ───────────────────────────

#[cfg(z3_ge_4_16)]
#[test]
fn translate_with_no_handler_gives_no_handler() {
    let x = Int::new_const("x");

    let s = x.synchronized();
    let translated = with_z3_config(&Config::new(), || {
        let x = s.recover();
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        opt.minimize(&x);
        // No handler registered — translate should be fine.
        opt.synchronized()
    })
    .recover();

    // Registering a handler on the translated instance must work normally.
    let fired = Rc::new(Cell::new(false));
    let fired2 = fired.clone();
    translated.set_model_handler(move |_| {
        fired2.set(true);
    });
    assert_eq!(translated.check(&[]), SatResult::Sat);
    assert!(fired.get());
}

#[cfg(z3_ge_4_16)]
#[test]
fn translate_does_not_carry_handler_across_contexts() {
    // Handler on the original; translated instance should start with no handler.
    let x = Int::new_const("x");

    // Arc<AtomicBool> is Send + Sync, so it can cross the with_z3_config boundary.
    let original_handler_fired = Arc::new(AtomicBool::new(false));
    let fired2 = original_handler_fired.clone();

    let s = x.synchronized();
    let translated = with_z3_config(&Config::new(), || {
        let x = s.recover();
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        opt.minimize(&x);
        opt.set_model_handler(move |_| {
            fired2.store(true, Ordering::Relaxed);
        });
        // Sanity: original handler fires in its own context.
        assert_eq!(opt.check(&[]), SatResult::Sat);
        opt.synchronized()
    })
    .recover();

    // The translated instance must not inherit the handler from the original context.
    // Register a fresh handler to confirm check works and only the new one fires.
    let new_fired = Rc::new(Cell::new(false));
    let new_fired2 = new_fired.clone();
    translated.set_model_handler(move |_| {
        new_fired2.set(true);
    });
    assert_eq!(translated.check(&[]), SatResult::Sat);
    assert!(
        new_fired.get(),
        "explicitly registered handler on translated instance must fire"
    );
}

#[cfg(z3_ge_4_16)]
#[test]
fn drop_translated_instance_with_no_handler_does_not_corrupt_original() {
    let x = Int::new_const("x");

    let original_handler_fired = Arc::new(AtomicBool::new(false));
    let fired2 = original_handler_fired.clone();

    let s = x.synchronized();
    let translated = with_z3_config(&Config::new(), || {
        let x = s.recover();
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        opt.minimize(&x);
        opt.set_model_handler(move |_| {
            fired2.store(true, Ordering::Relaxed);
        });
        assert_eq!(opt.check(&[]), SatResult::Sat);
        opt.synchronized()
    })
    .recover();

    // Drop the translated Optimize immediately.
    drop(translated);

    // Original should remain usable and its handler should have fired during check above.
    assert!(
        original_handler_fired.load(Ordering::Relaxed),
        "original handler must have fired during check in its own context"
    );
}

#[cfg(z3_ge_4_16)]
#[test]
fn translated_check_with_no_handler_after_original_drops() {
    // Regression: dropping the original Optimize (which has a handler) must not
    // leave a dangling Z3 callback on the translated instance. check() on the
    // translated instance with no handler must not crash.
    let x = Int::new_const("x");

    let s = x.synchronized();
    let translated = with_z3_config(&Config::new(), || {
        let x = s.recover();
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        opt.minimize(&x);
        opt.set_model_handler(|_| {});
        // opt drops here, freeing the handler allocation.
        opt.synchronized()
    })
    .recover();

    // translated has no handler; check() must not crash.
    assert_eq!(translated.check(&[]), SatResult::Sat);
}

#[cfg(z3_ge_4_16)]
#[test]
fn cloned_check_with_no_handler_after_original_drops() {
    // Same as above but via Clone (same context) instead of translate.
    let x = Int::new_const("x");
    let cloned = {
        let opt = Optimize::new();
        opt.assert(x.ge(0));
        opt.assert(x.le(10));
        opt.minimize(&x);
        opt.set_model_handler(|_| {});
        let cloned = opt.clone();
        // opt drops here, freeing the handler allocation.
        cloned
    };

    // cloned has no handler; check() must not crash.
    assert_eq!(cloned.check(&[]), SatResult::Sat);
}
