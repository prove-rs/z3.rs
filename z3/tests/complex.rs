#![cfg(z3_5_3_1)]

use z3::ast::{Ast, Complex, Dynamic, Int, Real};
use z3::{SatResult, Solver, SortKind};

#[test]
fn sort_kind_and_dynamic_round_trip() {
    let z = Complex::new_const("z");
    assert_eq!(z.get_sort().kind(), SortKind::Complex);

    let d = Dynamic::from(&z);
    assert!(d.as_real().is_none());
    assert_eq!(d.as_complex().unwrap(), z);
    assert!(Complex::try_from(Dynamic::from(Real::new_const("r"))).is_err());
}

#[test]
fn projections_of_literal() {
    let z = Complex::from_rationals(1, 2, 3, 1);
    assert_eq!(z.real_part().simplify().as_rational(), Some((1, 2)));
    assert_eq!(z.imag_part().simplify().as_rational(), Some((3, 1)));
    assert_eq!(z.as_rationals(), Some(((1, 2), (3, 1))));
}

#[test]
fn embeddings_have_zero_imaginary_part() {
    assert_eq!(
        Complex::from(Real::from_rational(5, 2)).as_rationals(),
        Some(((5, 2), (0, 1)))
    );
    assert_eq!(
        Complex::from(Int::from_i64(-3)).as_rationals(),
        Some(((-3, 1), (0, 1)))
    );
}

#[test]
fn division_matches_z3_formula() {
    // (1+2i)/(3+4i) = (11 + 2i)/25
    let q = Complex::from_rationals(1, 1, 2, 1) / Complex::from_rationals(3, 1, 4, 1);
    assert_eq!(q.as_rationals(), Some(((11, 25), (2, 25))));
}

#[test]
fn square_root_of_minus_one() {
    let z = Complex::new_const("z");
    let solver = Solver::new();
    solver.assert((&z * &z).eq(Real::from_rational(-1, 1)));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let value = model.eval(&z, true).unwrap();
    let ((re_n, _), (im_n, im_d)) = value.as_rationals().unwrap();
    assert_eq!(re_n, 0);
    assert_eq!(im_n.abs(), im_d);
}

#[test]
fn operators_and_mixed_real_operands() {
    let z = Complex::new_const("z");
    let x = Real::new_const("x");
    let solver = Solver::new();
    solver.assert((&z + &x).eq(Complex::from_rationals(4, 1, 1, 1)));
    solver.assert(x.eq(Real::from_rational(1, 1)));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        model.eval(&z, true).unwrap().as_rationals(),
        Some(((3, 1), (1, 1)))
    );

    let mut w = Complex::from_rationals(1, 1, 1, 1);
    w *= Complex::from_rationals(1, 1, -1, 1);
    w -= Real::from_rational(2, 1);
    assert_eq!((-w).as_rationals(), Some(((0, 1), (0, 1))));

    let s: Complex = [
        Complex::from_rationals(1, 1, 0, 1),
        Complex::from_rationals(0, 1, 1, 1),
    ]
    .iter()
    .sum();
    assert_eq!(s.as_rationals(), Some(((1, 1), (1, 1))));
}

#[test]
fn equal_complexes_have_equal_parts() {
    let z = Complex::new_const("z");
    let w = Complex::new_const("w");
    let solver = Solver::new();
    solver.assert(z.eq(&w));
    solver.assert(z.real_part().ne(w.real_part()));
    assert_eq!(solver.check(), SatResult::Unsat);
}
