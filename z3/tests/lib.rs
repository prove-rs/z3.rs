extern crate env_logger;
#[macro_use]
extern crate log;

extern crate z3;
use std::convert::TryInto;
use z3::ast::{Ast, Bool};
use z3::*;

#[cfg(feature = "arbitrary-size-numeral")]
extern crate num;
#[cfg(feature = "arbitrary-size-numeral")]
use num::bigint::BigInt;
#[cfg(feature = "arbitrary-size-numeral")]
use num::rational::BigRational;
#[cfg(feature = "arbitrary-size-numeral")]
use std::str::FromStr;

#[test]
fn test_config() {
    let _ = env_logger::try_init();
    let mut c = Config::new();
    c.set_proof_generation(true);
}

#[test]
fn test_context() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    cfg.set_proof_generation(true);
    let _ = Context::new(&cfg);
}

#[test]
fn test_sorts_and_symbols() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let _ = ast::Int::new_const(&ctx, "x");
    let _ = ast::Int::new_const(&ctx, "y");
}

#[test]
fn test_solving() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_solving_for_model() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let zero = ast::Int::from_i64(&ctx, 0);
    let two = ast::Int::from_i64(&ctx, 2);
    let seven = ast::Int::from_i64(&ctx, 7);

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    solver.assert(&y.gt(&zero));
    solver.assert(&y.rem(&seven)._eq(&two));
    let x_plus_two = ast::Int::add(&ctx, &[&x, &two]);
    solver.assert(&x_plus_two.gt(&seven));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_i64().unwrap();
    let yv = model.eval(&y).unwrap().as_i64().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv > yv);
    assert!(yv % 7 == 2);
    assert!(xv + 2 > 7);
}

#[test]
fn test_cloning_ast() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = x.clone();
    let zero = ast::Int::from_i64(&ctx, 0);

    let solver = Solver::new(&ctx);
    solver.assert(&x._eq(&zero));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_i64().unwrap();
    let yv = model.eval(&y).unwrap().as_i64().unwrap();
    assert_eq!(xv, 0);
    assert_eq!(yv, 0);
}

#[test]
fn test_format() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let ast = ast::Int::new_const(&ctx, "x");
    assert_eq!("x", format!("{}", ast));

    let int = Sort::int(&ctx);
    assert_eq!("Int", format!("{}", int));
}

#[test]
fn test_bitvectors() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let a = ast::BV::new_const(&ctx, "a", 64);
    let b = ast::BV::new_const(&ctx, "b", 64);
    let two = ast::BV::from_i64(&ctx, 2, 64);

    let solver = Solver::new(&ctx);
    solver.assert(&a.bvsgt(&b));
    solver.assert(&b.bvsgt(&two));
    let b_plus_two = b.bvadd(&two);
    solver.assert(&b_plus_two.bvsgt(&a));
    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let av = model.eval(&a).unwrap().as_i64().unwrap();
    let bv = model.eval(&b).unwrap().as_i64().unwrap();
    assert!(av > bv);
    assert!(bv > 2);
    assert!(bv + 2 > av);
}

#[test]
fn test_ast_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&destination);
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert_eq!(slv.check(), SatResult::Unsat);
}

#[test]
fn test_solver_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&destination);
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    let translated_slv = slv.translate(&source);
    // Add a new constraint, make the old one unsatisfiable, while the copy remains satisfiable.
    slv.assert(&translated_a._eq(&ast::Int::from_u64(&destination, 3)));
    assert_eq!(slv.check(), SatResult::Unsat);
    assert_eq!(translated_slv.check(), SatResult::Sat);
}

#[test]
fn test_model_translate() {
    let cfg = Config::new();
    let source = Context::new(&cfg);
    let a = ast::Int::new_const(&source, "a");

    let destination = Context::new(&cfg);
    let translated_a = a.translate(&destination);

    let slv = Solver::new(&source);
    slv.assert(&a._eq(&ast::Int::from_u64(&source, 2)));
    assert_eq!(slv.check(), SatResult::Sat);

    let model = slv.get_model().unwrap();
    assert_eq!(2, model.eval(&a).unwrap().as_i64().unwrap());
    let translated_model = model.translate(&destination);
    assert_eq!(
        2,
        translated_model
            .eval(&translated_a)
            .unwrap()
            .as_i64()
            .unwrap()
    );
}

#[test]
fn test_pb_ops_model() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Bool::new_const(&ctx, "x");
    let y = ast::Bool::new_const(&ctx, "y");
    let solver = Solver::new(&ctx);
    solver.push();

    solver.assert(&ast::Bool::pb_eq(&ctx, &[(&x, 1), (&y, 1)], 1));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!((xv && !yv) || (!xv && yv));

    solver.pop(1);
    solver.push();
    solver.assert(&ast::Bool::pb_ge(&ctx, &[(&x, 1), (&y, 1)], 2));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(xv && yv);

    solver.pop(1);
    solver.assert(&ast::Bool::pb_le(&ctx, &[(&x, 1), (&y, 1)], 0));
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x).unwrap().as_bool().unwrap();
    let yv = model.eval(&y).unwrap().as_bool().unwrap();
    info!("x: {}", xv);
    info!("y: {}", yv);
    assert!(!xv && !yv);
}

#[test]
fn function_ref_count() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let int_sort = Sort::int(&ctx);

    let _f = FuncDecl::new(&ctx, "f", &[&int_sort], &int_sort);
    let _g = FuncDecl::new(&ctx, "g", &[&int_sort], &int_sort);

    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_params() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");

    let mut params = Params::new(&ctx);
    params.set_bool("smt.mbqi", false);
    params.set_f64("smt.qi.eager_threshold", 5.0);
    params.set_u32("smt.qi.max_instances", 999);

    let solver = Solver::new(&ctx);
    solver.set_params(&params);
    solver.assert(&x.gt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_substitution() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = ast::Real::new_const(&ctx, "x");
    let y = ast::Real::new_const(&ctx, "y");
    let z = ast::Real::new_const(&ctx, "z");

    let x_plus_y = ast::Real::add(&ctx, &[&x, &y]);
    let x_plus_z = ast::Real::add(&ctx, &[&x, &z]);

    let substitutions = &[(&y, &z)];

    assert!(x_plus_y.substitute(substitutions) == x_plus_z);
}

#[test]
fn test_real_cmp() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::new_const(&ctx, "x");
    let x_plus_1 = ast::Real::add(&ctx, &[&x, &ast::Real::from_real(&ctx, 1, 1)]);
    // forall x, x < x + 1
    let forall = ast::forall_const(&ctx, &[&x.clone().into()], &[], &x.lt(&x_plus_1).into());

    solver.assert(&forall.try_into().unwrap());
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_arbitrary_size_real() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::from_real_str(&ctx, "99999999999999999999998", "99999999999999999999999")
        .unwrap();
    let y = ast::Real::from_real(&ctx, 1, 1);

    solver.assert(&x.lt(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_arbitrary_size_int() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Int::from_str(&ctx, "99999999999999999999998").unwrap();
    let one = ast::Int::from_i64(&ctx, 1);
    let y = ast::Int::from_str(&ctx, "99999999999999999999999").unwrap();

    solver.assert(&ast::Int::add(&ctx, &[&x, &one])._eq(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[cfg(feature = "arbitrary-size-numeral")]
#[test]
fn test_arbitrary_size_real_from_bigrational() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::Real::from_real_str(&ctx, "99999999999999999999998", "99999999999999999999999")
        .unwrap();
    let num = BigInt::from_str("99999999999999999999998").unwrap();
    let den = BigInt::from_str("99999999999999999999999").unwrap();
    let ratio = BigRational::new(num, den);
    let y = ast::Real::from_big_rational(&ctx, &ratio);

    solver.assert(&x._eq(&y));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[cfg(feature = "arbitrary-size-numeral")]
#[test]
fn test_arbitrary_size_int_from_bigint() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let num1 = BigInt::from_str("99999999999999999999998").unwrap();
    let x = ast::Int::from_big_int(&ctx, &num1);
    let y = ast::Int::from_i64(&ctx, 1);

    let num2 = BigInt::from_str("99999999999999999999999").unwrap();
    let z = ast::Int::from_big_int(&ctx, &num2);

    solver.assert(&ast::Int::add(&ctx, &[&x, &y])._eq(&z));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_string_eq() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "foo").unwrap();
    let z = ast::String::from_str(&ctx, "bar").unwrap();
    let h = ast::String::new_const(&ctx, "h");

    solver.assert(&x._eq(&y));
    solver.assert(&x._eq(&z).not());
    solver.assert(&h._eq(&x));
    assert_eq!(solver.check(), SatResult::Sat);

    solver.assert(&h._eq(&z));
    assert_eq!(solver.check(), SatResult::Unsat)
}

#[test]
fn test_string_concat() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "bar").unwrap();
    let z = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&ast::String::concat(&ctx, &[&x, &y])._eq(&z));
    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_string_prefix() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "foo").unwrap();
    let y = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&x.prefix(&y));
    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_string_suffix() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let x = ast::String::from_str(&ctx, "bar").unwrap();
    let y = ast::String::from_str(&ctx, "foobar").unwrap();

    solver.assert(&x.suffix(&y));
    assert_eq!(solver.check(), SatResult::Sat)
}

#[test]
fn test_solver_unknown() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    // Use a very short timeout to quickly return "unknown"
    cfg.set_timeout_msec(1);
    let ctx = Context::new(&cfg);

    // An open problem: find a model for x^3 + y^3 + z^3 == 42
    // See: https://en.wikipedia.org/wiki/Sums_of_three_cubes
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let z = ast::Int::new_const(&ctx, "z");
    let x_cube = ast::Int::mul(&ctx, &[&x, &x, &x]);
    let y_cube = ast::Int::mul(&ctx, &[&y, &y, &y]);
    let z_cube = ast::Int::mul(&ctx, &[&z, &z, &z]);
    let sum_of_cubes = &ast::Int::add(&ctx, &[&x_cube, &y_cube, &z_cube]);
    let sum_of_cubes_is_42 = sum_of_cubes._eq(&ast::Int::from_i64(&ctx, 42));

    let solver = Solver::new(&ctx);
    solver.assert(&sum_of_cubes_is_42);

    assert_eq!(solver.check(), SatResult::Unknown);
    assert!(solver.get_reason_unknown().is_some());
}

#[test]
fn test_optimize_unknown() {
    let _ = env_logger::try_init();
    let mut cfg = Config::new();
    // Use a very short timeout to quickly return "unknown"
    cfg.set_timeout_msec(1);
    let ctx = Context::new(&cfg);

    // An open problem: find a model for x^3 + y^3 + z^3 == 42
    // See: https://en.wikipedia.org/wiki/Sums_of_three_cubes
    let x = ast::Int::new_const(&ctx, "x");
    let y = ast::Int::new_const(&ctx, "y");
    let z = ast::Int::new_const(&ctx, "z");
    let x_cube = ast::Int::mul(&ctx, &[&x, &x, &x]);
    let y_cube = ast::Int::mul(&ctx, &[&y, &y, &y]);
    let z_cube = ast::Int::mul(&ctx, &[&z, &z, &z]);
    let sum_of_cubes = &ast::Int::add(&ctx, &[&x_cube, &y_cube, &z_cube]);
    let sum_of_cubes_is_42 = sum_of_cubes._eq(&ast::Int::from_i64(&ctx, 42));

    let optimize = Optimize::new(&ctx);
    optimize.assert(&sum_of_cubes_is_42);

    assert_eq!(optimize.check(&[]), SatResult::Unknown);
    assert!(optimize.get_reason_unknown().is_some());
}

#[test]
fn test_get_unsat_core() {
    let _ = env_logger::try_init();

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    assert!(
        solver.get_unsat_core().is_empty(),
        "no unsat core before assertions"
    );

    let x = ast::Int::new_const(&ctx, "x");

    let x_is_three = ast::Bool::new_const(&ctx, "x-is-three");
    solver.assert_and_track(&x._eq(&ast::Int::from_i64(&ctx, 3)), &x_is_three);

    let x_is_five = ast::Bool::new_const(&ctx, "x-is-five");
    solver.assert_and_track(&x._eq(&ast::Int::from_i64(&ctx, 5)), &x_is_five);

    assert!(
        solver.get_unsat_core().is_empty(),
        "no unsat core before checking"
    );

    let result = solver.check();
    assert_eq!(result, SatResult::Unsat);

    let unsat_core = solver.get_unsat_core();
    assert_eq!(unsat_core.len(), 2);
    assert!(unsat_core.contains(&x_is_three));
    assert!(unsat_core.contains(&x_is_five));
}

#[test]
fn test_datatype_builder() {
    let _ = env_logger::try_init();

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let maybe_int = DatatypeBuilder::new(&ctx, "MaybeInt")
        .variant("Nothing", vec![])
        .variant(
            "Just",
            vec![("int", DatatypeAccessor::Sort(Sort::int(&ctx)))],
        )
        .finish();

    let nothing = maybe_int.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let just_five = maybe_int.variants[1]
        .constructor
        .apply(&[&five.clone().into()]);

    let nothing_is_nothing = maybe_int.variants[0]
        .tester
        .apply(&[&nothing])
        .as_bool()
        .unwrap();
    solver.assert(&nothing_is_nothing);

    let nothing_is_just = maybe_int.variants[1]
        .tester
        .apply(&[&nothing])
        .as_bool()
        .unwrap();
    solver.assert(&nothing_is_just.not());

    let just_five_is_nothing = maybe_int.variants[0]
        .tester
        .apply(&[&just_five])
        .as_bool()
        .unwrap();
    solver.assert(&just_five_is_nothing.not());

    let just_five_is_just = maybe_int.variants[1]
        .tester
        .apply(&[&just_five])
        .as_bool()
        .unwrap();
    solver.assert(&just_five_is_just);

    let five_two = maybe_int.variants[1].accessors[0]
        .apply(&[&just_five])
        .as_int()
        .unwrap();
    solver.assert(&five._eq(&five_two));

    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_recursive_datatype() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let list_sort = DatatypeBuilder::new(&ctx, "List")
        .variant("nil", vec![])
        .variant(
            "cons",
            vec![
                ("car", DatatypeAccessor::Sort(Sort::int(&ctx))),
                ("cdr", DatatypeAccessor::Datatype("List".into())),
            ],
        )
        .finish();

    assert_eq!(list_sort.variants.len(), 2);
    let nil = list_sort.variants[0].constructor.apply(&[]);
    let five = ast::Int::from_i64(&ctx, 5);
    let cons_five_nil = list_sort.variants[1]
        .constructor
        .apply(&[&five.clone().into(), &nil]);

    let nil_is_nil = list_sort.variants[0]
        .tester
        .apply(&[&nil])
        .as_bool()
        .unwrap();
    solver.assert(&nil_is_nil);

    let nil_is_cons = list_sort.variants[1]
        .tester
        .apply(&[&nil])
        .as_bool()
        .unwrap();
    solver.assert(&nil_is_cons.not());

    let cons_five_nil_is_nil = list_sort.variants[0]
        .tester
        .apply(&[&cons_five_nil])
        .as_bool()
        .unwrap();
    solver.assert(&cons_five_nil_is_nil.not());

    let cons_five_nil_is_cons = list_sort.variants[1]
        .tester
        .apply(&[&cons_five_nil])
        .as_bool()
        .unwrap();
    solver.assert(&cons_five_nil_is_cons);

    let car_cons_five_is_five = list_sort.variants[1].accessors[0]
        .apply(&[&cons_five_nil])
        .as_int()
        .unwrap();
    solver.assert(&car_cons_five_is_five._eq(&five));
    assert_eq!(solver.check(), SatResult::Sat);

    let cdr_cons_five_is_nil = list_sort.variants[1].accessors[1]
        .apply(&[&cons_five_nil])
        .as_datatype()
        .unwrap();
    solver.assert(&cdr_cons_five_is_nil._eq(&nil.as_datatype().unwrap()));
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn test_mutually_recursive_datatype() {
    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let tree_builder = DatatypeBuilder::new(&ctx, "Tree")
        .variant(
            "leaf",
            vec![("val", DatatypeAccessor::Sort(Sort::int(&ctx)))],
        )
        .variant(
            "node",
            vec![("children", DatatypeAccessor::Datatype("TreeList".into()))],
        );

    let tree_list_builder = DatatypeBuilder::new(&ctx, "TreeList")
        .variant("nil", vec![])
        .variant(
            "cons",
            vec![
                ("car", DatatypeAccessor::Datatype("Tree".into())),
                ("cdr", DatatypeAccessor::Datatype("TreeList".into())),
            ],
        );

    let sorts = z3::datatype_builder::create_datatypes(vec![tree_builder, tree_list_builder]);
    assert_eq!(sorts.len(), 2);
    let tree_sort = &sorts[0];
    assert_eq!(tree_sort.variants.len(), 2);
    assert_eq!(tree_sort.variants[0].accessors.len(), 1);
    assert_eq!(tree_sort.variants[1].accessors.len(), 1);

    let tree_list_sort = &sorts[1];
    assert_eq!(tree_list_sort.variants.len(), 2);
    assert_eq!(tree_list_sort.variants[0].accessors.len(), 0);
    assert_eq!(tree_list_sort.variants[1].accessors.len(), 2);

    let ten = ast::Int::from_i64(&ctx, 10);
    let leaf_ten = tree_sort.variants[0]
        .constructor
        .apply(&[&ten.clone().into()]);
    let leaf_ten_val_is_ten = tree_sort.variants[0].accessors[0]
        .apply(&[&leaf_ten])
        .as_int()
        .unwrap();
    solver.assert(&leaf_ten_val_is_ten._eq(&ten.clone().into()));
    assert_eq!(solver.check(), SatResult::Sat);

    let nil = tree_list_sort.variants[0].constructor.apply(&[]);
    let twenty = ast::Int::from_i64(&ctx, 20);
    let leaf_twenty = tree_sort.variants[0]
        .constructor
        .apply(&[&twenty.clone().into()]);
    let cons_leaf_twenty_nil = tree_list_sort.variants[1]
        .constructor
        .apply(&[&leaf_twenty, &nil]);
    let cons_leaf_ten_cons_leaf_twenty_nil = tree_list_sort.variants[1]
        .constructor
        .apply(&[&leaf_ten, &cons_leaf_twenty_nil]);

    // n1 = Tree.node(TreeList.cons(Tree.leaf(10), TreeList.cons(Tree.leaf(20), TreeList.nil)))
    let n1 = tree_sort.variants[1]
        .constructor
        .apply(&[&cons_leaf_ten_cons_leaf_twenty_nil]);

    let n1_cons_nil = tree_list_sort.variants[1].constructor.apply(&[&n1, &nil]);
    // n2 = Tree.node(TreeList.cons(n1, TreeList.nil))
    let n2 = tree_sort.variants[1].constructor.apply(&[&n1_cons_nil]);

    solver.assert(&n2._eq(&n1).not());

    // assert(TreeList.car(Tree.children(n2)) == n1)
    solver.assert(
        &tree_list_sort.variants[1].accessors[0]
            .apply(&[&tree_sort.variants[1].accessors[0].apply(&[&n2])])
            ._eq(&n1)
    );
    assert_eq!(solver.check(), SatResult::Sat);
}

#[test]
fn get_model_without_check_does_not_exit() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    solver.get_model();
}

#[test]
fn check_application_of_tactic_to_goal() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let tactic = Tactic::new(&ctx, "ctx-solver-simplify");
    let repeat_tactic = Tactic::repeat(&ctx, tactic, 100);

    let goal = Goal::new(&ctx, false, false, false);
    let x = ast::Bool::new_const(&ctx, "x");
    goal.assert(&x);

    let y = ast::Int::new_const(&ctx, "y");
    let two = ast::Int::from_i64(&ctx, 2);
    let y_greater_than_two = y.ge(&two);
    goal.assert(&y_greater_than_two);

    let one = ast::Int::from_i64(&ctx, 1);
    let y_greater_than_one = y.ge(&one);
    goal.assert(&y_greater_than_one);

    assert_eq!(format!("{}", goal), "(goal\n  x\n  (>= y 2)\n  (>= y 1))");
    let goal_result = repeat_tactic.apply(&goal, &params);
    assert_eq!(format!("{}", goal_result), "(goal\n  x\n  (>= y 2))");
}

#[test]
fn test_goal_depth() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_depth(), 0);
}

#[test]
fn test_goal_size() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_size(), 2);
}

#[test]
fn test_goal_num_expr() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    goal.assert(&a);
    assert_eq!(goal.get_num_expr(), 1);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    goal.assert(&a);
    goal.assert(&b);
    assert_eq!(goal.get_num_expr(), 2);
}

#[test]
fn test_goal_get_precision() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let false_bool = ast::Bool::from_bool(&ctx, false);

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert_eq!(goal.get_precision(), z3::GoalPrec::Precise);
}

#[test]
fn test_goal_is_inconsistent() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert_eq!(goal.is_inconsistent(), true);

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&true_bool);
    assert_eq!(goal.is_inconsistent(), false);
}

#[test]
fn test_goal_is_sat() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&false_bool);
    assert_eq!(goal.is_decided_sat(), false);
    assert_eq!(goal.is_decided_unsat(), true);

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&true_bool);
    assert_eq!(goal.is_decided_unsat(), false);
    assert_eq!(goal.is_decided_sat(), true);
}

#[test]
fn test_goal_reset() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::Bool::new_const(&ctx, "a");
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a);
    assert_eq!(format!("{}", goal), "(goal\n  a)");
    goal.reset();
    assert_eq!(format!("{}", goal), "(goal)");
}

#[test]
#[should_panic]
fn test_goal_get_formulas_empty() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    goal.get_formulas::<Bool>();
}

#[test]
fn test_goal_get_formulas() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let goal = Goal::new(&ctx, false, false, false);
    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let c = ast::Bool::new_const(&ctx, "c");
    goal.assert(&a);
    goal.assert(&b);
    goal.assert(&c);
    assert_eq!(
        goal.get_formulas::<Bool>(),
        vec![a, b, c],
    );
}

#[test]
fn test_tactic_skip() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::create_skip(&ctx);
    let goal_result = tactic.apply(&goal, &params);
    assert_eq!(
        goal_result.get_formulas::<Bool>(),
        vec![a.clone(), b, a],
    );
}

#[test]
fn test_tactic_and_then() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::new(&ctx, "sat-preprocess");
    let and_then_tactic = tactic.and_then(Tactic::new(&ctx, "simplify"));
    let goal_result = and_then_tactic.apply(&goal, &params);
    assert_eq!(goal_result.get_formulas::<Bool>(), vec![a, b]);
}

#[test]
fn test_tactic_or_else() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let params = Params::new(&ctx);

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");
    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);

    let tactic = Tactic::new(&ctx, "sat-preprocess");
    let or_else_tactic = tactic.or_else(Tactic::new(&ctx, "simplify"));
    let goal_result = or_else_tactic.apply(&goal, &params);
    assert_eq!(goal_result.get_formulas::<Bool>(), vec![a, b]);
}


#[test]
fn test_goal_apply_tactic() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    pub fn test_apply_tactic(ctx: &Context, goal: Goal, before_formulas: Vec<Bool>, after_formulas: Vec<Bool>) {
        assert_eq!(goal.get_formulas::<Bool>(), before_formulas);
        let params = Params::new(&ctx);

        let tactic = Tactic::new(&ctx, "ctx-solver-simplify");
        let repeat_tactic = Tactic::repeat(&ctx, tactic, 100);
        let goal_result = repeat_tactic.apply(&goal, &params);
        assert_eq!(goal_result.get_formulas::<Bool>(), after_formulas);
    }

    let a = ast::Bool::new_const(&ctx, "a");
    let b = ast::Bool::new_const(&ctx, "b");

    let bools = [&a, &b, &a];
    let a_and_b_and_a = Bool::and(&ctx, &bools);
    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_b_and_a);
    test_apply_tactic(&ctx, goal, vec![a.clone(), b.clone(), a.clone()], vec![b.clone(), a.clone()]);

    let a_implies_b = ast::Bool::implies(&a, &b);
    let a_and_a_implies_b = Bool::and(&ctx, &[&a, &a_implies_b]);

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a_and_a_implies_b);
    test_apply_tactic(&ctx, goal, vec![a.clone(), a_implies_b.clone()], vec![a.clone(), b.clone()]);

    let goal = Goal::new(&ctx, false, false, false);
    goal.assert(&a);
    goal.assert(&a_implies_b.clone());
    test_apply_tactic(&ctx, goal, vec![a.clone(), a_implies_b.clone()], vec![a.clone(), b.clone()]);

    let true_bool = ast::Bool::from_bool(&ctx, true);
    let false_bool = ast::Bool::from_bool(&ctx, false);
    let goal = Goal::new(&ctx, false, false, false);
    let true_and_false_and_true = ast::Bool::and(&ctx, &[&true_bool, &false_bool, &true_bool]);
    goal.assert(&true_and_false_and_true);
    test_apply_tactic(&ctx, goal, vec![false_bool.clone()], vec![false_bool.clone()]);
}
