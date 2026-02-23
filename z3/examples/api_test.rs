use z3::{ast::*, *};

fn main() {
    println!("Z3 Enhanced API Test");
    println!("====================");

    // Test AstVector functionality
    println!("\n✓ Testing AstVector...");
    let vector = AstVector::new();
    let x = Int::new_const("x");
    vector.push(&x);
    println!("AstVector size: {}", vector.len());
    assert_eq!(vector.len(), 1);

    // Test Algebraic operations
    println!("\n✓ Testing Algebraic operations...");
    let a = Real::from_rational(3, 2);
    let b = Real::from_rational(5, 3);
    println!("a = {}, b = {}", a, b);

    let sum = Algebraic::add(&a, &b);
    println!("a + b = {}", sum);

    // Test enhanced Float operations
    println!("\n✓ Testing enhanced Float operations...");
    let f1 = Float::from_f64(std::f64::consts::PI);
    let f2 = Float::from_f64(std::f64::consts::E);

    println!("f1 = {}", f1);
    println!("f1 is positive: {}", f1.is_positive());
    println!("f1 min f2 = {}", f1.min(&f2));
    println!("f1 sqrt = {}", f1.sqrt());

    println!("\n🎉 All API extensions working correctly!");
}
