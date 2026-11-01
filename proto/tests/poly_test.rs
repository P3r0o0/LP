use lwe_rust::lwe::poly::Polynomial;

#[test]
fn test_polynomial_arithmetic() {
    let q = 3329;

    let p1 = Polynomial::new(vec![1, 2, 3, 4]);
    let p2 = Polynomial::new(vec![2, 1, 0, 0]);

    let p_add = p1.add(&p2, q);
    assert_eq!(p_add.coeffs, vec![3, 3, 3, 4]);

    let p_sub = p1.sub(&p2, q);
    assert_eq!(p_sub.coeffs, vec![1 + q - 2, 1, 3, 4]);

    let p_mul = p1.mul_schoolbook(&p2, q);
    assert_eq!(p_mul.coeffs, vec![q - 2, 5, 8, 11]);

    println!("Polynomial multiplication verified over Z_q[X]/(X^N + 1)");
}
