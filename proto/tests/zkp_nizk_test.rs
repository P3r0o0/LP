use lwe_rust::lwe::poly::Polynomial;
use lwe_rust::zkp::nizk::{ZKPParams, ZKPWitness};
use rand::Rng;

#[test]
fn test_zkp_nizk() {
    let n = 16;
    let q = 3329;
    let bound_b = 1024;
    let beta = 16;

    let params = ZKPParams::new(n, q, bound_b, beta);

    let mut rng = rand::thread_rng();

    let mut a_coeffs = vec![0; n];
    for i in 0..n {
        a_coeffs[i] = rng.gen_range(0..q);
    }
    let a = Polynomial::new(a_coeffs);

    let mut s_coeffs = vec![0; n];
    let mut e_coeffs = vec![0; n];
    for i in 0..n {
        s_coeffs[i] = match rng.gen_range(0..3) {
            0 => 0,
            1 => 1,
            _ => q - 1,
        };
        e_coeffs[i] = match rng.gen_range(0..3) {
            0 => 0,
            1 => 1,
            _ => q - 1,
        };
    }

    let witness = ZKPWitness {
        s: Polynomial::new(s_coeffs),
        e: Polynomial::new(e_coeffs),
    };

    println!("Starting NIZK Prove (Fiat-Shamir with Aborts)...");
    let (pub_info, proof, attempts) = params.prove(&a, &witness);
    println!("Proof generated after {} attempts.", attempts);

    let is_valid = params.verify(&pub_info, &proof);
    assert!(is_valid, "ZKP NIZK Verification Failed!");
    println!("ZKP NIZK Verification Passed!");
}
