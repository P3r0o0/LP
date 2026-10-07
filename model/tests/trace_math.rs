use lwe_rust::kyber::gen::{expand_a, expand_s_and_e};
use lwe_rust::kyber::ntt::tomont;
use lwe_rust::kyber::pke::ML_KEM_512;
use lwe_rust::kyber::poly::{poly_basemul_montgomery, Poly};
use lwe_rust::kyber::sym::g;

#[test]
fn test_trace() {
    let d_hex = "3DEF73C558E1F5F2BFB4F6EAA36EE200CDF54580958CC2176282628FF508A016";
    let mut d = [0u8; 32];
    hex::decode_to_slice(d_hex, &mut d).unwrap();
    let mut d_k = d.to_vec();
    d_k.push(ML_KEM_512.k as u8);
    let g_out = g(&d_k);
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&g_out[0..32]);
    let mut sigma = [0u8; 32];
    sigma.copy_from_slice(&g_out[32..64]);

    let mut a_hat = [[Poly::new(); 4]; 4];
    expand_a(&rho, ML_KEM_512.k, &mut a_hat);
    
    let mut s = [Poly::new(); 4];
    let mut e = [Poly::new(); 4];
    expand_s_and_e(&sigma, ML_KEM_512.k, ML_KEM_512.eta1, &mut s, &mut e);

    for i in 0..ML_KEM_512.k {
        s[i].ntt();
        e[i].ntt();
    }

    println!("a_hat[0][1]: {:?}", &a_hat[0][1].coeffs[0..4]);
    println!("s_hat[1]: {:?}", &s[1].coeffs[0..4]);

    let mut prod0 = Poly::new();
    poly_basemul_montgomery(&mut prod0, &a_hat[0][0], &s[0]);
    println!("prod0: {:?}", &prod0.coeffs[0..4]);

    let mut prod1 = Poly::new();
    poly_basemul_montgomery(&mut prod1, &a_hat[0][1], &s[1]);
    println!("prod1: {:?}", &prod1.coeffs[0..4]);

    let mut sum = Poly::new();
    sum.add(&prod0);
    sum.add(&prod1);
    println!("sum (R^-1): {:?}", &sum.coeffs[0..4]);

    tomont(&mut sum.coeffs);
    println!("sum (normal): {:?}", &sum.coeffs[0..4]);

    sum.add(&e[0]);
    println!("sum + e: {:?}", &sum.coeffs[0..4]);
}
