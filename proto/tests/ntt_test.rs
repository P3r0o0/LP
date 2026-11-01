use lwe_rust::lwe::ntt::{inv_ntt, inv_ntt_naive, ntt, ntt_mul, ntt_naive, pow_mod, NTTTable};
use lwe_rust::lwe::poly::Polynomial;
use std::time::Instant;

fn find_primitive_root(two_n: u64, q: u64) -> Option<u64> {
    for psi in 2..q {
        if pow_mod(psi, two_n, q) == 1 {
            let mut ok = true;
            for k in 1..two_n {
                if pow_mod(psi, k, q) == 1 {
                    ok = false;
                    break;
                }
            }
            if ok {
                return Some(psi);
            }
        }
    }
    None
}

#[test]
fn test_ntt_isomorphism() {
    let n = 16;
    let q = 97;

    let psi = find_primitive_root((2 * n) as u64, q).expect("No primitive root found!");
    println!("Found primitive 32nd root of unity mod {}: {}", q, psi);

    let mut coeffs1 = vec![0u64; n];
    let mut coeffs2 = vec![0u64; n];
    for i in 0..n {
        coeffs1[i] = i as u64;
        coeffs2[i] = (n - i) as u64;
    }
    let p1 = Polynomial::new(coeffs1);
    let p2 = Polynomial::new(coeffs2);

    let p_mul_schoolbook = p1.mul_schoolbook(&p2, q);

    let ntt1 = ntt(&p1, psi, q);
    let ntt2 = ntt(&p2, psi, q);

    let ntt_prod = ntt_mul(&ntt1, &ntt2, q);

    let p_mul_ntt = inv_ntt(&ntt_prod, psi, q);

    assert_eq!(
        p_mul_schoolbook.coeffs, p_mul_ntt.coeffs,
        "NTT multiplication failed to match schoolbook!"
    );

    println!("NTT Isomorphism perfectly verified! Schoolbook and NTT results match exactly.");
}

#[test]
fn test_fast_ntt_matches_naive_and_benchmark() {
    let n = 1024;
    let q = 65537u64;
    let psi = pow_mod(3, (q - 1) / ((2 * n) as u64), q);
    assert_eq!(pow_mod(psi, n as u64, q), q - 1);

    let coeffs: Vec<u64> = (0..n).map(|i| ((i * 1337 + 42) as u64) % q).collect();
    let poly = Polynomial::new(coeffs);

    let t0 = Instant::now();
    let evals_naive = ntt_naive(&poly, psi, q);
    let rec_naive = inv_ntt_naive(&evals_naive, psi, q);
    let dt_naive = t0.elapsed();

    let t1 = Instant::now();
    let evals_fast = ntt(&poly, psi, q);
    let rec_fast = inv_ntt(&evals_fast, psi, q);
    let dt_fast = t1.elapsed();

    assert_eq!(
        evals_fast, evals_naive,
        "Fast O(N log N) NTT must match naive O(N^2) NTT exactly!"
    );
    assert_eq!(
        rec_fast.coeffs, poly.coeffs,
        "Fast INTT(NTT(p)) must recover p!"
    );
    assert_eq!(
        rec_naive.coeffs, poly.coeffs,
        "Naive INTT(NTT(p)) must recover p!"
    );

    println!(
        "N = 1024 NTT+INTT: naive O(N^2) = {:?}, fast O(N log N) = {:?} ({:.1}x faster)",
        dt_naive,
        dt_fast,
        dt_naive.as_nanos() as f64 / dt_fast.as_nanos().max(1) as f64
    );
}

#[test]
fn test_precomputed_ntt_table_with_barrett() {
    let n = 1024;
    let q = 65537u64;
    let psi = pow_mod(3, (q - 1) / ((2 * n) as u64), q);

    let table = NTTTable::new(n, psi, q);
    let p1 = Polynomial::new((0..n).map(|i| ((i * 73 + 19) as u64) % q).collect());
    let p2 = Polynomial::new((0..n).map(|i| ((i * 29 + 5) as u64) % q).collect());

    let t0 = Instant::now();
    let f1 = ntt(&p1, psi, q);
    let rec1 = inv_ntt(&f1, psi, q);
    let dt_onthefly = t0.elapsed();

    let t1 = Instant::now();
    let f_table = table.forward(&p1);
    let rec_table = table.inverse(&f_table);
    let dt_table = t1.elapsed();

    assert_eq!(f_table, f1, "NTTTable::forward must match ntt bit-for-bit!");
    assert_eq!(
        rec_table.coeffs, p1.coeffs,
        "NTTTable::inverse must recover p1!"
    );
    assert_eq!(rec1.coeffs, p1.coeffs);

    let prod_table = table.mul_ntt(&p1, &p2);
    let prod_schoolbook = p1.mul_schoolbook(&p2, q);
    assert_eq!(
        prod_table.coeffs, prod_schoolbook.coeffs,
        "NTTTable::mul_ntt must match schoolbook multiplication!"
    );

    println!(
        "N = 1024 NTT+INTT: on-the-fly = {:?}, precomputed NTTTable+Barrett = {:?} ({:.2}x faster)",
        dt_onthefly,
        dt_table,
        dt_onthefly.as_nanos() as f64 / dt_table.as_nanos().max(1) as f64
    );
}
