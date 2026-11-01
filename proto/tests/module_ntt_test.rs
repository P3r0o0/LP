use lwe_rust::lwe::module_ntt::*;
use lwe_rust::lwe::poly::Polynomial;
use rand::Rng;

#[test]
fn test_module_ntt_isomorphism() {
    let k = 3;
    let l = 2;
    let n = 128;
    let q = 3329;
    let psi = 17;

    let mut rng = rand::thread_rng();

    let mut a = vec![];
    for _ in 0..k {
        let mut row = vec![];
        for _ in 0..l {
            let mut coeffs = vec![0; n];
            for i in 0..n {
                coeffs[i] = rng.gen_range(0..q);
            }
            row.push(Polynomial::new(coeffs));
        }
        a.push(row);
    }

    let mut s = vec![];
    for _ in 0..l {
        let mut coeffs = vec![0; n];
        for i in 0..n {
            coeffs[i] = rng.gen_range(0..q);
        }
        s.push(Polynomial::new(coeffs));
    }

    let mut e = vec![];
    for _ in 0..k {
        let mut coeffs = vec![0; n];
        for i in 0..n {
            coeffs[i] = rng.gen_range(0..q);
        }
        e.push(Polynomial::new(coeffs));
    }

    let mut t_std = Vec::with_capacity(k);
    for i in 0..k {
        let mut sum = Polynomial::zero(n);
        for j in 0..l {
            sum = sum.add(&a[i][j].mul_schoolbook(&s[j], q), q);
        }
        sum = sum.add(&e[i], q);
        t_std.push(sum);
    }

    let a_ntt = matrix_ntt(&a, psi, q);
    let s_ntt = vector_ntt(&s, psi, q);
    let e_ntt = vector_ntt(&e, psi, q);

    let t_eval = ntt_evaluate(&a_ntt, &s_ntt, &e_ntt, q);

    let t_fast = vector_intt(&t_eval, psi, q);

    for i in 0..k {
        assert_eq!(
            t_std[i].coeffs, t_fast[i].coeffs,
            "NTT Matrix-Vector evaluation mismatch at index {}!",
            i
        );
    }
    println!("Module-LWE NTT Matrix-Vector Isomorphism Verified Successfully!");
}
