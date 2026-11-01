use lwe_rust::distributions::discrete_gaussian::DiscreteGaussian;
use lwe_rust::fhe::bfv::BFVContext;
use lwe_rust::lwe::distinguisher::prob_true;
use lwe_rust::lwe::generator::{sample_lwe, sample_lwe_with_secret};
use lwe_rust::lwe::math::{
    add_mod, centered_lift, ct_eq_slice, matrix_vec_mul, mul_mod, sub_mod, zeroize_slice,
    BarrettModulus,
};
use lwe_rust::lwe::module_ntt::ntt_evaluate;
use lwe_rust::lwe::ntt::{inv_ntt, ntt, ntt_mul, pow_mod};
use lwe_rust::lwe::poly::Polynomial;
use lwe_rust::params::LweParams;
use lwe_rust::zkp::mod_nizk::{ModNIZKProof, ModZKPParams, ModZKPPublicInfo, ModZKPWitness};
use lwe_rust::zkp::nizk::{NIZKProof, ZKPParams, ZKPPublicInfo, ZKPWitness};
use rand::rngs::StdRng;
use rand::SeedableRng;

#[test]
fn test_large_modulus_q_over_32bit() {
    let q: u64 = (1u64 << 50) + 15;
    let a = q - 3;
    let b = q - 5;

    assert_eq!(mul_mod(a, b, q), 15);
    assert_eq!(add_mod(a, b, q), q - 8);
    assert_eq!(sub_mod(a, b, q), 2);
    assert_eq!(centered_lift(a, q), -3);

    let n = 8;
    let t = 16;
    let ctx = BFVContext::new(n, q, t);
    let (sk, pk) = ctx.keygen();

    let pt1 = Polynomial::new(vec![1, 2, 3, 4, 5, 6, 7, 8]);
    let pt2 = Polynomial::new(vec![2, 0, 1, 3, 0, 2, 1, 4]);
    let ct1 = ctx.encrypt(&pk, &pt1);
    let ct2 = ctx.encrypt(&pk, &pt2);

    let rk = ctx.keygen_relin(&sk, 65536, 4);
    let ct_mul = ctx.mul(&ct1, &ct2, &rk);
    let dec_mul = ctx.decrypt(&sk, &ct_mul);
    let expected = pt1.mul_schoolbook(&pt2, t);
    assert_eq!(
        dec_mul.coeffs, expected.coeffs,
        "50-bit BFV multiplication failed!"
    );

    let q_ntt_large: u64 = 29 * (1u64 << 57) + 1;
    assert_eq!(
        pow_mod(3, q_ntt_large - 1, q_ntt_large),
        1,
        "q_ntt_large must be prime"
    );
    let psi = pow_mod(3, (q_ntt_large - 1) / 16, q_ntt_large);
    assert_eq!(
        pow_mod(psi, 8, q_ntt_large),
        q_ntt_large - 1,
        "psi^N must be -1 mod q"
    );

    let p1 = Polynomial::new(vec![
        q_ntt_large - 10,
        12345678901,
        0,
        5,
        9999999999,
        2,
        7,
        11,
    ]);
    let p2 = Polynomial::new(vec![3, q_ntt_large - 5, 42, 10000000000, 1, 0, 8, 9]);
    let p1_ntt = ntt(&p1, psi, q_ntt_large);
    let p2_ntt = ntt(&p2, psi, q_ntt_large);
    let prod_ntt = ntt_mul(&p1_ntt, &p2_ntt, q_ntt_large);
    let prod = inv_ntt(&prod_ntt, psi, q_ntt_large);
    let expected_prod = p1.mul_schoolbook(&p2, q_ntt_large);
    assert_eq!(
        prod.coeffs, expected_prod.coeffs,
        "62-bit NTT multiplication failed!"
    );
}

#[test]
fn test_zkp_hash_to_challenge_non_periodic_and_ternary() {
    let n = 128;
    let q = 65537;
    let params = ZKPParams::new(n, q, 24000, 128);
    let a = Polynomial::new((0..n as u64).collect());
    let t = Polynomial::new((100..(100 + n as u64)).collect());
    let w = Polynomial::new((200..(200 + n as u64)).collect());

    let c = params.hash_to_challenge(&a, &t, &w);
    assert_eq!(c.coeffs.len(), n);
    assert!(c.coeffs.iter().all(|&x| x == 0 || x == 1 || x == q - 1));
    assert_ne!(
        &c.coeffs[0..32],
        &c.coeffs[32..64],
        "Challenge polynomial should not repeat every 32 coefficients!"
    );
    assert_ne!(
        &c.coeffs[32..64],
        &c.coeffs[64..96],
        "Challenge polynomial should not repeat every 32 coefficients!"
    );
}

#[test]
fn test_zkp_verify_rejects_malformed_dimensions_without_panic() {
    let n = 16;
    let q = 3329;
    let params = ZKPParams::new(n, q, 1024, 16);
    let a = Polynomial::new(vec![1; n]);
    let witness = ZKPWitness {
        s: Polynomial::new(vec![1; n]),
        e: Polynomial::new(vec![0; n]),
    };
    let (pub_info, proof, _) = params.prove(&a, &witness);
    assert!(params.verify(&pub_info, &proof));

    let bad_proof_zs = NIZKProof {
        c: proof.c.clone(),
        z_s: Polynomial::new(vec![0; n - 1]),
        z_e: proof.z_e.clone(),
    };
    assert!(!params.verify(&pub_info, &bad_proof_zs));

    let bad_proof_c = NIZKProof {
        c: Polynomial::new(vec![0; n + 1]),
        z_s: proof.z_s.clone(),
        z_e: proof.z_e.clone(),
    };
    assert!(!params.verify(&pub_info, &bad_proof_c));

    let bad_pub = ZKPPublicInfo {
        a: Polynomial::new(vec![1; n - 2]),
        t: pub_info.t.clone(),
    };
    assert!(!params.verify(&bad_pub, &proof));

    let mod_params = ModZKPParams::new(2, 2, 16, 3329, 1024, 16, 1062);
    let mod_a = vec![vec![Polynomial::new(vec![1; 16]); 2]; 2];
    let mod_w = ModZKPWitness {
        s: vec![Polynomial::new(vec![0; 16]); 2],
        e: vec![Polynomial::new(vec![0; 16]); 2],
    };
    let (mod_pub, mod_proof, _) = mod_params.prove(&mod_a, &mod_w);
    assert!(mod_params.verify(&mod_pub, &mod_proof));

    let bad_mod_proof = ModNIZKProof {
        c: mod_proof.c.clone(),
        z_s: vec![Polynomial::new(vec![0; 16]); 1],
        z_e: mod_proof.z_e.clone(),
    };
    assert!(!mod_params.verify(&mod_pub, &bad_mod_proof));

    let bad_mod_pub = ModZKPPublicInfo {
        a: mod_pub.a.clone(),
        t: vec![Polynomial::new(vec![0; 15]); 2],
    };
    assert!(!mod_params.verify(&bad_mod_pub, &mod_proof));
}

#[test]
fn test_empty_matrix_and_zero_trials_edge_cases() {
    let empty_mat: Vec<Vec<u64>> = Vec::new();
    let s = vec![1, 2, 3];
    assert!(matrix_vec_mul(&empty_mat, &s, 3329).is_empty());

    let empty_ntt_a: Vec<Vec<Vec<u64>>> = Vec::new();
    let empty_ntt_e: Vec<Vec<u64>> = Vec::new();
    let ntt_s = vec![vec![1, 2, 3, 4]];
    assert!(ntt_evaluate(&empty_ntt_a, &ntt_s, &empty_ntt_e, 3329).is_empty());

    let empty_samples = [];
    assert_eq!(prob_true(&empty_samples, |_| true), 0.0);
}

#[test]
fn test_strong_fiat_shamir_domain_and_param_binding() {
    let n = 16;
    let q = 3329;
    let a = Polynomial::new(vec![1; n]);
    let t = Polynomial::new(vec![2; n]);
    let w = Polynomial::new(vec![3; n]);

    let params_b1 = ZKPParams::new(n, q, 1024, 16);
    let params_b2 = ZKPParams::new(n, q, 1200, 16);
    assert_ne!(
        params_b1.hash_to_challenge(&a, &t, &w).coeffs,
        params_b2.hash_to_challenge(&a, &t, &w).coeffs,
        "Strong Fiat-Shamir must bind bound_b into the challenge!"
    );

    let mod_params_1x1 = ModZKPParams::new(1, 1, n, q, 1024, 16, 1062);
    let mod_c = mod_params_1x1.hash_to_challenge(
        &vec![vec![a.clone()]],
        &vec![t.clone()],
        &vec![w.clone()],
    );
    assert_ne!(
        params_b1.hash_to_challenge(&a, &t, &w).coeffs,
        mod_c.coeffs,
        "Ring-LWE and Module-LWE NIZK must have distinct domain separators!"
    );

    let mod_params_b2 = ModZKPParams::new(1, 1, n, q, 1200, 16, 1062);
    let mod_c_b2 = mod_params_b2.hash_to_challenge(&vec![vec![a]], &vec![t], &vec![w]);
    assert_ne!(mod_c.coeffs, mod_c_b2.coeffs);
}

#[test]
fn test_nizk_rejects_noncanonical_and_nonternary_proofs() {
    let n = 16;
    let q = 3329;
    let params = ZKPParams::new(n, q, 1024, 16);
    let a = Polynomial::new(vec![1; n]);
    let witness = ZKPWitness {
        s: Polynomial::new(vec![1; n]),
        e: Polynomial::new(vec![0; n]),
    };
    let (pub_info, proof, _) = params.prove(&a, &witness);
    assert!(params.verify(&pub_info, &proof));

    let mut non_canon_zs = proof.clone();
    non_canon_zs.z_s.coeffs[0] += q;
    assert!(
        !params.verify(&pub_info, &non_canon_zs),
        "Verify must reject non-canonical z_s >= q!"
    );

    let mut non_canon_pub = ZKPPublicInfo {
        a: pub_info.a.clone(),
        t: pub_info.t.clone(),
    };
    non_canon_pub.a.coeffs[0] += q;
    assert!(
        !params.verify(&non_canon_pub, &proof),
        "Verify must reject non-canonical public key >= q!"
    );

    let mut non_ternary_c = proof.clone();
    non_ternary_c.c.coeffs[0] = 2;
    assert!(
        !params.verify(&pub_info, &non_ternary_c),
        "Verify must reject non-ternary challenge c!"
    );

    let mod_params = ModZKPParams::new(2, 2, n, q, 1024, 16, 1062);
    let mod_a = vec![vec![Polynomial::new(vec![1; n]); 2]; 2];
    let mod_w = ModZKPWitness {
        s: vec![Polynomial::new(vec![0; n]); 2],
        e: vec![Polynomial::new(vec![0; n]); 2],
    };
    let (mod_pub, mod_proof, _) = mod_params.prove(&mod_a, &mod_w);
    assert!(mod_params.verify(&mod_pub, &mod_proof));

    let mut bad_mod_zs = mod_proof.clone();
    bad_mod_zs.z_s[0].coeffs[0] += q;
    assert!(!mod_params.verify(&mod_pub, &bad_mod_zs));

    let mut bad_mod_c = mod_proof.clone();
    bad_mod_c.c.coeffs[0] = 2;
    assert!(!mod_params.verify(&mod_pub, &bad_mod_c));
}

#[test]
fn test_barrett_modulus_and_side_channel_primitives() {
    let primes = [17u64, 257, 3329, 65537, (1u64 << 50) + 15, (1u64 << 61) - 1];
    for &q in &primes {
        let bm = BarrettModulus::new(q);
        let test_vals = [0, 1, 2, q / 2, q - 2, q - 1];
        for &a in &test_vals {
            assert_eq!(bm.reduce_u64(a), a % q);
            assert_eq!(bm.reduce_u64(a + q), a % q);
            for &b in &test_vals {
                assert_eq!(
                    bm.mul_mod(a, b),
                    mul_mod(a, b, q),
                    "Barrett mul_mod mismatch for q={}, a={}, b={}",
                    q,
                    a,
                    b
                );
            }
        }
    }

    let v1 = vec![10u64, 20, 30, 40];
    let v2 = vec![10u64, 20, 30, 40];
    let v3 = vec![10u64, 20, 31, 40];
    assert!(ct_eq_slice(&v1, &v2));
    assert!(!ct_eq_slice(&v1, &v3));
    assert!(!ct_eq_slice(&v1, &[10, 20]));

    let mut secret_buf = vec![42u64, 99, 123456];
    zeroize_slice(&mut secret_buf);
    assert_eq!(secret_buf, vec![0, 0, 0]);
}

#[test]
fn test_deterministic_lwe_sampling_and_centered_bfv() {
    let params = LweParams::new(8, 16, 3329);
    let dist = DiscreteGaussian { eta: 2 };

    let mut rng1 = StdRng::seed_from_u64(12345);
    let mut rng2 = StdRng::seed_from_u64(12345);
    let inst1 = sample_lwe(&mut rng1, &params, &dist);
    let inst2 = sample_lwe(&mut rng2, &params, &dist);
    assert_eq!(inst1.a, inst2.a, "Seeded sample_lwe must be deterministic!");
    assert_eq!(inst1.b, inst2.b, "Seeded sample_lwe must be deterministic!");

    let s1 = vec![1, 2, 3, 4, 5, 6, 7, 8];
    let mut rng3 = StdRng::seed_from_u64(99999);
    let mut rng4 = StdRng::seed_from_u64(99999);
    let inst3 = sample_lwe_with_secret(&mut rng3, &params, &s1, &dist);
    let inst4 = sample_lwe_with_secret(&mut rng4, &params, &s1, &dist);
    assert_eq!(inst3.a, inst4.a);
    assert_eq!(inst3.b, inst4.b);

    let ctx = BFVContext::new(16, 65537, 16);
    let (sk, _) = ctx.keygen();
    assert!(
        sk.0.coeffs.iter().all(|&c| c == 0 || c == 1 || c == 65536),
        "BFV secret key must be centered ternary {{-1, 0, 1}} mod q"
    );
    let has_neg_one = (0..10).any(|_| {
        let (sk_i, _) = ctx.keygen();
        sk_i.0.coeffs.contains(&65536)
    });
    assert!(
        has_neg_one,
        "BFV ternary distribution must include -1 (q - 1)!"
    );
}
