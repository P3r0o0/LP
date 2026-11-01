use lwe_rust::fhe::bfv::BFVContext;
use lwe_rust::lwe::ntt::pow_mod;
use lwe_rust::lwe::poly::Polynomial;

#[test]
fn test_bfv_fhe() {
    let n = 16;
    let q = 1_000_000_007;
    let t = 10;

    let ctx = BFVContext::new(n, q, t);

    let (sk, pk) = ctx.keygen();

    let mut m1 = vec![0u64; n];
    for i in 0..n {
        m1[i] = (i as u64) % t;
    }
    let pt1 = Polynomial::new(m1.clone());
    let ct1 = ctx.encrypt(&pk, &pt1);

    let mut m2 = vec![0u64; n];
    for i in 0..n {
        m2[i] = (9 - (i as u64) % t) % t;
    }
    let pt2 = Polynomial::new(m2.clone());
    let ct2 = ctx.encrypt(&pk, &pt2);

    let ct_add = ctx.add(&ct1, &ct2);

    let base = 1024;
    let l = 3;
    let rk = ctx.keygen_relin(&sk, base, l);

    let ct_mul = ctx.mul(&ct1, &ct2, &rk);

    let pt_dec1 = ctx.decrypt(&sk, &ct1);
    let pt_dec2 = ctx.decrypt(&sk, &ct2);
    let pt_add_dec = ctx.decrypt(&sk, &ct_add);
    let pt_mul_dec = ctx.decrypt(&sk, &ct_mul);

    assert_eq!(pt1.coeffs, pt_dec1.coeffs, "Decryption 1 failed!");
    assert_eq!(pt2.coeffs, pt_dec2.coeffs, "Decryption 2 failed!");

    for i in 0..n {
        let expected = (m1[i] + m2[i]) % t;
        assert_eq!(
            expected, pt_add_dec.coeffs[i],
            "Homomorphic addition failed at index {}",
            i
        );
    }

    let p1_p2_unred = pt1.mul_schoolbook_unreduced(&pt2);
    for i in 0..n {
        let mut expected = p1_p2_unred[i] % (t as i128);
        if expected < 0 {
            expected += t as i128;
        }
        assert_eq!(
            expected as u64, pt_mul_dec.coeffs[i],
            "Homomorphic multiplication failed at index {}",
            i
        );
    }

    println!("BFV FHE Module (Keygen, Encrypt, Decrypt, Homomorphic Add, Homomorphic Mul) verified successfully!");
}

#[test]
fn test_bfv_sub_plain_ops_and_ntt_acceleration() {
    let n = 64;
    let q = 998_244_353u64;
    let t = 16u64;
    let psi = pow_mod(3, (q - 1) / ((2 * n) as u64), q);
    assert_eq!(pow_mod(psi, n as u64, q), q - 1);

    let ctx = BFVContext::new_with_ntt(n, q, t, psi);
    let (sk, pk) = ctx.keygen();

    let m1: Vec<u64> = (0..n).map(|i| (i as u64 + 3) % t).collect();
    let m2: Vec<u64> = (0..n).map(|i| (i as u64 * 5 + 1) % t).collect();
    let m_plain: Vec<u64> = (0..n).map(|i| (i as u64 % 3) + 1).collect();

    let pt1 = Polynomial::new(m1);
    let pt2 = Polynomial::new(m2);
    let pt_plain = Polynomial::new(m_plain);

    let ct1 = ctx.encrypt(&pk, &pt1);
    let ct2 = ctx.encrypt(&pk, &pt2);

    let ct_sub = ctx.sub(&ct1, &ct2);
    let dec_sub = ctx.decrypt(&sk, &ct_sub);
    assert_eq!(dec_sub.coeffs, pt1.sub(&pt2, t).coeffs, "BFV sub failed!");

    let ct_add_plain = ctx.add_plain(&ct1, &pt_plain);
    let dec_add_plain = ctx.decrypt(&sk, &ct_add_plain);
    assert_eq!(
        dec_add_plain.coeffs,
        pt1.add(&pt_plain, t).coeffs,
        "BFV add_plain failed!"
    );

    let ct_sub_plain = ctx.sub_plain(&ct1, &pt_plain);
    let dec_sub_plain = ctx.decrypt(&sk, &ct_sub_plain);
    assert_eq!(
        dec_sub_plain.coeffs,
        pt1.sub(&pt_plain, t).coeffs,
        "BFV sub_plain failed!"
    );

    let ct_mul_plain = ctx.mul_plain(&ct1, &pt_plain);
    let dec_mul_plain = ctx.decrypt(&sk, &ct_mul_plain);
    assert_eq!(
        dec_mul_plain.coeffs,
        pt1.mul_schoolbook(&pt_plain, t).coeffs,
        "BFV mul_plain failed!"
    );

    let rk = ctx.keygen_relin(&sk, 1024, 3);
    let ct_mul = ctx.mul(&ct1, &ct2, &rk);
    let dec_mul = ctx.decrypt(&sk, &ct_mul);
    assert_eq!(
        dec_mul.coeffs,
        pt1.mul_schoolbook(&pt2, t).coeffs,
        "NTT-accelerated BFV mul failed!"
    );
}

#[test]
fn test_bfv_noise_budget_and_modulus_switch() {
    let n = 16;
    let q = 1_000_000_007u64;
    let t = 16u64;
    let ctx = BFVContext::new(n, q, t);
    let (sk, pk) = ctx.keygen();

    let pt1 = Polynomial::new((0..n).map(|i| (i as u64) % t).collect());
    let pt2 = Polynomial::new((0..n).map(|i| ((i * 3 + 1) as u64) % t).collect());
    let ct1 = ctx.encrypt(&pk, &pt1);
    let ct2 = ctx.encrypt(&pk, &pt2);

    let n1 = ctx.noise_norm(&sk, &ct1, &pt1);
    let n2 = ctx.noise_norm(&sk, &ct2, &pt2);
    let b1 = ctx.noise_budget_bits(&sk, &ct1, &pt1);
    assert!(
        b1 > 15,
        "Fresh encryption should have ample noise budget bits"
    );

    let ct_add_plain = ctx.add_plain(&ct1, &pt2);
    let pt_sum = pt1.add(&pt2, t);
    let pt_no_wrap = Polynomial::new(vec![1; n]);
    let pt1_small = Polynomial::new(vec![2; n]);
    let ct1_small = ctx.encrypt(&pk, &pt1_small);
    let n_small_before = ctx.noise_norm(&sk, &ct1_small, &pt1_small);
    let ct_small_add_plain = ctx.add_plain(&ct1_small, &pt_no_wrap);
    let n_small_after = ctx.noise_norm(&sk, &ct_small_add_plain, &Polynomial::new(vec![3; n]));
    assert_eq!(
        n_small_before, n_small_after,
        "add_plain must incur zero noise growth!"
    );
    let _ = (ct_add_plain, pt_sum);

    let pt2_small = Polynomial::new(vec![3; n]);
    let ct2_small = ctx.encrypt(&pk, &pt2_small);
    let n2_small = ctx.noise_norm(&sk, &ct2_small, &pt2_small);
    let ct_add_small = ctx.add(&ct1_small, &ct2_small);
    let n_add_small = ctx.noise_norm(&sk, &ct_add_small, &Polynomial::new(vec![5; n]));
    assert!(
        n_add_small <= n_small_before + n2_small,
        "Homomorphic addition noise must obey triangle inequality!"
    );

    let rk = ctx.keygen_relin(&sk, 1024, 3);
    let ct_mul = ctx.mul(&ct1, &ct2, &rk);
    let pt_mul = pt1.mul_schoolbook(&pt2, t);
    let b_mul = ctx.noise_budget_bits(&sk, &ct_mul, &pt_mul);
    assert!(
        b_mul > 0 && b_mul < b1,
        "Multiplication should consume noise budget while remaining > 0"
    );

    let q_new = 65537u64;
    let ct1_switched = ctx.modulus_switch(&ct1, q_new);
    let ctx_small = BFVContext::new(n, q_new, t);
    let sk_small_coeffs: Vec<u64> =
        sk.0.coeffs
            .iter()
            .map(|&c| if c == q - 1 { q_new - 1 } else { c })
            .collect();
    let sk_small = lwe_rust::fhe::bfv::SecretKey(Polynomial::new(sk_small_coeffs));
    let dec_switched = ctx_small.decrypt(&sk_small, &ct1_switched);
    assert_eq!(
        dec_switched.coeffs, pt1.coeffs,
        "Decryption after modulus_switch to q_new failed!"
    );
    let _ = n1 + n2;
}

#[test]
fn test_bfv_serialization_and_galois_automorphisms() {
    use lwe_rust::fhe::bfv::{Ciphertext, PublicKey};

    let n = 16;
    let q = 998_244_353u64;
    let t = 16u64;
    let psi = pow_mod(3, (q - 1) / ((2 * n) as u64), q);
    let ctx = BFVContext::new_with_ntt(n, q, t, psi);

    let (sk, pk) = ctx.keygen();
    assert!(pk.is_well_formed(n, q));

    let pk_bytes = pk.to_bytes();
    assert_eq!(pk_bytes.len(), 2 * n * 8);
    let pk_restored = PublicKey::from_bytes(&pk_bytes, n, q).expect("valid pk bytes");
    assert_eq!(pk, pk_restored);
    assert!(PublicKey::from_bytes(&pk_bytes[..pk_bytes.len() - 1], n, q).is_none());

    let mut bad_pk_bytes = pk_bytes.clone();
    bad_pk_bytes[0..8].copy_from_slice(&q.to_le_bytes());
    assert!(PublicKey::from_bytes(&bad_pk_bytes, n, q).is_none());

    let pt = Polynomial::new((0..n).map(|i| ((i * 5 + 3) as u64) % t).collect());
    let ct = ctx.encrypt(&pk, &pt);
    assert!(ct.is_well_formed(n, q));

    let ct_bytes = ct.to_bytes();
    assert_eq!(ct_bytes.len(), 2 * n * 8);
    let ct_restored = Ciphertext::from_bytes(&ct_bytes, n, q).expect("valid ct bytes");
    assert_eq!(ct, ct_restored);
    assert!(Ciphertext::from_bytes(&ct_bytes[1..], n, q).is_none());

    let mut bad_ct_bytes = ct_bytes.clone();
    bad_ct_bytes[8..16].copy_from_slice(&(q + 5).to_le_bytes());
    assert!(Ciphertext::from_bytes(&bad_ct_bytes, n, q).is_none());

    let pt2 = Polynomial::new((0..n).map(|i| ((i * 7 + 2) as u64) % t).collect());
    for &g in &[3usize, 5, 7, 2 * n - 1] {
        let lhs_add = pt.add(&pt2, t).apply_galois(g, t);
        let rhs_add = pt.apply_galois(g, t).add(&pt2.apply_galois(g, t), t);
        assert_eq!(
            lhs_add, rhs_add,
            "apply_galois must be additive for g={}",
            g
        );

        let lhs_mul = pt.mul_schoolbook(&pt2, t).apply_galois(g, t);
        let rhs_mul = pt
            .apply_galois(g, t)
            .mul_schoolbook(&pt2.apply_galois(g, t), t);
        assert_eq!(
            lhs_mul, rhs_mul,
            "apply_galois must be multiplicative for g={}",
            g
        );
    }

    let base = 1024u64;
    let l = 3usize;
    for &g in &[3usize, 5, 2 * n - 1] {
        let gk = ctx.keygen_galois(&sk, g, base, l);
        let ct_gal = ctx.apply_galois(&ct, &gk);
        assert!(ct_gal.is_well_formed(n, q));
        let dec_gal = ctx.decrypt(&sk, &ct_gal);
        let expected_gal = pt.apply_galois(g, t);
        assert_eq!(
            dec_gal.coeffs, expected_gal.coeffs,
            "Homomorphic Galois automorphism failed for g={}",
            g
        );
    }

    let gk3 = ctx.keygen_galois(&sk, 3, base, l);
    let gk5 = ctx.keygen_galois(&sk, 5, base, l);
    let ct_5 = ctx.apply_galois(&ct, &gk5);
    let ct_3_5 = ctx.apply_galois(&ct_5, &gk3);
    let dec_3_5 = ctx.decrypt(&sk, &ct_3_5);
    assert_eq!(
        dec_3_5.coeffs,
        pt.apply_galois(15, t).coeffs,
        "Composed Galois automorphisms sigma_3(sigma_5(ct)) must match sigma_15(pt)!"
    );
}

#[test]
fn test_bfv_simd_batch_encoder_and_key_serialization() {
    use lwe_rust::fhe::bfv::{BFVBatchEncoder, GaloisKey, RelinKey, SecretKey};

    let n = 16;
    let t = 97u64;
    let psi_t = pow_mod(5, (t - 1) / ((2 * n) as u64), t);
    assert_eq!(pow_mod(psi_t, n as u64, t), t - 1);

    let q = 998_244_353u64;
    let psi_q = pow_mod(3, (q - 1) / ((2 * n) as u64), q);
    assert_eq!(pow_mod(psi_q, n as u64, q), q - 1);

    let encoder = BFVBatchEncoder::new(n, t, psi_t);
    let ctx = BFVContext::new_with_ntt(n, q, t, psi_q);
    let (sk, pk) = ctx.keygen();
    let rk = ctx.keygen_relin(&sk, 1024, 3);
    let gk3 = ctx.keygen_galois(&sk, 3, 1024, 3);

    assert!(sk.is_well_formed(n, q));
    let sk_bytes = sk.to_bytes();
    let sk_restored = SecretKey::from_bytes(&sk_bytes, n, q).expect("valid sk bytes");
    assert_eq!(sk.0, sk_restored.0);

    assert!(rk.is_well_formed(n, q));
    let rk_bytes = rk.to_bytes();
    let rk_restored = RelinKey::from_bytes(&rk_bytes, n, q).expect("valid rk bytes");
    assert_eq!(rk, rk_restored);

    assert!(gk3.is_well_formed(n, q));
    let gk_bytes = gk3.to_bytes();
    let gk_restored = GaloisKey::from_bytes(&gk_bytes, n, q).expect("valid gk bytes");
    assert_eq!(gk3, gk_restored);

    let slots1: Vec<u64> = (0..n).map(|i| ((i * 7 + 3) as u64) % t).collect();
    let slots2: Vec<u64> = (0..n).map(|i| ((i * 5 + 11) as u64) % t).collect();

    let pt1 = encoder.encode_simd(&slots1);
    let pt2 = encoder.encode_simd(&slots2);
    assert_eq!(encoder.decode_simd(&pt1), slots1);
    assert_eq!(encoder.decode_simd(&pt2), slots2);

    let ct1 = ctx.encrypt(&pk, &pt1);
    let ct2 = ctx.encrypt(&pk, &pt2);

    let ct_add = ctx.add(&ct1, &ct2);
    let dec_add_slots = encoder.decode_simd(&ctx.decrypt(&sk, &ct_add));
    let expected_add: Vec<u64> = (0..n).map(|i| (slots1[i] + slots2[i]) % t).collect();
    assert_eq!(
        dec_add_slots, expected_add,
        "SIMD slot-wise addition failed!"
    );

    let ct_sub = ctx.sub(&ct1, &ct2);
    let dec_sub_slots = encoder.decode_simd(&ctx.decrypt(&sk, &ct_sub));
    let expected_sub: Vec<u64> = (0..n).map(|i| (slots1[i] + t - slots2[i]) % t).collect();
    assert_eq!(
        dec_sub_slots, expected_sub,
        "SIMD slot-wise subtraction failed!"
    );

    let ct_mul = ctx.mul(&ct1, &ct2, &rk_restored);
    let dec_mul_slots = encoder.decode_simd(&ctx.decrypt(&sk, &ct_mul));
    let expected_mul: Vec<u64> = (0..n).map(|i| (slots1[i] * slots2[i]) % t).collect();
    assert_eq!(
        dec_mul_slots, expected_mul,
        "SIMD slot-wise Hadamard multiplication failed!"
    );

    let ct_gal = ctx.apply_galois(&ct1, &gk_restored);
    let dec_gal_slots = encoder.decode_simd(&ctx.decrypt(&sk, &ct_gal));
    let expected_permuted = encoder.permute_slots(&slots1, 3);
    assert_eq!(
        dec_gal_slots, expected_permuted,
        "SIMD slot permutation under Galois automorphism sigma_3 failed!"
    );
}
