use lwe_rust::lwe::kem::ModKEMContext;
use lwe_rust::lwe::pke::{ModPKECiphertext, ModPKEContext, ModPKEPublicKey};
use lwe_rust::lwe::poly::Polynomial;
use lwe_rust::zkp::mod_nizk::{ModNIZKProof, ModZKPParams, ModZKPWitness};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

#[test]
fn test_verifiable_keygen() {
    println!("=== Verifiable Key Generation for Module-LWE PKE ===");

    let k = 2;
    let l = 2;
    let n = 128;
    let q = 65537;

    let mut psi = 1u64;
    for _ in 0..256 {
        psi = (psi * 3) % q;
    }

    let bound_b = 24000;
    let beta = 128;

    let params = ModZKPParams::new(k, l, n, q, bound_b, beta, psi);
    let mut rng = rand::thread_rng();

    println!("1. Prover generates secret key (s, e)...");
    let mut s = vec![];
    for _ in 0..l {
        let mut coeffs = vec![0; n];
        for i in 0..n {
            coeffs[i] = match rng.gen_range(0..3) {
                0 => 0,
                1 => 1,
                _ => q - 1,
            };
        }
        s.push(Polynomial::new(coeffs));
    }

    let mut e = vec![];
    for _ in 0..k {
        let mut coeffs = vec![0; n];
        for i in 0..n {
            coeffs[i] = match rng.gen_range(0..3) {
                0 => 0,
                1 => 1,
                _ => q - 1,
            };
        }
        e.push(Polynomial::new(coeffs));
    }

    println!("2. Prover generates public matrix A...");
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

    let witness = ModZKPWitness {
        s: s.clone(),
        e: e.clone(),
    };

    println!("3. Prover computes t = A*s + e and generates NIZK proof...");
    let (pub_info, proof, attempts) = params.prove(&a, &witness);
    println!(
        "   -> Proof generated successfully in {} attempts!",
        attempts
    );

    println!("4. Verifier receives public key (A, t) and the proof...");
    let is_valid = params.verify(&pub_info, &proof);

    assert!(is_valid, "Verifiable KeyGen Proof Failed!");
    println!("   -> Public Key is mathematically verified to be well-formed (s, e are small)!");
    println!("=== Verifiable Key Generation Completed ===");
}

#[test]
fn test_verifiable_module_lwe_pke_end_to_end() {
    let k = 2;
    let n = 128;
    let q = 65537u64;
    let t = 16u64;
    let mut psi = 1u64;
    for _ in 0..256 {
        psi = (psi * 3) % q;
    }

    let bound_b = 24000;
    let beta = 128;

    let pke = ModPKEContext::new(k, n, q, t, psi);

    let (sk, pk, proof, attempts) = pke.verifiable_keygen(bound_b, beta);
    assert!(attempts >= 1);
    assert!(
        pke.verify_public_key(&pk, &proof, bound_b, beta),
        "ModPKE public key NIZK verification failed!"
    );

    let msg_coeffs: Vec<u64> = (0..n).map(|i| (i as u64 * 7 + 3) % t).collect();
    let pt = Polynomial::new(msg_coeffs);
    let ct = pke.encrypt(&pk, &pt);
    let dec = pke.decrypt(&sk, &ct);

    assert_eq!(
        dec.coeffs, pt.coeffs,
        "ModPKE decryption failed to recover plaintext!"
    );
}

#[test]
fn test_fujisaki_okamoto_cca2_kem_and_implicit_rejection() {
    let k = 2;
    let n = 128;
    let q = 65537u64;
    let t = 2u64;
    let mut psi = 1u64;
    for _ in 0..256 {
        psi = (psi * 3) % q;
    }

    let kem = ModKEMContext::new(k, n, q, t, psi);
    let (sk, pk) = kem.keygen();

    let (ct, k_enc) = kem.encaps(&pk);
    let k_dec = kem.decaps(&sk, &ct);
    assert_eq!(
        k_enc, k_dec,
        "FO-KEM decapsulation failed on valid ciphertext!"
    );

    let mut bad_ct_v = ct.clone();
    bad_ct_v.v.coeffs[0] = (bad_ct_v.v.coeffs[0] + 1) % q;
    let k_rej_v1 = kem.decaps(&sk, &bad_ct_v);
    let k_rej_v2 = kem.decaps(&sk, &bad_ct_v);
    assert_ne!(
        k_rej_v1, k_enc,
        "Tampered ciphertext ct.v must not decapsulate to k_enc!"
    );
    assert_eq!(
        k_rej_v1, k_rej_v2,
        "Implicit rejection key must be deterministic for same ct!"
    );

    let mut bad_ct_u = ct.clone();
    bad_ct_u.u[0].coeffs[0] = (bad_ct_u.u[0].coeffs[0] + 1) % q;
    let k_rej_u = kem.decaps(&sk, &bad_ct_u);
    assert_ne!(
        k_rej_u, k_enc,
        "Tampered ciphertext ct.u must not decapsulate to k_enc!"
    );
    assert_ne!(
        k_rej_u, k_rej_v1,
        "Different tampered ciphertexts must yield distinct PRF rejection keys!"
    );
}

#[test]
fn test_verifiable_encryption_ciphertext_nizk() {
    let k = 2;
    let n = 128;
    let q = 65537u64;
    let t = 16u64;
    let mut psi = 1u64;
    for _ in 0..256 {
        psi = (psi * 3) % q;
    }

    let bound_b = 24000;
    let beta = 128;
    let pke = ModPKEContext::new(k, n, q, t, psi);
    let (sk, pk) = pke.keygen();

    let pt = Polynomial::new((0..n).map(|i| (i as u64 * 5 + 1) % t).collect());
    let (ct, proof, attempts) = pke.verifiable_encrypt(&pk, &pt, bound_b, beta);
    assert!(attempts >= 1);

    assert!(
        pke.verify_ciphertext(&pk, &ct, &pt, &proof, bound_b, beta),
        "Verifiable encryption NIZK proof failed to verify!"
    );

    assert_eq!(pke.decrypt(&sk, &ct).coeffs, pt.coeffs);

    let mut pt_wrong = pt.clone();
    pt_wrong.coeffs[0] = (pt_wrong.coeffs[0] + 1) % t;
    assert!(
        !pke.verify_ciphertext(&pk, &ct, &pt_wrong, &proof, bound_b, beta),
        "Verify_ciphertext must reject proof for wrong plaintext!"
    );

    let mut ct_tampered = ct.clone();
    ct_tampered.u[0].coeffs[0] = (ct_tampered.u[0].coeffs[0] + 1) % q;
    assert!(
        !pke.verify_ciphertext(&pk, &ct_tampered, &pt, &proof, bound_b, beta),
        "Verify_ciphertext must reject tampered ciphertext!"
    );
}

#[test]
fn test_kem_malformed_inputs_and_canonical_serialization_kat() {
    let k = 2;
    let n = 128;
    let q = 65537u64;
    let mut psi = 1u64;
    for _ in 0..256 {
        psi = (psi * 3) % q;
    }

    let kem = ModKEMContext::new_binary(k, n, q, psi);
    assert_eq!(kem.pke.params.max_ternary_noise_bound(), 2 * 2 * 128 + 1);
    assert!(kem.pke.params.is_zero_failure_guaranteed());

    let mut rng1 = StdRng::seed_from_u64(0xCAFE_BABE_1234_5678);
    let mut rng2 = StdRng::seed_from_u64(0xCAFE_BABE_1234_5678);
    let (sk1, pk1) = kem.keygen_with_rng(&mut rng1);
    let (_sk2, pk2) = kem.keygen_with_rng(&mut rng2);
    assert_eq!(
        pk1, pk2,
        "Seeded KEM keygen must be bit-for-bit deterministic!"
    );

    let (ct1, k_shared1) = kem.encaps_with_rng(&mut rng1, &pk1);
    let (ct2, k_shared2) = kem.encaps_with_rng(&mut rng2, &pk2);
    assert_eq!(
        ct1, ct2,
        "Seeded KEM encaps must be bit-for-bit deterministic!"
    );
    assert_eq!(k_shared1, k_shared2);
    assert_eq!(kem.decaps(&sk1, &ct1), k_shared1);

    let mut non_canon_ct = ct1.clone();
    non_canon_ct.v.coeffs[0] += q;
    let k_rej_noncanon = kem.decaps(&sk1, &non_canon_ct);
    assert_ne!(
        k_rej_noncanon, k_shared1,
        "decaps must reject non-canonical ciphertext coefficients >= q!"
    );

    let bad_len_ct = ModPKECiphertext {
        u: vec![Polynomial::zero(n); k - 1],
        v: Polynomial::zero(n - 3),
    };
    let k_rej_badlen = kem.decaps(&sk1, &bad_len_ct);
    assert_ne!(k_rej_badlen, k_shared1);

    let pk_bytes = pk1.to_bytes();
    let pk_decoded =
        ModPKEPublicKey::from_bytes(&pk_bytes, k, n, q).expect("Valid pk bytes must decode");
    assert_eq!(pk1, pk_decoded);
    assert!(ModPKEPublicKey::from_bytes(&pk_bytes[..pk_bytes.len() - 1], k, n, q).is_none());

    let ct_bytes = ct1.to_bytes();
    let ct_decoded =
        ModPKECiphertext::from_bytes(&ct_bytes, k, n, q).expect("Valid ct bytes must decode");
    assert_eq!(ct1, ct_decoded);

    let mut bad_ct_bytes = ct_bytes.clone();
    bad_ct_bytes[0..8].copy_from_slice(&q.to_le_bytes());
    assert!(
        ModPKECiphertext::from_bytes(&bad_ct_bytes, k, n, q).is_none(),
        "from_bytes must reject non-canonical coefficient == q!"
    );

    let bound_b = 24000;
    let beta = 128;
    let (_sk_v, pk_v, proof_v, _) = kem.pke.verifiable_keygen_with_rng(&mut rng1, bound_b, beta);
    let proof_bytes = proof_v.to_bytes();
    let proof_decoded =
        ModNIZKProof::from_bytes(&proof_bytes, k, k, n, q).expect("Valid proof bytes must decode");
    assert_eq!(proof_v, proof_decoded);
    assert!(kem
        .pke
        .verify_public_key(&pk_v, &proof_decoded, bound_b, beta));

    let mut bad_proof_bytes = proof_bytes.clone();
    bad_proof_bytes[0..8].copy_from_slice(&2u64.to_le_bytes());
    assert!(
        ModNIZKProof::from_bytes(&bad_proof_bytes, k, k, n, q).is_none(),
        "ModNIZKProof::from_bytes must reject non-ternary challenge c!"
    );
}

#[test]
fn test_seed_compressed_public_key_and_ciphertext_compression() {
    use lwe_rust::lwe::math::{compress_coeff, decompress_coeff, mul_mod, norm, BarrettModulus};
    use lwe_rust::lwe::pke::{ModPKECompressedPublicKey, ModPKESecretKey};

    for &q_large in &[(1u64 << 50) + 15, 29 * (1u64 << 57) + 1] {
        let barrett = BarrettModulus::new(q_large);
        let samples = [0u64, 1, 2, 123456789, q_large / 2, q_large - 3, q_large - 1];
        for &a in &samples {
            for &b in &samples {
                assert_eq!(
                    barrett.mul_mod(a, b),
                    mul_mod(a, b, q_large),
                    "62-bit BarrettModulus::mul_mod mismatch for q={}",
                    q_large
                );
            }
        }
    }

    let k = 2;
    let n = 64;
    let q = 3329u64;
    let t = 2u64;
    let psi = 17u64;
    let psi_64 = (psi * psi) % q;
    let pke = ModPKEContext::new(k, n, q, t, psi_64);

    let mut rng = StdRng::seed_from_u64(0xABCD_EF01_2345_6789);
    let (sk, pk_full, cpk) = pke.keygen_compressed_with_rng(&mut rng);
    assert!(sk.is_well_formed(k, n, q));
    assert!(cpk.is_well_formed(k, n, q));

    let cpk_bytes = cpk.to_bytes();
    assert_eq!(cpk_bytes.len(), 32 + k * n * 8);
    assert!(cpk_bytes.len() < pk_full.to_bytes().len() / 2);

    let cpk_restored =
        ModPKECompressedPublicKey::from_bytes(&cpk_bytes, k, n, q).expect("valid cpk bytes");
    let pk_decompressed = pke.decompress_public_key(&cpk_restored);
    assert_eq!(pk_full, pk_decompressed);

    let sk_bytes = sk.to_bytes();
    let sk_restored = ModPKESecretKey::from_bytes(&sk_bytes, k, n, q).expect("valid sk bytes");
    assert_eq!(sk, sk_restored);

    let d_u = 10u32;
    let d_v = 4u32;
    for x in 0..q {
        let y = compress_coeff(x, q, d_u);
        assert!(y < (1u64 << d_u));
        let x_rec = decompress_coeff(y, q, d_u);
        let diff = if x >= x_rec { x - x_rec } else { q + x - x_rec };
        let err = norm(diff, q);
        assert!(
            err <= 2,
            "Quantization error {} exceeded bound for x={}",
            err,
            x
        );
    }

    let pt = Polynomial::new((0..n).map(|i| (i as u64) % t).collect());
    let ct = pke.encrypt_with_rng(&mut rng, &pk_decompressed, &pt);
    let ct_compressed = ct.compress(q, d_u, d_v);
    let ct_decompressed = ct_compressed.decompress(q, d_u, d_v);

    let pt_dec = pke.decrypt(&sk_restored, &ct_decompressed);
    assert_eq!(
        pt_dec.coeffs, pt.coeffs,
        "Decryption of quantization-compressed Module-LWE ciphertext (du=10, dv=4) failed!"
    );
}
