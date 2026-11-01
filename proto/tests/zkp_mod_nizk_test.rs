use lwe_rust::lwe::poly::Polynomial;
use lwe_rust::zkp::mod_nizk::{ModZKPParams, ModZKPWitness};
use rand::Rng;

#[test]
fn test_zkp_mod_nizk() {
    let k = 2;
    let l = 3;
    let n = 16;
    let q = 3329;
    let bound_b = 1024;
    let beta = 16;
    let psi = 1062;

    let params = ModZKPParams::new(k, l, n, q, bound_b, beta, psi);

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

    let witness = ModZKPWitness { s, e };

    println!("Starting Module-LWE NIZK Prove (Fiat-Shamir with Aborts)...");
    let (pub_info, proof, attempts) = params.prove(&a, &witness);
    println!("Proof generated after {} attempts.", attempts);

    let is_valid = params.verify(&pub_info, &proof);
    assert!(is_valid, "Module-LWE NIZK Verification Failed!");
    println!("Module-LWE NIZK Verification Passed!");
}

#[test]
fn test_context_bound_nizk_signatures_and_acceptance_rate() {
    use lwe_rust::zkp::nizk::{ZKPParams, ZKPWitness};

    let zkp = ZKPParams::new(8, 3329, 512, 8);
    let rate = zkp.expected_acceptance_rate();
    assert!(
        rate > 0.70 && rate < 1.0,
        "Expected acceptance rate should be in (0.70, 1.0), got {}",
        rate
    );
    assert!((zkp.single_attempt_rejection_prob() - (1.0 - rate)).abs() < 1e-15);
    assert!(zkp.all_attempts_rejection_prob(100) < 1e-50);
    assert_eq!(zkp.unrejected_tv_distance(0), 0.0);
    assert!(zkp.unrejected_tv_distance(1) > 0.0);
    assert!(zkp.unrejected_tv_distance(4) > zkp.unrejected_tv_distance(1));
    assert!(zkp.unrejected_tv_distance(8) > zkp.unrejected_tv_distance(4));
    for s in 0..=8 {
        assert_eq!(zkp.accepted_zk_tv_distance(s), 0.0);
    }
    assert!(zkp.accepted_zk_tv_distance(9) > 0.0);
    assert!(zkp.accepted_zk_tv_distance(12) > zkp.accepted_zk_tv_distance(9));

    let a_std = Polynomial::new(vec![101, 202, 303, 404, 505, 606, 707, 808]);
    let witness_std = ZKPWitness {
        s: Polynomial::new(vec![1, 0, 3328, 1, 0, 1, 3328, 0]),
        e: Polynomial::new(vec![0, 1, 0, 3328, 1, 0, 0, 1]),
    };

    let msg = b"Transfer 100 tokens from Alice to Bob (nonce=42)";
    let (pub_std, sig_std, _) = zkp.prove_with_context(&a_std, &witness_std, msg);
    assert!(
        zkp.verify_with_context(&pub_std, &sig_std, msg),
        "Context-bound Ring-LWE NIZK signature must verify with matching message"
    );
    assert!(
        !zkp.verify_with_context(&pub_std, &sig_std, b"Transfer 999 tokens"),
        "Context-bound Ring-LWE NIZK signature must reject modified message!"
    );
    assert!(
        !zkp.verify(&pub_std, &sig_std),
        "Context-bound Ring-LWE NIZK signature must reject empty context!"
    );

    let mod_zkp = ModZKPParams::new(2, 2, 16, 3329, 1024, 16, 1062);
    assert!(
        mod_zkp.ntt_table.is_some(),
        "ModZKPParams::new should automatically populate precomputed NTTTable"
    );
    let mod_rate = mod_zkp.expected_acceptance_rate();
    assert!(
        mod_rate > 0.10 && mod_rate < 1.0,
        "Expected Module-LWE acceptance rate should be in (0.10, 1.0), got {}",
        mod_rate
    );
    assert!((mod_zkp.single_attempt_rejection_prob() - (1.0 - mod_rate)).abs() < 1e-15);
    assert!(mod_zkp.all_attempts_rejection_prob(1000) < 1e-100);
    assert_eq!(mod_zkp.unrejected_tv_distance(0), 0.0);
    assert!(mod_zkp.unrejected_tv_distance(8) > mod_zkp.unrejected_tv_distance(4));
    for s in 0..=16 {
        assert_eq!(mod_zkp.accepted_zk_tv_distance(s), 0.0);
    }
    assert!(mod_zkp.accepted_zk_tv_distance(17) > 0.0);
    assert!(mod_zkp.accepted_zk_tv_distance(20) > mod_zkp.accepted_zk_tv_distance(17));

    let a_mod: Vec<Vec<Polynomial>> = (0..2)
        .map(|r| {
            (0..2)
                .map(|c| {
                    Polynomial::new(
                        (0..16)
                            .map(|k| ((r * 101 + c * 53 + k * 19 + 7) % 3329) as u64)
                            .collect(),
                    )
                })
                .collect()
        })
        .collect();
    let witness_mod = ModZKPWitness {
        s: vec![
            Polynomial::new(vec![1, 0, 3328, 0, 1, 0, 0, 1, 0, 3328, 0, 1, 0, 0, 0, 1]),
            Polynomial::new(vec![0, 1, 0, 3328, 0, 1, 0, 0, 1, 0, 3328, 0, 1, 0, 0, 0]),
        ],
        e: vec![
            Polynomial::new(vec![0, 0, 1, 0, 3328, 0, 1, 0, 0, 1, 0, 0, 3328, 0, 1, 0]),
            Polynomial::new(vec![1, 0, 0, 1, 0, 3328, 0, 1, 0, 0, 1, 0, 0, 3328, 0, 0]),
        ],
    };

    let (pub_mod, sig_mod, _) = mod_zkp.prove_with_context(&a_mod, &witness_mod, msg);
    assert!(
        mod_zkp.verify_with_context(&pub_mod, &sig_mod, msg),
        "Context-bound Module-LWE NIZK signature must verify with matching message"
    );
    assert!(
        !mod_zkp.verify_with_context(&pub_mod, &sig_mod, b"Tampered message"),
        "Context-bound Module-LWE NIZK signature must reject tampered message!"
    );
    assert!(
        !mod_zkp.verify(&pub_mod, &sig_mod),
        "Context-bound Module-LWE NIZK signature must reject empty context!"
    );
}
