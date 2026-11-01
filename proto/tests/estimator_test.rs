use lwe_rust::estimator::{
    estimate_dual_attack, estimate_mod_pke_failure, estimate_mod_pke_failure_asymmetric,
    estimate_primal_usvp_gsa, estimate_primal_usvp_simulator, root_hermite_factor,
    simulate_bkz_profile, DiscretePMF, LweEstimateInput, SecurityReport,
};
use lwe_rust::lwe::kem::ModKEMContext;
use lwe_rust::lwe::math::centered_lift;
use lwe_rust::lwe::pke::ModPKEParams;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

#[test]
fn test_root_hermite_factor_monotone_and_calibrated() {
    let d50 = root_hermite_factor(50);
    let d100 = root_hermite_factor(100);
    let d200 = root_hermite_factor(200);
    let d400 = root_hermite_factor(400);

    assert!((d50 - 1.0114).abs() < 0.001, "d50 = {d50}");
    assert!((d100 - 1.0090).abs() < 0.0005, "d100 = {d100}");
    assert!((d200 - 1.00628).abs() < 0.0005, "d200 = {d200}");
    assert!((d400 - 1.00397).abs() < 0.0005, "d400 = {d400}");
    assert!(d50 > d100 && d100 > d200 && d200 > d400);
}

#[test]
fn test_kyber_mlkem_calibration() {
    let kyber512 = LweEstimateInput::new_cbd(512, 768, 3329, 3, 3);
    let p512_gsa = estimate_primal_usvp_gsa(&kyber512);
    let p512_sim = estimate_primal_usvp_simulator(&kyber512, 15);
    let d512 = estimate_dual_attack(&kyber512);

    assert!(
        (p512_gsa.beta as isize - 406).abs() <= 10,
        "Kyber-512 GSA beta={} (expected ~406)",
        p512_gsa.beta
    );
    assert!(
        (p512_gsa.classical_bits - 118.55).abs() <= 3.0,
        "Kyber-512 classical_bits={}",
        p512_gsa.classical_bits
    );
    assert!(
        (p512_sim.beta as isize - 406).abs() <= 15,
        "Kyber-512 CN11 simulator beta={} (expected ~406)",
        p512_sim.beta
    );
    assert!(
        (d512.classical_bits - p512_gsa.classical_bits).abs() <= 6.0,
        "Kyber-512 dual bits={} vs primal bits={}",
        d512.classical_bits,
        p512_gsa.classical_bits
    );

    let kyber768 = LweEstimateInput::new_cbd(768, 1024, 3329, 2, 2);
    let p768_gsa = estimate_primal_usvp_gsa(&kyber768);
    let p768_sim = estimate_primal_usvp_simulator(&kyber768, 15);
    let d768 = estimate_dual_attack(&kyber768);
    assert!(
        (p768_gsa.beta as isize - 623).abs() <= 10,
        "Kyber-768 GSA beta={} (expected ~623)",
        p768_gsa.beta
    );
    assert!(
        (p768_gsa.classical_bits - 181.9).abs() <= 3.0,
        "Kyber-768 classical_bits={}",
        p768_gsa.classical_bits
    );
    assert!(
        (p768_sim.beta as isize - 623).abs() <= 20,
        "Kyber-768 CN11 simulator beta={} vs GSA beta={}",
        p768_sim.beta,
        p768_gsa.beta
    );

    let kyber1024 = LweEstimateInput::new_cbd(1024, 1280, 3329, 2, 2);
    let p1024_gsa = estimate_primal_usvp_gsa(&kyber1024);
    let p1024_sim = estimate_primal_usvp_simulator(&kyber1024, 15);
    let d1024 = estimate_dual_attack(&kyber1024);
    assert!(
        (p1024_gsa.beta as isize - 873).abs() <= 15,
        "Kyber-1024 GSA beta={} (expected ~873)",
        p1024_gsa.beta
    );
    assert!(
        (p1024_gsa.classical_bits - 254.9).abs() <= 4.5,
        "Kyber-1024 classical_bits={}",
        p1024_gsa.classical_bits
    );

    let cbd2 = DiscretePMF::cbd(2);
    let cbd3 = DiscretePMF::cbd(3);
    let (_, _, _, fail512_log2) =
        estimate_mod_pke_failure_asymmetric(512, 256, 3329, &cbd3, &cbd2, Some(10), Some(4));
    let (_, _, _, fail768_log2) =
        estimate_mod_pke_failure_asymmetric(768, 256, 3329, &cbd2, &cbd2, Some(10), Some(4));
    let (_, _, _, fail1024_log2) =
        estimate_mod_pke_failure_asymmetric(1024, 256, 3329, &cbd2, &cbd2, Some(11), Some(5));

    println!("=== MEASURED ML-KEM CALIBRATION ===");
    println!(
        "ML-KEM-512 : GSA beta={}, Sim beta={}, Dual beta={}, CoreSVP={:.1}, Quantum={:.1}, d4f={:.1}, DualBits={:.1}, log2(p_fail)={:.1}",
        p512_gsa.beta, p512_sim.beta, d512.beta, p512_gsa.classical_bits, p512_gsa.quantum_bits, p512_gsa.d4f_classical_bits, d512.classical_bits, fail512_log2
    );
    println!(
        "ML-KEM-768 : GSA beta={}, Sim beta={}, Dual beta={}, CoreSVP={:.1}, Quantum={:.1}, d4f={:.1}, DualBits={:.1}, log2(p_fail)={:.1}",
        p768_gsa.beta, p768_sim.beta, d768.beta, p768_gsa.classical_bits, p768_gsa.quantum_bits, p768_gsa.d4f_classical_bits, d768.classical_bits, fail768_log2
    );
    println!(
        "ML-KEM-1024: GSA beta={}, Sim beta={}, Dual beta={}, CoreSVP={:.1}, Quantum={:.1}, d4f={:.1}, DualBits={:.1}, log2(p_fail)={:.1}",
        p1024_gsa.beta, p1024_sim.beta, d1024.beta, p1024_gsa.classical_bits, p1024_gsa.quantum_bits, p1024_gsa.d4f_classical_bits, d1024.classical_bits, fail1024_log2
    );
}

#[test]
fn test_he_standard_bfv_calibration() {
    let q_27bit = (1u64 << 27) - 39;
    let sigma_ternary = (2.0f64 / 3.0).sqrt();
    let he_1024 = LweEstimateInput::new_gaussian(1024, 2048, q_27bit, sigma_ternary, 3.19, 1);
    let est_1024 = estimate_primal_usvp_gsa(&he_1024);
    let sim_1024 = estimate_primal_usvp_simulator(&he_1024, 15);
    assert!(
        (est_1024.he_standard_bits - 131.2).abs() <= 4.0,
        "HE N=1024 log2(q)=27 he_standard_bits={} (expected ~131.2)",
        est_1024.he_standard_bits
    );

    let q_54bit = (1u64 << 54) - 33;
    let he_2048 = LweEstimateInput::new_gaussian(2048, 4096, q_54bit, sigma_ternary, 3.19, 1);
    let est_2048 = estimate_primal_usvp_gsa(&he_2048);
    let sim_2048 = estimate_primal_usvp_simulator(&he_2048, 15);
    assert!(
        (est_2048.he_standard_bits - 131.0).abs() <= 4.0,
        "HE N=2048 log2(q)=54 he_standard_bits={} (expected ~131.0)",
        est_2048.he_standard_bits
    );

    println!("=== MEASURED HE STANDARD CALIBRATION ===");
    println!(
        "HE N=1024: GSA beta={}, Sim beta={}, CoreSVP={:.1}, HE-Std={:.1}, Quantum={:.1}",
        est_1024.beta,
        sim_1024.beta,
        est_1024.classical_bits,
        est_1024.he_standard_bits,
        est_1024.quantum_bits
    );
    println!(
        "HE N=2048: GSA beta={}, Sim beta={}, CoreSVP={:.1}, HE-Std={:.1}, Quantum={:.1}",
        est_2048.beta,
        sim_2048.beta,
        est_2048.classical_bits,
        est_2048.he_standard_bits,
        est_2048.quantum_bits
    );
}

#[test]
fn test_cn11_bkz_simulator_volume_conservation() {
    let m = 512;
    let n = 512;
    let q = 3329u64;
    let sigma = (1.5f64).sqrt();
    let beta = 400;
    let profile = simulate_bkz_profile(m, n, q, sigma, sigma, beta, 15);

    assert_eq!(profile.len(), m + n + 1);
    let expected_vol = (m as f64) * (q as f64).ln();
    let actual_vol: f64 = profile.iter().sum();
    assert!(
        (actual_vol - expected_vol).abs() < 1e-9,
        "Expected log-vol {expected_vol}, got {actual_vol}"
    );
}

#[test]
fn test_discrete_pmf_and_failure_probability() {
    let tern = DiscretePMF::uniform_ternary();
    let sum_tern: f64 = tern.probs.iter().sum();
    assert!((sum_tern - 1.0).abs() < 1e-15);

    let cbd2 = DiscretePMF::cbd(2);
    let sum_cbd2: f64 = cbd2.probs.iter().sum();
    assert!((sum_cbd2 - 1.0).abs() < 1e-15);
    assert!((cbd2.prob(0) - 6.0 / 16.0).abs() < 1e-15);
    assert!((cbd2.prob(2) - 1.0 / 16.0).abs() < 1e-15);

    let rep_toy = SecurityReport::evaluate_mod_pke(2, 4, 97, None, None, None);
    let rep_demo = SecurityReport::evaluate_mod_pke(2, 256, 3329, None, None, None);
    let rep_light = SecurityReport::evaluate_mod_pke(3, 256, 7681, None, None, None);
    let rep_std = SecurityReport::evaluate_mod_pke(4, 256, 12289, None, None, None);

    println!("=== MEASURED PRESET REPORTS ===");
    for (name, r) in [
        ("preset_toy_zero_failure  (2, 4, 97)", &rep_toy),
        ("main.rs demo             (2, 256, 3329)", &rep_demo),
        ("preset_light_zero_failure(3, 256, 7681)", &rep_light),
        ("preset_standard_128bit   (4, 256, 12289)", &rep_std),
    ] {
        println!(
            "{name}: GSA_beta={}, Sim_beta={}, Dual_beta={}, CoreSVP={:.1}, HE_Std={:.1}, Quantum={:.1}, MinClassical={:.1}, MinQuantum={:.1}, max_noise={}, thresh={}, p_fail={:.3e}, log2_fail={}",
            r.primal_gsa.beta,
            r.primal_sim.beta,
            r.dual.beta,
            r.primal_gsa.classical_bits,
            r.primal_gsa.he_standard_bits,
            r.primal_gsa.quantum_bits,
            r.min_classical_bits,
            r.min_quantum_bits,
            r.max_noise,
            r.noise_threshold,
            r.failure_prob,
            r.log2_failure_prob
        );
    }

    assert_eq!(rep_toy.max_noise, 17);
    assert_eq!(rep_toy.noise_threshold, 24);
    assert_eq!(rep_toy.failure_prob, 0.0);

    assert_eq!(rep_light.max_noise, 1537);
    assert_eq!(rep_light.noise_threshold, 1920);
    assert_eq!(rep_light.failure_prob, 0.0);
    assert!(rep_light.min_classical_bits >= 120.0);

    assert_eq!(rep_std.max_noise, 2049);
    assert_eq!(rep_std.noise_threshold, 3072);
    assert_eq!(rep_std.failure_prob, 0.0);
    assert!(rep_std.min_classical_bits >= 128.0);
    assert!(rep_std.min_quantum_bits >= 128.0);
}

#[test]
fn test_failure_probability_monte_carlo_cross_validation() {
    let k = 2usize;
    let n_poly = 4usize;
    let n_total = k * n_poly;
    let q = 13u64;
    let tern = DiscretePMF::uniform_ternary();

    let (max_noise, threshold, ub_fail, _log2_ub) =
        estimate_mod_pke_failure(n_total, n_poly, q, &tern, &tern, None, None);
    assert_eq!(max_noise, 17);
    assert_eq!(threshold, 3);

    let prod = DiscretePMF::product_of_independent(&tern, &tern);
    let pair = prod.convolve(&prod);
    let exact_noise_pmf = pair.convolve_power(n_total).convolve(&tern);
    let exact_single_coord_fail = exact_noise_pmf.tail_probability(threshold);

    let mut rng = StdRng::seed_from_u64(0x4D43_2026);
    let trials = 100_000usize;
    let mut single_coord_failures = 0usize;
    let mut any_coord_failures = 0usize;

    let sample_tern_poly = |rng: &mut StdRng| -> [i64; 4] {
        let mut out = [0i64; 4];
        for c in out.iter_mut() {
            *c = rng.gen_range(-1i64..=1);
        }
        out
    };
    let negacyclic_mul = |a: &[i64; 4], b: &[i64; 4]| -> [i64; 4] {
        let mut res = [0i64; 4];
        for i in 0..4 {
            for j in 0..4 {
                if i + j < 4 {
                    res[i + j] += a[i] * b[j];
                } else {
                    res[i + j - 4] -= a[i] * b[j];
                }
            }
        }
        res
    };

    for _ in 0..trials {
        let s0 = sample_tern_poly(&mut rng);
        let s1 = sample_tern_poly(&mut rng);
        let e0 = sample_tern_poly(&mut rng);
        let e1 = sample_tern_poly(&mut rng);
        let r0 = sample_tern_poly(&mut rng);
        let r1 = sample_tern_poly(&mut rng);
        let e1_0 = sample_tern_poly(&mut rng);
        let e1_1 = sample_tern_poly(&mut rng);
        let e2 = sample_tern_poly(&mut rng);

        let er0 = negacyclic_mul(&e0, &r0);
        let er1 = negacyclic_mul(&e1, &r1);
        let se0 = negacyclic_mul(&s0, &e1_0);
        let se1 = negacyclic_mul(&s1, &e1_1);

        let mut poly_failed = false;
        for idx in 0..n_poly {
            let err_coeff = er0[idx] + er1[idx] - se0[idx] - se1[idx] + e2[idx];
            if err_coeff.unsigned_abs() <= q / 2 {
                let mod_val = err_coeff.rem_euclid(q as i64) as u64;
                assert_eq!(centered_lift(mod_val, q), err_coeff);
            }
            if err_coeff.unsigned_abs() as usize >= threshold {
                if idx == 0 {
                    single_coord_failures += 1;
                }
                poly_failed = true;
            }
        }
        if poly_failed {
            any_coord_failures += 1;
        }
    }

    let mc_single_rate = single_coord_failures as f64 / (trials as f64);
    let mc_any_rate = any_coord_failures as f64 / (trials as f64);

    println!(
        "Monte Carlo vs DiscretePMF: exact_single={:.5}, mc_single={:.5}, mc_any={:.5}, union_bound={:.5}",
        exact_single_coord_fail, mc_single_rate, mc_any_rate, ub_fail
    );

    assert!(
        (mc_single_rate - exact_single_coord_fail).abs() < 0.005,
        "MC single rate {mc_single_rate} vs exact {exact_single_coord_fail}"
    );
    assert!(mc_any_rate <= ub_fail + 0.005);
}

#[test]
fn test_standard_presets_end_to_end() {
    let p_toy = ModPKEParams::preset_toy_zero_failure();
    assert!(p_toy.is_zero_failure_guaranteed());

    let p_light = ModPKEParams::preset_light_zero_failure();
    assert!(p_light.is_zero_failure_guaranteed());

    let p_std = ModPKEParams::preset_standard_128bit();
    assert!(p_std.is_zero_failure_guaranteed());

    let kem = ModKEMContext::preset_standard_128bit();
    let mut rng = StdRng::seed_from_u64(0x128B_175E);
    let (sk, pk) = kem.keygen_with_rng(&mut rng);
    let (ct, ss_enc) = kem.encaps_with_rng(&mut rng, &pk);
    let ss_dec = kem.decaps(&sk, &ct);
    assert_eq!(ss_enc, ss_dec);
}
