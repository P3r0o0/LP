use lwe_rust::distributions::discrete_gaussian::DiscreteGaussian;
use lwe_rust::distributions::ErrorDistribution;
use lwe_rust::lwe::math::{matrix_vec_mul, norm_inf, vec_add};
use lwe_rust::lwe::sample::LweSample;
use lwe_rust::params::LweParams;
use rand::thread_rng;

#[test]
fn test_homomorphic_addition_completeness() {
    let mut rng = thread_rng();
    let params = LweParams::new(256, 100, 3329);
    let err_dist = DiscreteGaussian { eta: 3 };

    let s = lwe_rust::distributions::uniform::sample_uniform_secret(&mut rng, params.n, params.q);

    let e1 = err_dist.sample(&params);
    let e2 = err_dist.sample(&params);

    let a1 = lwe_rust::distributions::uniform::sample_uniform_matrix(
        &mut rng, params.m, params.n, params.q,
    );
    let a2 = lwe_rust::distributions::uniform::sample_uniform_matrix(
        &mut rng, params.m, params.n, params.q,
    );

    let as1 = matrix_vec_mul(&a1, &s, params.q);
    let b1 = vec_add(&as1, &e1, params.q);
    let sample1 = LweSample::new(a1.clone(), b1);

    let as2 = matrix_vec_mul(&a2, &s, params.q);
    let b2 = vec_add(&as2, &e2, params.q);
    let sample2 = LweSample::new(a2.clone(), b2);

    let sample_sum = sample1.add(&sample2, params.q);

    let a_sum = lwe_rust::lwe::math::matrix_add(&a1, &a2, params.q);
    let e_sum = vec_add(&e1, &e2, params.q);
    let expected_as_sum = matrix_vec_mul(&a_sum, &s, params.q);
    let expected_b_sum = vec_add(&expected_as_sum, &e_sum, params.q);

    assert_eq!(sample_sum.a, a_sum);
    assert_eq!(sample_sum.b, expected_b_sum);

    let norm_e1 = norm_inf(&e1, params.q);
    let norm_e2 = norm_inf(&e2, params.q);
    let norm_e_sum = norm_inf(&e_sum, params.q);

    assert!(
        norm_e_sum <= norm_e1 + norm_e2,
        "Triangle inequality failed for norm"
    );

    println!(
        "Norm e1: {}, Norm e2: {}, Norm e1+e2: {}",
        norm_e1, norm_e2, norm_e_sum
    );
}

#[test]
fn test_standard_regev_lwe_encryption_and_serialization() {
    use lwe_rust::lwe::generator::sample_lwe_with_secret;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    let mut rng = StdRng::seed_from_u64(0x1234_5678_9ABC_DEF0);
    let params = LweParams::new(64, 32, 3329);
    let err_dist = DiscreteGaussian { eta: 2 };
    let t = 8u64;

    let s = lwe_rust::distributions::uniform::sample_uniform_secret(&mut rng, params.n, params.q);
    let base1 = sample_lwe_with_secret(&mut rng, &params, &s, &err_dist);
    let base2 = sample_lwe_with_secret(&mut rng, &params, &s, &err_dist);

    let m1: Vec<u64> = (0..params.m).map(|i| (i as u64) % t).collect();
    let m2: Vec<u64> = (0..params.m).map(|i| ((i * 3 + 1) as u64) % t).collect();

    let ct1 = base1.encrypt_messages(&m1, t, params.q);
    let ct2 = base2.encrypt_messages(&m2, t, params.q);
    assert!(ct1.is_well_formed(params.m, params.n, params.q));

    assert_eq!(ct1.decrypt_messages(&s, t, params.q), m1);
    assert_eq!(ct2.decrypt_messages(&s, t, params.q), m2);

    let m1_small = vec![2u64; params.m];
    let m2_small = vec![3u64; params.m];
    let ct1_s = base1.encrypt_messages(&m1_small, t, params.q);
    let ct2_s = base2.encrypt_messages(&m2_small, t, params.q);
    let ct_sum = ct1_s.add(&ct2_s, params.q);
    assert_eq!(
        ct_sum.decrypt_messages(&s, t, params.q),
        vec![5u64; params.m]
    );

    let ct_diff = ct2_s.sub(&ct1_s, params.q);
    assert_eq!(
        ct_diff.decrypt_messages(&s, t, params.q),
        vec![1u64; params.m]
    );

    let bytes = ct1.to_bytes();
    assert_eq!(bytes.len(), (params.m * params.n + params.m) * 8);
    let restored =
        LweSample::from_bytes(&bytes, params.m, params.n, params.q).expect("valid LweSample");
    assert_eq!(ct1, restored);
    assert!(
        LweSample::from_bytes(&bytes[..bytes.len() - 1], params.m, params.n, params.q).is_none()
    );

    let mut bad_bytes = bytes.clone();
    bad_bytes[0..8].copy_from_slice(&params.q.to_le_bytes());
    assert!(LweSample::from_bytes(&bad_bytes, params.m, params.n, params.q).is_none());

    let poly_cbd = err_dist.sample_poly_with_rng(&mut rng, 64, params.q);
    assert_eq!(poly_cbd.coeffs.len(), 64);
    assert!(poly_cbd.norm_inf(params.q) <= err_dist.eta as u64);
}
