use lwe_rust::gauge::abelian_proj::SU2Link;
use lwe_rust::gauge::plaquette::extract_lwe_noise_from_plaquette;
use rand::{thread_rng, Rng};
use rand_distr::{Distribution, Normal};

fn sample_su2_beta(beta: f64) -> SU2Link {
    let mut rng = thread_rng();

    let std_dev = (1.0 / beta).sqrt();
    let normal = Normal::new(0.0, std_dev).unwrap();

    let a1 = normal.sample(&mut rng);
    let a2 = normal.sample(&mut rng);
    let a3 = normal.sample(&mut rng);

    let a_sq = a1 * a1 + a2 * a2 + a3 * a3;
    let a0 = if a_sq < 1.0 {
        (1.0f64 - a_sq).sqrt()
    } else {
        0.0
    };

    SU2Link::new(a0, a1, a2, a3)
}

#[allow(unused_variables)]
fn compute_optimal_q_for_beta(beta: f64) -> i64 {
    3329
}

fn compute_tv_distance(samples: &[i64], expected_variance: f64) -> f64 {
    let mut counts = std::collections::HashMap::new();
    let n = samples.len() as f64;
    for &s in samples {
        *counts.entry(s).or_insert(0) += 1;
    }

    let mut tv = 0.0;

    for x in -20..=20 {
        let emp_prob = counts.get(&x).copied().unwrap_or(0) as f64 / n;

        let std_dev = expected_variance.sqrt();
        let expected_prob = (1.0 / (std_dev * (2.0 * std::f64::consts::PI).sqrt()))
            * (-(x as f64 * x as f64) / (2.0 * expected_variance)).exp();

        tv += 0.5 * (emp_prob - expected_prob).abs();
    }
    tv
}

#[test]
fn test_gauge_noise_is_approximately_gaussian() {
    let beta_values = [10.0, 50.0, 100.0, 500.0];
    let num_samples = 10000;

    for &beta in &beta_values {
        let q = compute_optimal_q_for_beta(beta);

        let mut noise_samples = Vec::with_capacity(num_samples);
        for _ in 0..num_samples {
            let u1 = sample_su2_beta(beta);
            let u2 = sample_su2_beta(beta);
            let u3 = sample_su2_beta(beta);
            let u4 = sample_su2_beta(beta);

            let noise = extract_lwe_noise_from_plaquette(&u1, &u2, &u3, &u4, q);
            noise_samples.push(noise);
        }

        let mean = noise_samples.iter().map(|&x| x as f64).sum::<f64>() / num_samples as f64;
        let variance = noise_samples
            .iter()
            .map(|&x| (x as f64 - mean).powi(2))
            .sum::<f64>()
            / num_samples as f64;

        let tv_dist = compute_tv_distance(&noise_samples, variance);

        println!(
            "β = {:>5.1}, q = {}, Var = {:>7.3}, TV distance = {:.4}",
            beta, q, variance, tv_dist
        );

        assert!(tv_dist < 0.2, "TV distance too large!");
    }
}
