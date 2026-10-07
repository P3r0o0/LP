use alloc::vec::Vec;
use crate::distributions::ErrorDistribution;
use crate::lwe::generator::{sample_lwe, sample_uniform};
use crate::lwe::sample::LweSample;
use crate::params::LweParams;
use rand::Rng;

pub type Distinguisher = fn(&LweSample) -> bool;

pub fn prob_true<F>(samples: &[LweSample], d: F) -> f64
where
    F: Fn(&LweSample) -> bool,
{
    let count = samples.iter().filter(|s| d(*s)).count();
    count as f64 / samples.len() as f64
}

pub fn lwe_advantage<R: Rng, E: ErrorDistribution, F>(
    rng: &mut R,
    params: &LweParams,
    err_dist: &E,
    d: F,
    trials: usize,
) -> f64
where
    F: Fn(&LweSample) -> bool,
{
    let mut lwe_samples = Vec::with_capacity(trials);
    let mut uniform_samples = Vec::with_capacity(trials);

    for _ in 0..trials {
        lwe_samples.push(sample_lwe(rng, params, err_dist));
        uniform_samples.push(sample_uniform(rng, params));
    }

    let p_lwe = prob_true(&lwe_samples, &d);
    let p_uniform = prob_true(&uniform_samples, &d);

    (p_lwe - p_uniform).abs()
}
