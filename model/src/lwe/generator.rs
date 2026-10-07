use crate::distributions::uniform::{
    sample_uniform_matrix, sample_uniform_secret, sample_uniform_vector,
};
use crate::distributions::ErrorDistribution;
use crate::lwe::math::{matrix_vec_mul, vec_add};
use crate::lwe::sample::LweSample;
use crate::params::LweParams;
use rand::Rng;

pub fn sample_lwe<R: Rng, E: ErrorDistribution>(
    rng: &mut R,
    params: &LweParams,
    err_dist: &E,
) -> LweSample {
    let a = sample_uniform_matrix(rng, params.m, params.n, params.q);
    let s = sample_uniform_secret(rng, params.n, params.q);
    let e = err_dist.sample(params);
    let as_vec = matrix_vec_mul(&a, &s, params.q);
    let b = vec_add(&as_vec, &e, params.q);
    LweSample::new(a, b)
}

pub fn sample_uniform<R: Rng>(rng: &mut R, params: &LweParams) -> LweSample {
    let a = sample_uniform_matrix(rng, params.m, params.n, params.q);
    let b = sample_uniform_vector(rng, params.m, params.q);
    LweSample::new(a, b)
}
