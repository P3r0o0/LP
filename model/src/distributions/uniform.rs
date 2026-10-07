use alloc::vec::Vec;
use crate::lwe::sample::Matrix;
use rand::Rng;

pub fn sample_uniform_matrix<R: Rng>(rng: &mut R, m: usize, n: usize, q: u64) -> Matrix {
    let mut matrix = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range(0..q));
        }
        matrix.push(row);
    }
    matrix
}

pub fn sample_uniform_secret<R: Rng>(rng: &mut R, n: usize, q: u64) -> Vec<u64> {
    let mut secret = Vec::with_capacity(n);
    for _ in 0..n {
        secret.push(rng.gen_range(0..q));
    }
    secret
}

pub fn sample_uniform_vector<R: Rng>(rng: &mut R, m: usize, q: u64) -> Vec<u64> {
    let mut vector = Vec::with_capacity(m);
    for _ in 0..m {
        vector.push(rng.gen_range(0..q));
    }
    vector
}
