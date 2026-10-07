use alloc::vec::Vec;
use crate::lwe::sample::Matrix;

pub fn matrix_vec_mul(a: &Matrix, s: &[u64], q: u64) -> Vec<u64> {
    assert_eq!(a[0].len(), s.len());
    let mut result = Vec::with_capacity(a.len());
    for row in a {
        let mut sum = 0u64;
        for (a_ij, s_j) in row.iter().zip(s.iter()) {
            sum = (sum + a_ij * s_j) % q;
        }
        result.push(sum);
    }
    result
}

pub fn vec_add(v1: &[u64], v2: &[u64], q: u64) -> Vec<u64> {
    assert_eq!(v1.len(), v2.len());
    v1.iter().zip(v2.iter()).map(|(x, y)| (x + y) % q).collect()
}
