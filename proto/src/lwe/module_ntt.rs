use crate::lwe::math::{add_mod, mul_mod};
use crate::lwe::ntt::{inv_ntt, ntt, NTTTable};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;

pub fn vector_ntt(v: &[Polynomial], psi: u64, q: u64) -> Vec<Vec<u64>> {
    v.iter().map(|p| ntt(p, psi, q)).collect()
}

pub fn matrix_ntt(m: &[Vec<Polynomial>], psi: u64, q: u64) -> Vec<Vec<Vec<u64>>> {
    m.iter().map(|row| vector_ntt(row, psi, q)).collect()
}

pub fn vector_intt(v: &[Vec<u64>], psi: u64, q: u64) -> Vec<Polynomial> {
    v.iter().map(|p| inv_ntt(p, psi, q)).collect()
}

pub fn matrix_intt(m: &[Vec<Vec<u64>>], psi: u64, q: u64) -> Vec<Vec<Polynomial>> {
    m.iter().map(|row| vector_intt(row, psi, q)).collect()
}

pub fn vector_ntt_table(v: &[Polynomial], table: &NTTTable) -> Vec<Vec<u64>> {
    v.iter().map(|p| table.forward(p)).collect()
}

pub fn matrix_ntt_table(m: &[Vec<Polynomial>], table: &NTTTable) -> Vec<Vec<Vec<u64>>> {
    m.iter().map(|row| vector_ntt_table(row, table)).collect()
}

pub fn vector_intt_table(v: &[Vec<u64>], table: &NTTTable) -> Vec<Polynomial> {
    v.iter().map(|p| table.inverse(p)).collect()
}

pub fn matrix_intt_table(m: &[Vec<Vec<u64>>], table: &NTTTable) -> Vec<Vec<Polynomial>> {
    m.iter().map(|row| vector_intt_table(row, table)).collect()
}

pub fn ntt_evaluate_table(
    a: &[Vec<Vec<u64>>],
    s: &[Vec<u64>],
    e: &[Vec<u64>],
    table: &NTTTable,
) -> Vec<Vec<u64>> {
    let k = a.len();
    assert_eq!(k, e.len());
    if k == 0 {
        return Vec::new();
    }
    let l = s.len();
    let n = table.n;
    let q = table.q;
    let mut result = Vec::with_capacity(k);

    for i in 0..k {
        assert_eq!(a[i].len(), l);
        assert_eq!(e[i].len(), n);
        let mut sum = vec![0u64; n];
        for j in 0..l {
            assert_eq!(a[i][j].len(), n);
            assert_eq!(s[j].len(), n);
            for x in 0..n {
                let prod = table.barrett.mul_mod(a[i][j][x], s[j][x]);
                sum[x] = add_mod(sum[x], prod, q);
            }
        }
        for x in 0..n {
            sum[x] = add_mod(sum[x], e[i][x], q);
        }
        result.push(sum);
    }
    result
}

pub fn ntt_evaluate(a: &[Vec<Vec<u64>>], s: &[Vec<u64>], e: &[Vec<u64>], q: u64) -> Vec<Vec<u64>> {
    let k = a.len();
    assert_eq!(k, e.len());
    if k == 0 {
        return Vec::new();
    }
    let l = s.len();
    let n = e[0].len();

    let mut result = Vec::with_capacity(k);

    for i in 0..k {
        assert_eq!(a[i].len(), l);
        assert_eq!(e[i].len(), n);
        let mut sum = vec![0; n];
        for j in 0..l {
            assert_eq!(a[i][j].len(), n);
            assert_eq!(s[j].len(), n);
            for x in 0..n {
                let prod = mul_mod(a[i][j][x], s[j][x], q);
                sum[x] = add_mod(sum[x], prod, q);
            }
        }
        for x in 0..n {
            sum[x] = add_mod(sum[x], e[i][x], q);
        }
        result.push(sum);
    }
    result
}
