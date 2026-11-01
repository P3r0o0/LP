use crate::lwe::math::{
    add_mod, compress_coeff, ct_eq_slice, decompress_coeff, mul_mod, norm_inf, sub_mod,
    zeroize_slice,
};
use alloc::vec;
use alloc::vec::Vec;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial {
    pub coeffs: Vec<u64>,
}

impl Polynomial {
    pub fn new(coeffs: Vec<u64>) -> Self {
        Self { coeffs }
    }

    pub fn zero(n: usize) -> Self {
        Self { coeffs: vec![0; n] }
    }

    pub fn zeroize(&mut self) {
        zeroize_slice(&mut self.coeffs);
    }

    pub fn is_canonical(&self, q: u64) -> bool {
        self.coeffs.iter().all(|&c| c < q)
    }

    pub fn is_ternary(&self, q: u64) -> bool {
        self.coeffs.iter().all(|&c| c == 0 || c == 1 || c == q - 1)
    }

    pub fn ct_eq(&self, other: &Self) -> bool {
        ct_eq_slice(&self.coeffs, &other.coeffs)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.coeffs.len() * 8);
        for &c in &self.coeffs {
            out.extend_from_slice(&c.to_le_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        if bytes.len() != n.checked_mul(8)? {
            return None;
        }
        let mut coeffs = Vec::with_capacity(n);
        for chunk in bytes.chunks_exact(8) {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(chunk);
            let c = u64::from_le_bytes(arr);
            if c >= q {
                return None;
            }
            coeffs.push(c);
        }
        Some(Self { coeffs })
    }

    pub fn norm_inf(&self, q: u64) -> u64 {
        norm_inf(&self.coeffs, q)
    }

    pub fn add(&self, other: &Self, q: u64) -> Self {
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        let mut result = Vec::with_capacity(self.coeffs.len());
        for (&a, &b) in self.coeffs.iter().zip(other.coeffs.iter()) {
            result.push(add_mod(a, b, q));
        }
        Self::new(result)
    }

    pub fn sub(&self, other: &Self, q: u64) -> Self {
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        let mut result = Vec::with_capacity(self.coeffs.len());
        for (&a, &b) in self.coeffs.iter().zip(other.coeffs.iter()) {
            result.push(sub_mod(a, b, q));
        }
        Self::new(result)
    }

    pub fn mul_schoolbook(&self, other: &Self, q: u64) -> Self {
        let n = self.coeffs.len();
        assert_eq!(n, other.coeffs.len());
        let mut result = vec![0u64; n];

        for i in 0..n {
            for j in 0..n {
                let coeff = mul_mod(self.coeffs[i], other.coeffs[j], q);
                if i + j < n {
                    result[i + j] = add_mod(result[i + j], coeff, q);
                } else {
                    let idx = (i + j) - n;
                    result[idx] = sub_mod(result[idx], coeff, q);
                }
            }
        }
        Self::new(result)
    }

    pub fn mul_ntt(&self, other: &Self, psi: u64, q: u64) -> Self {
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        let a_ntt = crate::lwe::ntt::ntt(self, psi, q);
        let b_ntt = crate::lwe::ntt::ntt(other, psi, q);
        let prod_ntt = crate::lwe::ntt::ntt_mul(&a_ntt, &b_ntt, q);
        crate::lwe::ntt::inv_ntt(&prod_ntt, psi, q)
    }

    pub fn mul_schoolbook_unreduced(&self, other: &Self) -> Vec<i128> {
        let n = self.coeffs.len();
        assert_eq!(n, other.coeffs.len());
        let mut result = vec![0i128; n];

        for i in 0..n {
            for j in 0..n {
                let coeff = (self.coeffs[i] as i128) * (other.coeffs[j] as i128);
                if i + j < n {
                    result[i + j] += coeff;
                } else {
                    let idx = (i + j) - n;
                    result[idx] -= coeff;
                }
            }
        }
        result
    }

    pub fn apply_galois(&self, g: usize, q: u64) -> Self {
        assert!(
            g % 2 == 1,
            "Galois exponent g must be odd so that (X^g)^N == -1 mod (X^N + 1)"
        );
        let n = self.coeffs.len();
        let mut result = vec![0u64; n];
        if n == 0 {
            return Self::new(result);
        }
        for (i, &c) in self.coeffs.iter().enumerate() {
            let c_mod = c % q;
            let prod = i * g;
            let k = prod / n;
            let r = prod % n;
            if k % 2 == 0 {
                result[r] = add_mod(result[r], c_mod, q);
            } else {
                result[r] = sub_mod(result[r], c_mod, q);
            }
        }
        Self::new(result)
    }

    pub fn compress(&self, q: u64, d: u32) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|&c| compress_coeff(c, q, d))
            .collect();
        Self::new(coeffs)
    }

    pub fn decompress(&self, q: u64, d: u32) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|&y| decompress_coeff(y, q, d))
            .collect();
        Self::new(coeffs)
    }
}
