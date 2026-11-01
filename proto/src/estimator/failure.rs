use std::vec;
use std::vec::Vec;

use crate::lwe::math::{centered_lift, compress_coeff, decompress_coeff};

#[derive(Debug, Clone)]
pub struct DiscretePMF {
    pub max_abs: usize,
    pub probs: Vec<f64>,
}

impl DiscretePMF {
    pub fn dirac_zero() -> Self {
        Self {
            max_abs: 0,
            probs: vec![1.0],
        }
    }

    #[inline]
    pub fn prob(&self, x: i64) -> f64 {
        let m = self.max_abs as i64;
        if x < -m || x > m {
            0.0
        } else {
            self.probs[(x + m) as usize]
        }
    }

    pub fn uniform_ternary() -> Self {
        let p = 1.0 / 3.0;
        Self {
            max_abs: 1,
            probs: vec![p, p, p],
        }
    }

    pub fn cbd(eta: usize) -> Self {
        if eta == 0 {
            return Self::dirac_zero();
        }
        let two_eta = 2 * eta;
        let scale = 2.0f64.powi(-(two_eta as i32));
        let mut probs = Vec::with_capacity(two_eta + 1);
        for k in 0..=two_eta {
            let mut binom = 1u128;
            for j in 0..k {
                binom = binom * ((two_eta - j) as u128) / ((j + 1) as u128);
            }
            probs.push((binom as f64) * scale);
        }
        Self {
            max_abs: eta,
            probs,
        }
    }

    pub fn compression_error(q: u64, d_bits: u32) -> Self {
        if d_bits == 0 || (1u64 << d_bits) >= q {
            return Self::dirac_zero();
        }
        if q <= 131_072 {
            let max_bound = ((q >> (d_bits + 1)) + 2) as usize;
            let mut counts = vec![0u64; 2 * max_bound + 1];
            for u in 0..q {
                let comp = compress_coeff(u, q, d_bits);
                let decomp = decompress_coeff(comp, q, d_bits);
                let diff = if decomp >= u {
                    decomp - u
                } else {
                    q - (u - decomp)
                };
                let err = centered_lift(diff, q);
                let abs_e = err.unsigned_abs() as usize;
                assert!(abs_e <= max_bound);
                counts[(max_bound as i64 + err) as usize] += 1;
                counts[(max_bound as i64 - err) as usize] += 1;
            }
            let denom = (2 * q) as f64;
            let probs = counts.into_iter().map(|c| (c as f64) / denom).collect();
            Self {
                max_abs: max_bound,
                probs,
            }
        } else {
            let b = (q >> (d_bits + 1)) as usize;
            let p = 1.0 / ((2 * b + 1) as f64);
            Self {
                max_abs: b,
                probs: vec![p; 2 * b + 1],
            }
        }
    }

    pub fn product_of_independent(a: &Self, b: &Self) -> Self {
        let max_prod = a.max_abs * b.max_abs;
        let mut probs = vec![0.0; 2 * max_prod + 1];
        let ma = a.max_abs as i64;
        let mb = b.max_abs as i64;
        let mp = max_prod as i64;

        for xa in -ma..=ma {
            let pa = a.prob(xa);
            if pa == 0.0 {
                continue;
            }
            for xb in -mb..=mb {
                let pb = b.prob(xb);
                if pb == 0.0 {
                    continue;
                }
                let prod = xa * xb;
                probs[(prod + mp) as usize] += pa * pb;
            }
        }

        Self {
            max_abs: max_prod,
            probs,
        }
    }

    pub fn convolve(&self, other: &Self) -> Self {
        if self.max_abs == 0 {
            return other.clone();
        }
        if other.max_abs == 0 {
            return self.clone();
        }
        let new_max = self.max_abs + other.max_abs;
        let mut out = vec![0.0; 2 * new_max + 1];
        for (i, &pa) in self.probs.iter().enumerate() {
            if pa == 0.0 {
                continue;
            }
            for (j, &pb) in other.probs.iter().enumerate() {
                out[i + j] += pa * pb;
            }
        }
        Self {
            max_abs: new_max,
            probs: out,
        }
    }

    pub fn convolve_power(&self, mut count: usize) -> Self {
        if count == 0 || self.max_abs == 0 {
            return Self::dirac_zero();
        }
        let mut result = Self::dirac_zero();
        let mut base = self.clone();
        while count > 0 {
            if (count & 1) == 1 {
                result = result.convolve(&base);
            }
            count >>= 1;
            if count > 0 {
                base = base.convolve(&base);
            }
        }
        result
    }

    pub fn tail_probability(&self, threshold: usize) -> f64 {
        if threshold == 0 {
            return 1.0;
        }
        if threshold > self.max_abs {
            return 0.0;
        }
        let m = self.max_abs;
        let mut sum = 0.0;
        for abs_x in (threshold..=m).rev() {
            sum += self.probs[m - abs_x] + self.probs[m + abs_x];
        }
        sum.min(1.0)
    }

    pub fn union_bound_failure(&self, threshold: usize, num_coords: usize) -> (f64, f64) {
        let single = self.tail_probability(threshold);
        if single <= 0.0 {
            return (0.0, f64::NEG_INFINITY);
        }
        let total = ((num_coords.max(1) as f64) * single).min(1.0);
        let log2_total = (num_coords.max(1) as f64).log2() + single.log2();
        (total, log2_total.min(0.0))
    }
}

pub fn estimate_mod_pke_failure_asymmetric(
    n_total: usize,
    n_poly: usize,
    q: u64,
    sk_r_pmf: &DiscretePMF,
    enc_err_pmf: &DiscretePMF,
    d_u: Option<u32>,
    d_v: Option<u32>,
) -> (usize, usize, f64, f64) {
    let cu_pmf = match d_u {
        Some(du) => DiscretePMF::compression_error(q, du),
        None => DiscretePMF::dirac_zero(),
    };
    let cv_pmf = match d_v {
        Some(dv) => DiscretePMF::compression_error(q, dv),
        None => DiscretePMF::dirac_zero(),
    };

    let er_prod = DiscretePMF::product_of_independent(sk_r_pmf, sk_r_pmf);
    let e1_plus_cu = enc_err_pmf.convolve(&cu_pmf);
    let s_e1cu_prod = DiscretePMF::product_of_independent(sk_r_pmf, &e1_plus_cu);

    let pair_pmf = er_prod.convolve(&s_e1cu_prod);
    let inner_products_pmf = pair_pmf.convolve_power(n_total);

    let total_noise_pmf = inner_products_pmf.convolve(enc_err_pmf).convolve(&cv_pmf);

    let delta = q / 2;
    let threshold = delta.div_ceil(2) as usize;
    let max_noise = total_noise_pmf.max_abs;
    let (p_fail, log2_p_fail) = total_noise_pmf.union_bound_failure(threshold, n_poly);

    (max_noise, threshold, p_fail, log2_p_fail)
}

pub fn estimate_mod_pke_failure(
    n_total: usize,
    n_poly: usize,
    q: u64,
    secret_pmf: &DiscretePMF,
    error_pmf: &DiscretePMF,
    d_u: Option<u32>,
    d_v: Option<u32>,
) -> (usize, usize, f64, f64) {
    let cu_pmf = match d_u {
        Some(du) => DiscretePMF::compression_error(q, du),
        None => DiscretePMF::dirac_zero(),
    };
    let cv_pmf = match d_v {
        Some(dv) => DiscretePMF::compression_error(q, dv),
        None => DiscretePMF::dirac_zero(),
    };

    let er_prod = DiscretePMF::product_of_independent(error_pmf, secret_pmf);
    let e1_plus_cu = error_pmf.convolve(&cu_pmf);
    let s_e1cu_prod = DiscretePMF::product_of_independent(secret_pmf, &e1_plus_cu);

    let pair_pmf = er_prod.convolve(&s_e1cu_prod);
    let inner_products_pmf = pair_pmf.convolve_power(n_total);
    let total_noise_pmf = inner_products_pmf.convolve(error_pmf).convolve(&cv_pmf);

    let delta = q / 2;
    let threshold = delta.div_ceil(2) as usize;
    let max_noise = total_noise_pmf.max_abs;
    let (p_fail, log2_p_fail) = total_noise_pmf.union_bound_failure(threshold, n_poly);

    (max_noise, threshold, p_fail, log2_p_fail)
}
