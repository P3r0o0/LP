use crate::lwe::math::{add_mod, mul_mod, sub_mod, BarrettModulus};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;

pub fn pow_mod(mut a: u64, mut exp: u64, q: u64) -> u64 {
    let mut res = 1 % q;
    a %= q;
    while exp > 0 {
        if exp & 1 == 1 {
            res = mul_mod(res, a, q);
        }
        a = mul_mod(a, a, q);
        exp >>= 1;
    }
    res
}

pub fn inv_mod(a: u64, q: u64) -> u64 {
    assert!(q >= 2, "Modulus q must be >= 2");
    pow_mod(a, q - 2, q)
}

fn radix2_fft_in_place(a: &mut [u64], omega: u64, q: u64) {
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }

    let mut j = 0usize;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            a.swap(i, j);
        }
    }

    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        let w_len = pow_mod(omega, step as u64, q);

        for start in (0..n).step_by(len) {
            let mut w = 1u64;
            for k in 0..half {
                let u = a[start + k];
                let v = mul_mod(a[start + k + half], w, q);
                a[start + k] = add_mod(u, v, q);
                a[start + k + half] = sub_mod(u, v, q);
                w = mul_mod(w, w_len, q);
            }
        }
        len <<= 1;
    }
}

pub fn ntt_naive(poly: &Polynomial, psi: u64, q: u64) -> Vec<u64> {
    let n = poly.coeffs.len();
    let mut result = Vec::with_capacity(n);
    let psi_sq = mul_mod(psi, psi, q);
    let mut root = psi % q;

    for _ in 0..n {
        let mut eval = 0u64;
        let mut current_power = 1u64;

        for j in 0..n {
            eval = add_mod(eval, mul_mod(poly.coeffs[j], current_power, q), q);
            current_power = mul_mod(current_power, root, q);
        }
        result.push(eval);
        root = mul_mod(root, psi_sq, q);
    }
    result
}

pub fn inv_ntt_naive(evals: &[u64], psi: u64, q: u64) -> Polynomial {
    let n = evals.len();
    if n == 0 {
        return Polynomial::new(Vec::new());
    }
    let mut coeffs = vec![0u64; n];
    let n_inv = inv_mod(n as u64, q);
    let psi_inv = inv_mod(psi, q);

    for i in 0..n {
        let mut sum = 0u64;
        let base_step = pow_mod(psi_inv, (2 * i) as u64, q);
        let mut root_inv = pow_mod(psi_inv, i as u64, q);
        for j in 0..n {
            sum = add_mod(sum, mul_mod(evals[j], root_inv, q), q);
            root_inv = mul_mod(root_inv, base_step, q);
        }
        coeffs[i] = mul_mod(sum, n_inv, q);
    }

    Polynomial::new(coeffs)
}

pub fn ntt(poly: &Polynomial, psi: u64, q: u64) -> Vec<u64> {
    let n = poly.coeffs.len();
    if n == 0 {
        return Vec::new();
    }
    if !n.is_power_of_two() {
        return ntt_naive(poly, psi, q);
    }

    let mut a = Vec::with_capacity(n);
    let mut psi_pow = 1u64;
    for &c in &poly.coeffs {
        a.push(mul_mod(c, psi_pow, q));
        psi_pow = mul_mod(psi_pow, psi, q);
    }

    let omega = mul_mod(psi, psi, q);
    radix2_fft_in_place(&mut a, omega, q);
    a
}

pub fn inv_ntt(evals: &[u64], psi: u64, q: u64) -> Polynomial {
    let n = evals.len();
    if n == 0 {
        return Polynomial::new(Vec::new());
    }
    if !n.is_power_of_two() {
        return inv_ntt_naive(evals, psi, q);
    }

    let n_inv = inv_mod(n as u64, q);
    let psi_inv = inv_mod(psi, q);
    let omega_inv = mul_mod(psi_inv, psi_inv, q);

    let mut a = evals.to_vec();
    radix2_fft_in_place(&mut a, omega_inv, q);

    let mut scale = n_inv;
    for coeff in a.iter_mut() {
        *coeff = mul_mod(*coeff, scale, q);
        scale = mul_mod(scale, psi_inv, q);
    }

    Polynomial::new(a)
}

pub fn ntt_mul(a: &[u64], b: &[u64], q: u64) -> Vec<u64> {
    assert_eq!(a.len(), b.len());
    a.iter()
        .zip(b.iter())
        .map(|(&x, &y)| mul_mod(x, y, q))
        .collect()
}

#[derive(Debug, Clone)]
pub struct NTTTable {
    pub n: usize,
    pub q: u64,
    pub psi: u64,
    pub barrett: BarrettModulus,
    pub bitrev: Vec<usize>,
    pub psi_powers: Vec<u64>,
    pub inv_psi_powers_scaled: Vec<u64>,
    pub forward_stage_twiddles: Vec<Vec<u64>>,
    pub inverse_stage_twiddles: Vec<Vec<u64>>,
}

impl NTTTable {
    pub fn new(n: usize, psi: u64, q: u64) -> Self {
        assert!(
            n > 0 && n.is_power_of_two(),
            "NTTTable degree n must be a power of 2"
        );
        assert_eq!(
            pow_mod(psi, n as u64, q),
            q - 1,
            "psi must satisfy psi^N == -1 mod q"
        );
        let barrett = BarrettModulus::new(q);

        let mut bitrev = (0..n).collect::<Vec<usize>>();
        let mut j = 0usize;
        for i in 1..n {
            let mut bit = n >> 1;
            while j & bit != 0 {
                j ^= bit;
                bit >>= 1;
            }
            j ^= bit;
            if i < j {
                bitrev.swap(i, j);
            }
        }

        let mut psi_powers = Vec::with_capacity(n);
        let mut cur = 1u64;
        for _ in 0..n {
            psi_powers.push(cur);
            cur = barrett.mul_mod(cur, psi);
        }

        let n_inv = inv_mod(n as u64, q);
        let psi_inv = inv_mod(psi, q);
        let mut inv_psi_powers_scaled = Vec::with_capacity(n);
        let mut cur_inv = n_inv;
        for _ in 0..n {
            inv_psi_powers_scaled.push(cur_inv);
            cur_inv = barrett.mul_mod(cur_inv, psi_inv);
        }

        let omega = barrett.mul_mod(psi, psi);
        let omega_inv = barrett.mul_mod(psi_inv, psi_inv);
        let mut forward_stage_twiddles = Vec::new();
        let mut inverse_stage_twiddles = Vec::new();

        let mut len = 2;
        while len <= n {
            let half = len / 2;
            let step = n / len;
            let w_len_fwd = pow_mod(omega, step as u64, q);
            let w_len_inv = pow_mod(omega_inv, step as u64, q);

            let mut fwd_twiddles = Vec::with_capacity(half);
            let mut inv_twiddles = Vec::with_capacity(half);
            let mut wf = 1u64;
            let mut wi = 1u64;
            for _ in 0..half {
                fwd_twiddles.push(wf);
                inv_twiddles.push(wi);
                wf = barrett.mul_mod(wf, w_len_fwd);
                wi = barrett.mul_mod(wi, w_len_inv);
            }
            forward_stage_twiddles.push(fwd_twiddles);
            inverse_stage_twiddles.push(inv_twiddles);
            len <<= 1;
        }

        Self {
            n,
            q,
            psi,
            barrett,
            bitrev,
            psi_powers,
            inv_psi_powers_scaled,
            forward_stage_twiddles,
            inverse_stage_twiddles,
        }
    }

    pub fn forward(&self, poly: &Polynomial) -> Vec<u64> {
        assert_eq!(poly.coeffs.len(), self.n);
        let n = self.n;
        let q = self.q;

        let mut a = vec![0u64; n];
        for i in 0..n {
            let twisted = self.barrett.mul_mod(poly.coeffs[i], self.psi_powers[i]);
            a[self.bitrev[i]] = twisted;
        }

        for twiddles in &self.forward_stage_twiddles {
            let half = twiddles.len();
            let len = half * 2;
            for start in (0..n).step_by(len) {
                for k in 0..half {
                    let u = a[start + k];
                    let v = self.barrett.mul_mod(a[start + k + half], twiddles[k]);
                    a[start + k] = add_mod(u, v, q);
                    a[start + k + half] = sub_mod(u, v, q);
                }
            }
        }
        a
    }

    pub fn inverse(&self, evals: &[u64]) -> Polynomial {
        assert_eq!(evals.len(), self.n);
        let n = self.n;
        let q = self.q;

        let mut a = vec![0u64; n];
        for i in 0..n {
            a[self.bitrev[i]] = evals[i];
        }

        for twiddles in &self.inverse_stage_twiddles {
            let half = twiddles.len();
            let len = half * 2;
            for start in (0..n).step_by(len) {
                for k in 0..half {
                    let u = a[start + k];
                    let v = self.barrett.mul_mod(a[start + k + half], twiddles[k]);
                    a[start + k] = add_mod(u, v, q);
                    a[start + k + half] = sub_mod(u, v, q);
                }
            }
        }

        for j in 0..n {
            a[j] = self.barrett.mul_mod(a[j], self.inv_psi_powers_scaled[j]);
        }

        Polynomial::new(a)
    }

    pub fn mul_ntt(&self, a: &Polynomial, b: &Polynomial) -> Polynomial {
        let a_ntt = self.forward(a);
        let b_ntt = self.forward(b);
        let prod_ntt: Vec<u64> = a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(&x, &y)| self.barrett.mul_mod(x, y))
            .collect();
        self.inverse(&prod_ntt)
    }
}
