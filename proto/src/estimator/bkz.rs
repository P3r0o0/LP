use std::f64::consts::{E, PI};
use std::vec;
use std::vec::Vec;

pub fn ln_gamma(x: f64) -> f64 {
    const COEFFS: [f64; 9] = [
        0.999_999_999_999_809_9,
        676.520_368_121_885_1,
        -1_259.139_216_722_402_8,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    if x < 0.5 {
        return PI.ln() - (PI * x).sin().ln() - ln_gamma(1.0 - x);
    }
    let z = x - 1.0;
    let mut sum = COEFFS[0];
    for (i, &c) in COEFFS.iter().enumerate().skip(1) {
        sum += c / (z + i as f64);
    }
    let t = z + 7.5;
    0.5 * (2.0 * PI).ln() + (z + 0.5) * t.ln() - t + sum.ln()
}

pub fn ln_gh_factor(k: usize) -> f64 {
    assert!(k >= 1);
    let kf = k as f64;
    ln_gamma(0.5 * kf + 1.0) / kf - 0.5 * PI.ln()
}

pub fn root_hermite_factor(beta: usize) -> f64 {
    ln_root_hermite_factor(beta).exp()
}

pub fn ln_root_hermite_factor(beta: usize) -> f64 {
    if beta <= 2 {
        return 1.0219f64.ln();
    }
    if beta < 50 {
        let b50 = {
            let b = 50.0;
            (((PI * b).ln() / b + (b / (2.0 * PI * E)).ln()) / (2.0 * (b - 1.0))).exp()
        };
        if beta <= 20 {
            let t = (beta - 2) as f64 / 18.0;
            let delta = 1.0219 * (1.0 - t) + 1.0128 * t;
            return delta.ln();
        } else {
            let t = (beta - 20) as f64 / 30.0;
            let delta = 1.0128 * (1.0 - t) + b50 * t;
            return delta.ln();
        }
    }
    let b = beta as f64;
    ((PI * b).ln() / b + (b / (2.0 * PI * E)).ln()) / (2.0 * (b - 1.0))
}

#[inline]
pub fn core_svp_classical_bits(beta: usize) -> f64 {
    0.292 * (beta as f64)
}

#[inline]
pub fn core_svp_quantum_bits(beta: usize) -> f64 {
    0.265 * (beta as f64)
}

pub fn d4f_dimension_saving(beta: usize) -> f64 {
    if beta <= 40 {
        return 0.0;
    }
    let b = beta as f64;
    let denom = (b / (2.0 * PI * E)).ln();
    if denom <= 0.5 {
        0.0
    } else {
        (b * (4.0f64 / 3.0).ln() / denom).max(0.0)
    }
}

pub fn zonal_gsa_profile(
    m: usize,
    n: usize,
    q: u64,
    sigma_s: f64,
    sigma_e: f64,
    beta: usize,
) -> Vec<f64> {
    let d = m + n + 1;
    let ln_q = (q as f64).ln();
    let ln_zeta = if sigma_s > 0.0 && sigma_e > 0.0 {
        (sigma_e / sigma_s).ln()
    } else {
        0.0
    };
    let total_log_vol = (m as f64) * ln_q + (n as f64) * ln_zeta;
    let floor_val = ln_zeta.min(0.0);
    let ln_delta = ln_root_hermite_factor(beta.max(2));

    let max_span = ((d as f64) * ln_delta).abs() + ln_q.abs() + ln_zeta.abs() + 10.0;
    let mut lo = -max_span;
    let mut hi = max_span;
    for _ in 0..60 {
        let mid = 0.5 * (lo + hi);
        let mut s = 0.0;
        for i in 0..d {
            let unclipped = mid + ((d as isize - 1 - 2 * (i as isize)) as f64) * ln_delta;
            s += unclipped.clamp(floor_val, ln_q);
        }
        if s < total_log_vol {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let mu = 0.5 * (lo + hi);
    let mut profile = Vec::with_capacity(d);
    for i in 0..d {
        let unclipped = mu + ((d as isize - 1 - 2 * (i as isize)) as f64) * ln_delta;
        profile.push(unclipped.clamp(floor_val, ln_q));
    }
    profile
}

pub fn cn11_block_offset(dk: usize) -> f64 {
    if dk <= 1 {
        return 0.0;
    }
    if dk >= 46 {
        return ln_gh_factor(dk);
    }
    let gh = ln_gh_factor(dk);
    let hkz_corr = 0.5 * (dk as f64 / 45.0).ln().abs() * 0.045;
    (gh + hkz_corr).max(0.02 * ((dk - 1) as f64))
}

pub fn simulate_bkz_profile(
    m: usize,
    n: usize,
    q: u64,
    sigma_s: f64,
    sigma_e: f64,
    beta: usize,
    tours: usize,
) -> Vec<f64> {
    let d = m + n + 1;
    assert!(beta >= 2 && beta <= d);
    let ln_q = (q as f64).ln();
    let ln_zeta = if sigma_s > 0.0 && sigma_e > 0.0 {
        (sigma_e / sigma_s).ln()
    } else {
        0.0
    };
    let total_log_vol = (m as f64) * ln_q + (n as f64) * ln_zeta;
    let floor_val = ln_zeta.min(0.0);

    let mut profile = zonal_gsa_profile(m, n, q, sigma_s, sigma_e, 2);

    let mut block_offset = vec![0.0; beta + 1];
    for dk in 2..=beta {
        block_offset[dk] = cn11_block_offset(dk);
    }

    let mut old_prefix = vec![0.0; d + 1];
    let mut new_profile = vec![0.0; d];

    for _tour in 0..tours {
        old_prefix[0] = 0.0;
        for i in 0..d {
            old_prefix[i + 1] = old_prefix[i] + profile[i];
        }

        let mut new_prefix_sum = 0.0;
        let mut active = false;
        for k in 0..(d - 1) {
            let dk = beta.min(d - k);
            let block_log_det = old_prefix[k + dk] - new_prefix_sum;
            let cand_lk = (block_log_det / (dk as f64) + block_offset[dk]).clamp(floor_val, ln_q);

            if cand_lk < profile[k] - 1e-12 {
                active = true;
            }
            let max_allowed =
                (total_log_vol - new_prefix_sum - ((d - 1 - k) as f64) * floor_val).min(ln_q);
            let next_lk = if active {
                cand_lk
            } else {
                profile[k].min(cand_lk)
            }
            .clamp(floor_val, max_allowed.max(floor_val));
            new_profile[k] = next_lk;
            new_prefix_sum += next_lk;
        }
        new_profile[d - 1] = (total_log_vol - new_prefix_sum).clamp(floor_val, ln_q);
        profile.copy_from_slice(&new_profile);
    }

    let sum_now: f64 = profile.iter().sum();
    let diff = total_log_vol - sum_now;
    if diff.abs() > 1e-12 {
        profile[d - 1] += diff;
    }

    profile
}

pub fn bkz_sim_usvp_success(profile: &[f64], beta: usize, sigma_e: f64) -> bool {
    let d = profile.len();
    if beta < 2 || beta > d {
        return false;
    }
    let lhs = 0.5 * (beta as f64).ln() + sigma_e.max(1e-9).ln();
    let rhs = profile[d - beta];
    lhs <= rhs
}
