use std::f64::consts::PI;

use super::bkz::{
    bkz_sim_usvp_success, core_svp_classical_bits, core_svp_quantum_bits, d4f_dimension_saving,
    ln_root_hermite_factor, simulate_bkz_profile,
};

#[derive(Debug, Clone, Copy)]
pub struct LweEstimateInput {
    pub n: usize,
    pub m_max: usize,
    pub q: u64,
    pub sigma_s: f64,
    pub sigma_e: f64,
    pub secret_bound: u64,
}

impl LweEstimateInput {
    pub fn new_ternary(n: usize, m_max: usize, q: u64) -> Self {
        let sigma = (2.0f64 / 3.0).sqrt();
        Self {
            n,
            m_max,
            q,
            sigma_s: sigma,
            sigma_e: sigma,
            secret_bound: 1,
        }
    }

    pub fn new_cbd(n: usize, m_max: usize, q: u64, eta_s: usize, eta_e: usize) -> Self {
        Self {
            n,
            m_max,
            q,
            sigma_s: (eta_s as f64 / 2.0).sqrt(),
            sigma_e: (eta_e as f64 / 2.0).sqrt(),
            secret_bound: eta_s as u64,
        }
    }

    pub fn new_gaussian(
        n: usize,
        m_max: usize,
        q: u64,
        sigma_s: f64,
        sigma_e: f64,
        secret_bound: u64,
    ) -> Self {
        Self {
            n,
            m_max,
            q,
            sigma_s,
            sigma_e,
            secret_bound,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AttackEstimate {
    pub beta: usize,
    pub m_opt: usize,
    pub d: usize,
    pub classical_bits: f64,
    pub quantum_bits: f64,
    pub d4f_classical_bits: f64,
    pub he_standard_bits: f64,
}

impl AttackEstimate {
    pub fn from_beta(beta: usize, m_opt: usize, d: usize) -> Self {
        let g = d4f_dimension_saving(beta);
        let eff_beta = ((beta as f64) - g).max(2.0);
        let classical = core_svp_classical_bits(beta);
        Self {
            beta,
            m_opt,
            d,
            classical_bits: classical,
            quantum_bits: core_svp_quantum_bits(beta),
            d4f_classical_bits: 0.292 * eff_beta,
            he_standard_bits: classical + 16.4 + (8.0 * (d.max(1) as f64)).log2(),
        }
    }
}

#[inline]
pub fn primal_usvp_gsa_succeeds(input: &LweEstimateInput, m: usize, beta: usize) -> bool {
    let d = m + input.n + 1;
    if beta < 2 || beta > d {
        return false;
    }
    let ln_q = (input.q as f64).ln();
    let ln_zeta = (input.sigma_e / input.sigma_s).ln();
    let ln_vol = (m as f64) * ln_q + (input.n as f64) * ln_zeta;
    let ln_delta = ln_root_hermite_factor(beta);

    let lhs = 0.5 * (beta as f64).ln() + input.sigma_e.max(1e-9).ln();
    let rhs = ln_vol / (d as f64) + ((2 * beta) as isize - (d as isize) - 1) as f64 * ln_delta;
    lhs <= rhs
}

fn min_beta_primal_gsa_for_m(input: &LweEstimateInput, m: usize) -> usize {
    let d = m + input.n + 1;
    let mut lo = 2usize;
    let mut hi = d;
    if !primal_usvp_gsa_succeeds(input, m, hi) {
        return d;
    }
    while lo < hi {
        let mid = (lo + hi) / 2;
        if primal_usvp_gsa_succeeds(input, m, mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

pub fn estimate_primal_usvp_gsa(input: &LweEstimateInput) -> AttackEstimate {
    let m_upper = input.m_max.max(1).min(input.n * 4);
    let step = (m_upper / 256).max(1);

    let mut best_beta = usize::MAX;
    let mut best_m = input.n.min(m_upper).max(1);

    let mut m = 1;
    while m <= m_upper {
        let beta = min_beta_primal_gsa_for_m(input, m);
        if beta < best_beta {
            best_beta = beta;
            best_m = m;
        }
        m += step;
    }

    let fine_start = best_m.saturating_sub(step * 2).max(1);
    let fine_end = (best_m + step * 2).min(m_upper);
    for m_fine in fine_start..=fine_end {
        let beta = min_beta_primal_gsa_for_m(input, m_fine);
        if beta < best_beta {
            best_beta = beta;
            best_m = m_fine;
        }
    }

    AttackEstimate::from_beta(best_beta, best_m, best_m + input.n + 1)
}

pub fn estimate_primal_usvp_simulator(input: &LweEstimateInput, tours: usize) -> AttackEstimate {
    let gsa = estimate_primal_usvp_gsa(input);
    let m_upper = input.m_max.max(1).min(input.n * 4);

    let mut best_beta = usize::MAX;
    let mut best_m = gsa.m_opt;

    let candidates = [
        gsa.m_opt.saturating_sub(32).max(1),
        gsa.m_opt,
        (gsa.m_opt + 32).min(m_upper),
    ];

    for &m in &candidates {
        let d = m + input.n + 1;
        let mut lo = 2usize;
        let mut hi = d;
        while lo < hi {
            let mid = (lo + hi) / 2;
            let profile = simulate_bkz_profile(
                m,
                input.n,
                input.q,
                input.sigma_s,
                input.sigma_e,
                mid,
                tours,
            );
            if bkz_sim_usvp_success(&profile, mid, input.sigma_e) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        if lo < best_beta {
            best_beta = lo;
            best_m = m;
        }
    }

    AttackEstimate::from_beta(best_beta, best_m, best_m + input.n + 1)
}

pub fn estimate_dual_attack(input: &LweEstimateInput) -> AttackEstimate {
    let m_upper = input.m_max.max(1).min(input.n * 4);
    let ln_q = (input.q as f64).ln();
    let ln_2 = 2.0f64.ln();
    let ln_ratio = (input.sigma_s / input.sigma_e).ln();

    let primal = estimate_primal_usvp_gsa(input);
    let beta_min = (primal.beta.saturating_sub(80)).max(2);
    let beta_max = (primal.beta + 80).min(m_upper + input.n);

    let mut best_cost_classical = f64::INFINITY;
    let mut best_beta = primal.beta;
    let mut best_m = primal.m_opt;

    for beta in beta_min..=beta_max {
        let ln_delta = ln_root_hermite_factor(beta);
        let num = (input.n as f64) * (ln_q + ln_ratio);
        let d_continuous = if num > 0.0 {
            (num / ln_delta).sqrt().round() as usize
        } else {
            input.n + 1
        };
        let m_cand = d_continuous
            .saturating_sub(input.n)
            .clamp(1, m_upper)
            .max(beta.saturating_sub(input.n));

        for m in [
            m_cand.saturating_sub(16).max(1),
            m_cand,
            (m_cand + 16).min(m_upper),
        ] {
            let d = m + input.n;
            if beta > d {
                continue;
            }
            let ln_l =
                ((d - 1) as f64) * ln_delta + ((input.n as f64) * (ln_q + ln_ratio)) / (d as f64);
            let ln_tau = ln_l + input.sigma_e.max(1e-9).ln() - ln_q;
            if ln_tau > 4.0 {
                continue;
            }
            let tau = ln_tau.exp();
            let log2_nvec = 4.0 * PI * PI * tau * tau / ln_2;
            let extra_calls_bits = (log2_nvec - 0.2075 * (beta as f64)).max(0.0);
            let total_classical = core_svp_classical_bits(beta) + extra_calls_bits;

            if total_classical < best_cost_classical {
                best_cost_classical = total_classical;
                best_beta = beta;
                best_m = m;
            }
        }
    }

    let mut est = AttackEstimate::from_beta(best_beta, best_m, best_m + input.n);
    if best_cost_classical.is_finite() {
        let extra = (best_cost_classical - est.classical_bits).max(0.0);
        est.classical_bits = best_cost_classical;
        est.quantum_bits += extra;
        est.d4f_classical_bits += extra;
        est.he_standard_bits += extra;
    }
    est
}

pub fn estimate_hybrid_mitm(input: &LweEstimateInput) -> f64 {
    let alphabet_size = (2 * input.secret_bound + 1) as f64;
    let log2_alphabet = alphabet_size.log2();
    let sqrt_2_over_pi = (2.0 / PI).sqrt();
    let ln_2 = 2.0f64.ln();

    let base_primal = estimate_primal_usvp_gsa(input).classical_bits;
    let mut best_bits = base_primal;

    let max_k = (input.n / 2).min(256);
    let step = (max_k / 32).max(1);
    let mut k = step;
    while k <= max_k {
        let reduced_input = LweEstimateInput {
            n: input.n - k,
            ..*input
        };
        let lat_est = estimate_primal_usvp_gsa(&reduced_input);
        let profile = super::bkz::zonal_gsa_profile(
            lat_est.m_opt,
            reduced_input.n,
            reduced_input.q,
            reduced_input.sigma_s,
            reduced_input.sigma_e,
            lat_est.beta,
        );
        let mut neg_log2_psucc = 0.0;
        for &ln_bi in &profile {
            let bi = ln_bi.exp();
            let ratio = sqrt_2_over_pi * reduced_input.sigma_e / bi.max(1e-9);
            let p_i = (1.0 - ratio).clamp(0.05, 1.0);
            neg_log2_psucc -= p_i.ln() / ln_2;
        }

        let mitm_bits = (0.5 * (k as f64) * log2_alphabet + neg_log2_psucc)
            .min((k as f64) * log2_alphabet + lat_est.classical_bits);
        let combined = lat_est.classical_bits.max(mitm_bits);
        if combined < best_bits {
            best_bits = combined;
        }
        k += step;
    }

    best_bits
}
