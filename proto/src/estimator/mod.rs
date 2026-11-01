pub mod attacks;
pub mod bkz;
pub mod failure;

pub use attacks::{
    estimate_dual_attack, estimate_hybrid_mitm, estimate_primal_usvp_gsa,
    estimate_primal_usvp_simulator, AttackEstimate, LweEstimateInput,
};
pub use bkz::{
    bkz_sim_usvp_success, core_svp_classical_bits, core_svp_quantum_bits, d4f_dimension_saving,
    ln_gh_factor, ln_root_hermite_factor, root_hermite_factor, simulate_bkz_profile,
    zonal_gsa_profile,
};
pub use failure::{estimate_mod_pke_failure, estimate_mod_pke_failure_asymmetric, DiscretePMF};

#[derive(Debug, Clone, Copy)]
pub struct SecurityReport {
    pub primal_gsa: AttackEstimate,
    pub primal_sim: AttackEstimate,
    pub dual: AttackEstimate,
    pub hybrid_mitm_bits: f64,
    pub min_classical_bits: f64,
    pub min_quantum_bits: f64,
    pub max_noise: usize,
    pub noise_threshold: usize,
    pub failure_prob: f64,
    pub log2_failure_prob: f64,
}

impl SecurityReport {
    pub fn evaluate_mod_pke(
        k: usize,
        n_poly: usize,
        q: u64,
        eta_opt: Option<usize>,
        d_u: Option<u32>,
        d_v: Option<u32>,
    ) -> Self {
        let n_total = k * n_poly;
        let m_max = (k + 1) * n_poly;
        let (input, pmf) = match eta_opt {
            Some(eta) => (
                LweEstimateInput::new_cbd(n_total, m_max, q, eta, eta),
                DiscretePMF::cbd(eta),
            ),
            None => (
                LweEstimateInput::new_ternary(n_total, m_max, q),
                DiscretePMF::uniform_ternary(),
            ),
        };

        let primal_gsa = estimate_primal_usvp_gsa(&input);
        let primal_sim = estimate_primal_usvp_simulator(&input, 15);
        let dual = estimate_dual_attack(&input);
        let hybrid_mitm_bits = estimate_hybrid_mitm(&input);

        let min_classical_bits = primal_gsa
            .classical_bits
            .min(primal_sim.classical_bits)
            .min(dual.classical_bits)
            .min(hybrid_mitm_bits);
        let min_quantum_bits = primal_gsa
            .quantum_bits
            .min(primal_sim.quantum_bits)
            .min(dual.quantum_bits);

        let (max_noise, noise_threshold, failure_prob, log2_failure_prob) =
            estimate_mod_pke_failure(n_total, n_poly, q, &pmf, &pmf, d_u, d_v);

        Self {
            primal_gsa,
            primal_sim,
            dual,
            hybrid_mitm_bits,
            min_classical_bits,
            min_quantum_bits,
            max_noise,
            noise_threshold,
            failure_prob,
            log2_failure_prob,
        }
    }
}
