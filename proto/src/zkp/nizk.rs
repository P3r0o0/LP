use crate::lwe::math::{ct_eq_slice, norm, sub_mod};
use crate::lwe::poly::Polynomial;
use alloc::vec::Vec;
use rand::Rng;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

pub struct ZKPParams {
    pub n: usize,
    pub q: u64,
    pub bound_b: u64,
    pub beta: u64,
}

pub struct ZKPWitness {
    pub s: Polynomial,
    pub e: Polynomial,
}

impl Drop for ZKPWitness {
    fn drop(&mut self) {
        self.s.zeroize();
        self.e.zeroize();
    }
}

pub struct ZKPPublicInfo {
    pub a: Polynomial,
    pub t: Polynomial,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NIZKProof {
    pub c: Polynomial,
    pub z_s: Polynomial,
    pub z_e: Polynomial,
}

impl NIZKProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.c.coeffs.len() * 24);
        out.extend_from_slice(&self.c.to_bytes());
        out.extend_from_slice(&self.z_s.to_bytes());
        out.extend_from_slice(&self.z_e.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        if bytes.len() != poly_bytes.checked_mul(3)? {
            return None;
        }
        let c = Polynomial::from_bytes(&bytes[0..poly_bytes], n, q)?;
        if !c.is_ternary(q) {
            return None;
        }
        let z_s = Polynomial::from_bytes(&bytes[poly_bytes..2 * poly_bytes], n, q)?;
        let z_e = Polynomial::from_bytes(&bytes[2 * poly_bytes..3 * poly_bytes], n, q)?;
        Some(Self { c, z_s, z_e })
    }
}

impl ZKPParams {
    pub fn new(n: usize, q: u64, bound_b: u64, beta: u64) -> Self {
        assert!(n > 0, "Degree n must be > 0");
        assert!(bound_b >= beta, "Masking bound_b must be >= beta");
        assert!(bound_b < q / 2, "Masking bound_b must be < q / 2");
        Self {
            n,
            q,
            bound_b,
            beta,
        }
    }

    pub fn norm(&self, x: u64) -> u64 {
        norm(x, self.q)
    }

    pub fn inf_norm(&self, poly: &Polynomial) -> u64 {
        poly.norm_inf(self.q)
    }

    pub fn expected_acceptance_rate(&self) -> f64 {
        if self.bound_b < self.beta {
            return 0.0;
        }
        let num = (2 * (self.bound_b - self.beta) + 1) as f64;
        let den = (2 * self.bound_b + 1) as f64;
        let p = num / den;
        let mut acc = 1.0f64;
        for _ in 0..(2 * self.n) {
            acc *= p;
        }
        acc
    }

    pub fn single_attempt_rejection_prob(&self) -> f64 {
        1.0 - self.expected_acceptance_rate()
    }

    pub fn all_attempts_rejection_prob(&self, max_attempts: usize) -> f64 {
        let reject_prob = self.single_attempt_rejection_prob();
        let mut acc = 1.0f64;
        let mut b = reject_prob;
        let mut e = max_attempts;
        while e > 0 {
            if (e & 1) == 1 {
                acc *= b;
            }
            b *= b;
            e >>= 1;
        }
        acc
    }

    pub fn unrejected_tv_distance(&self, shift_inf: u64) -> f64 {
        if shift_inf == 0 {
            return 0.0;
        }
        let span = 2 * self.bound_b + 1;
        if shift_inf >= span {
            return 1.0;
        }
        let overlap = (span - shift_inf) as f64 / (span as f64);
        let mut prod = 1.0f64;
        for _ in 0..(2 * self.n) {
            prod *= overlap;
        }
        1.0 - prod
    }

    pub fn accepted_zk_tv_distance(&self, actual_shift_inf: u64) -> f64 {
        if actual_shift_inf <= self.beta {
            return 0.0;
        }
        let excess = actual_shift_inf - self.beta;
        let box_span = 2 * (self.bound_b - self.beta) + 1;
        if excess >= box_span {
            return 1.0;
        }
        let ratio = (box_span - excess) as f64 / (box_span as f64);
        let mut prod = 1.0f64;
        for _ in 0..(2 * self.n) {
            prod *= ratio;
        }
        1.0 - prod
    }

    pub fn hash_to_challenge(&self, a: &Polynomial, t: &Polynomial, w: &Polynomial) -> Polynomial {
        self.hash_to_challenge_with_context(a, t, w, b"")
    }

    pub fn hash_to_challenge_with_context(
        &self,
        a: &Polynomial,
        t: &Polynomial,
        w: &Polynomial,
        ctx: &[u8],
    ) -> Polynomial {
        let mut hasher = Shake256::default();
        hasher.update(b"LWE-ZKP-NIZK-v1");
        hasher.update(&(self.n as u64).to_le_bytes());
        hasher.update(&self.q.to_le_bytes());
        hasher.update(&self.bound_b.to_le_bytes());
        hasher.update(&self.beta.to_le_bytes());
        for &val in &a.coeffs {
            hasher.update(&val.to_le_bytes());
        }
        for &val in &t.coeffs {
            hasher.update(&val.to_le_bytes());
        }
        for &val in &w.coeffs {
            hasher.update(&val.to_le_bytes());
        }
        if !ctx.is_empty() {
            hasher.update(b"CTX");
            hasher.update(&(ctx.len() as u64).to_le_bytes());
            hasher.update(ctx);
        }
        let mut reader = hasher.finalize_xof();

        let mut coeffs = Vec::with_capacity(self.n);
        let mut buf = [0u8; 1];
        for _ in 0..self.n {
            loop {
                reader.read(&mut buf);
                let byte = buf[0];
                if byte < 255 {
                    let val = match byte % 3 {
                        0 => 0,
                        1 => 1,
                        _ => self.q - 1,
                    };
                    coeffs.push(val);
                    break;
                }
            }
        }
        Polynomial::new(coeffs)
    }

    #[cfg(feature = "std")]
    pub fn prove(&self, a: &Polynomial, witness: &ZKPWitness) -> (ZKPPublicInfo, NIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.prove_with_rng(&mut rng, a, witness)
    }

    pub fn prove_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        a: &Polynomial,
        witness: &ZKPWitness,
    ) -> (ZKPPublicInfo, NIZKProof, u32) {
        self.prove_with_context_and_rng(rng, a, witness, b"")
    }

    #[cfg(feature = "std")]
    pub fn prove_with_context(
        &self,
        a: &Polynomial,
        witness: &ZKPWitness,
        ctx: &[u8],
    ) -> (ZKPPublicInfo, NIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.prove_with_context_and_rng(&mut rng, a, witness, ctx)
    }

    pub fn prove_with_context_and_rng<R: Rng>(
        &self,
        rng: &mut R,
        a: &Polynomial,
        witness: &ZKPWitness,
        ctx: &[u8],
    ) -> (ZKPPublicInfo, NIZKProof, u32) {
        assert_eq!(a.coeffs.len(), self.n);
        assert_eq!(witness.s.coeffs.len(), self.n);
        assert_eq!(witness.e.coeffs.len(), self.n);
        assert!(self.bound_b >= self.beta, "Masking bound_b must be >= beta");

        let t = a.mul_schoolbook(&witness.s, self.q).add(&witness.e, self.q);
        let pub_info = ZKPPublicInfo { a: a.clone(), t };

        let mut attempts = 0;

        loop {
            attempts += 1;
            let mut y_s_coeffs = Vec::with_capacity(self.n);
            let mut y_e_coeffs = Vec::with_capacity(self.n);
            for _ in 0..self.n {
                let val_s = rng.gen_range(0..=(2 * self.bound_b));
                let val_e = rng.gen_range(0..=(2 * self.bound_b));

                let y_s_val = sub_mod(val_s, self.bound_b, self.q);
                let y_e_val = sub_mod(val_e, self.bound_b, self.q);

                y_s_coeffs.push(y_s_val);
                y_e_coeffs.push(y_e_val);
            }
            let mut y_s = Polynomial::new(y_s_coeffs);
            let mut y_e = Polynomial::new(y_e_coeffs);

            let w = a.mul_schoolbook(&y_s, self.q).add(&y_e, self.q);

            let c = self.hash_to_challenge_with_context(a, &pub_info.t, &w, ctx);

            let safe_bound = self.bound_b - self.beta;
            let cs = c.mul_schoolbook(&witness.s, self.q);
            let z_s = y_s.add(&cs, self.q);
            y_s.zeroize();
            if self.inf_norm(&z_s) > safe_bound {
                y_e.zeroize();
                continue;
            }

            let ce = c.mul_schoolbook(&witness.e, self.q);
            let z_e = y_e.add(&ce, self.q);
            y_e.zeroize();
            if self.inf_norm(&z_e) <= safe_bound {
                return (pub_info, NIZKProof { c, z_s, z_e }, attempts);
            }
        }
    }

    pub fn verify(&self, pub_info: &ZKPPublicInfo, proof: &NIZKProof) -> bool {
        self.verify_with_context(pub_info, proof, b"")
    }

    pub fn verify_with_context(
        &self,
        pub_info: &ZKPPublicInfo,
        proof: &NIZKProof,
        ctx: &[u8],
    ) -> bool {
        if self.bound_b < self.beta {
            return false;
        }
        if pub_info.a.coeffs.len() != self.n
            || pub_info.t.coeffs.len() != self.n
            || proof.c.coeffs.len() != self.n
            || proof.z_s.coeffs.len() != self.n
            || proof.z_e.coeffs.len() != self.n
        {
            return false;
        }
        if !pub_info.a.is_canonical(self.q)
            || !pub_info.t.is_canonical(self.q)
            || !proof.c.is_canonical(self.q)
            || !proof.c.is_ternary(self.q)
            || !proof.z_s.is_canonical(self.q)
            || !proof.z_e.is_canonical(self.q)
        {
            return false;
        }

        let safe_bound = self.bound_b - self.beta;
        if self.inf_norm(&proof.z_s) > safe_bound || self.inf_norm(&proof.z_e) > safe_bound {
            return false;
        }

        let az = pub_info.a.mul_schoolbook(&proof.z_s, self.q);
        let az_plus_ze = az.add(&proof.z_e, self.q);
        let ct = proof.c.mul_schoolbook(&pub_info.t, self.q);
        let w_prime = az_plus_ze.sub(&ct, self.q);

        let c_prime = self.hash_to_challenge_with_context(&pub_info.a, &pub_info.t, &w_prime, ctx);

        ct_eq_slice(&proof.c.coeffs, &c_prime.coeffs)
    }
}
