use crate::lwe::pke::{ModPKECiphertext, ModPKEContext, ModPKEPublicKey, ModPKESecretKey};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use core::ptr::write_volatile;
use core::sync::atomic::{compiler_fence, Ordering};
use rand::Rng;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

fn zeroize_bytes(bytes: &mut [u8]) {
    for b in bytes.iter_mut() {
        unsafe {
            write_volatile(b, 0);
        }
    }
    compiler_fence(Ordering::SeqCst);
}

pub struct ModKEMSecretKey {
    pub pke_sk: ModPKESecretKey,
    pub pk: ModPKEPublicKey,
    pub pk_hash: [u8; 32],
    pub z: [u8; 32],
}

impl Drop for ModKEMSecretKey {
    fn drop(&mut self) {
        zeroize_bytes(&mut self.z);
    }
}

pub struct ModKEMContext {
    pub pke: ModPKEContext,
}

impl ModKEMContext {
    pub fn new(k: usize, n: usize, q: u64, t: u64, psi: u64) -> Self {
        assert_eq!(
            t, 2,
            "FO-KEM message modulus t must be 2 (1 bit per coefficient)"
        );
        let pke = ModPKEContext::new(k, n, q, t, psi);
        assert!(
            pke.params.is_zero_failure_guaranteed(),
            "FO-KEM requires 2 * (2 * k * N + 1) < delta for zero decryption failure"
        );
        Self { pke }
    }

    pub fn new_binary(k: usize, n: usize, q: u64, psi: u64) -> Self {
        Self::new(k, n, q, 2, psi)
    }

    pub fn preset_toy_zero_failure() -> Self {
        Self::new_binary(2, 4, 97, 33)
    }

    pub fn preset_light_zero_failure() -> Self {
        let p = crate::lwe::pke::ModPKEParams::preset_light_zero_failure();
        Self::new_binary(p.k, p.n, p.q, p.psi)
    }

    pub fn preset_standard_128bit() -> Self {
        let p = crate::lwe::pke::ModPKEParams::preset_standard_128bit();
        Self::new_binary(p.k, p.n, p.q, p.psi)
    }

    pub fn hash_pk(&self, pk: &ModPKEPublicKey) -> [u8; 32] {
        let mut hasher = Shake256::default();
        hasher.update(b"LWE-RUST-MODKEM-HPK-V1");
        hasher.update(&(self.pke.params.k as u64).to_le_bytes());
        hasher.update(&(self.pke.params.n as u64).to_le_bytes());
        hasher.update(&self.pke.params.q.to_le_bytes());
        hasher.update(&self.pke.params.t.to_le_bytes());
        hasher.update(&self.pke.params.psi.to_le_bytes());
        for row in &pk.a {
            for poly in row {
                for &c in &poly.coeffs {
                    hasher.update(&c.to_le_bytes());
                }
            }
        }
        for poly in &pk.t {
            for &c in &poly.coeffs {
                hasher.update(&c.to_le_bytes());
            }
        }
        let mut out = [0u8; 32];
        hasher.finalize_xof().read(&mut out);
        out
    }

    fn derive_key_and_coins(&self, pk_hash: &[u8; 32], m: &Polynomial) -> ([u8; 32], [u8; 32]) {
        let mut hasher = Shake256::default();
        hasher.update(b"LWE-RUST-MODKEM-G-V1");
        hasher.update(pk_hash);
        for &c in &m.coeffs {
            hasher.update(&c.to_le_bytes());
        }
        let mut reader = hasher.finalize_xof();
        let mut k_shared = [0u8; 32];
        let mut coins = [0u8; 32];
        reader.read(&mut k_shared);
        reader.read(&mut coins);
        (k_shared, coins)
    }

    fn derive_rejection_key(&self, z: &[u8; 32], ct: &ModPKECiphertext) -> [u8; 32] {
        let mut hasher = Shake256::default();
        hasher.update(b"LWE-RUST-MODKEM-J-V1");
        hasher.update(z);
        for poly in &ct.u {
            for &c in &poly.coeffs {
                hasher.update(&c.to_le_bytes());
            }
        }
        for &c in &ct.v.coeffs {
            hasher.update(&c.to_le_bytes());
        }
        let mut k_rej = [0u8; 32];
        hasher.finalize_xof().read(&mut k_rej);
        k_rej
    }

    #[cfg(feature = "std")]
    pub fn keygen(&self) -> (ModKEMSecretKey, ModPKEPublicKey) {
        let mut rng = rand::thread_rng();
        self.keygen_with_rng(&mut rng)
    }

    pub fn keygen_with_rng<R: Rng>(&self, rng: &mut R) -> (ModKEMSecretKey, ModPKEPublicKey) {
        let (pke_sk, pk) = self.pke.keygen_with_rng(rng);
        let pk_hash = self.hash_pk(&pk);
        let mut z = [0u8; 32];
        rng.fill(&mut z);
        (
            ModKEMSecretKey {
                pke_sk,
                pk: pk.clone(),
                pk_hash,
                z,
            },
            pk,
        )
    }

    #[cfg(feature = "std")]
    pub fn encaps(&self, pk: &ModPKEPublicKey) -> (ModPKECiphertext, [u8; 32]) {
        let mut rng = rand::thread_rng();
        self.encaps_with_rng(&mut rng, pk)
    }

    pub fn encaps_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &ModPKEPublicKey,
    ) -> (ModPKECiphertext, [u8; 32]) {
        let n = self.pke.params.n;
        let t = self.pke.params.t;
        let coeffs: Vec<u64> = (0..n).map(|_| rng.gen_range(0..t)).collect();
        let mut m = Polynomial::new(coeffs);

        let pk_hash = self.hash_pk(pk);
        let (k_shared, mut coins) = self.derive_key_and_coins(&pk_hash, &m);
        let ct = self.pke.encrypt_deterministic(pk, &m, &coins);

        m.zeroize();
        zeroize_bytes(&mut coins);
        (ct, k_shared)
    }

    pub fn decaps(&self, sk: &ModKEMSecretKey, ct: &ModPKECiphertext) -> [u8; 32] {
        let k = self.pke.params.k;
        let n = self.pke.params.n;
        let q = self.pke.params.q;

        let is_wf = ct.is_well_formed(k, n, q);
        let dummy_ct;
        let ct_ref = if is_wf {
            ct
        } else {
            dummy_ct = ModPKECiphertext {
                u: vec![Polynomial::zero(n); k],
                v: Polynomial::zero(n),
            };
            &dummy_ct
        };

        let mut m_prime = self.pke.decrypt(&sk.pke_sk, ct_ref);
        let (mut k_prime, mut coins_prime) = self.derive_key_and_coins(&sk.pk_hash, &m_prime);
        let ct_prime = self
            .pke
            .encrypt_deterministic(&sk.pk, &m_prime, &coins_prime);
        let k_rej = self.derive_rejection_key(&sk.z, ct);

        let valid = is_wf && ct_ref.ct_eq(&ct_prime);
        let mask = (valid as u8).wrapping_neg();

        let mut out = [0u8; 32];
        for i in 0..32 {
            out[i] = (k_prime[i] & mask) | (k_rej[i] & !mask);
        }

        m_prime.zeroize();
        zeroize_bytes(&mut k_prime);
        zeroize_bytes(&mut coins_prime);
        out
    }
}
