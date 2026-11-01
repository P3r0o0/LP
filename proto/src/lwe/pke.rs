use crate::lwe::math::{add_mod, mul_mod};
use crate::lwe::module_ntt::{
    matrix_ntt, matrix_ntt_table, ntt_evaluate, ntt_evaluate_table, vector_intt, vector_intt_table,
    vector_ntt, vector_ntt_table,
};
use crate::lwe::ntt::{inv_ntt, pow_mod, NTTTable};
use crate::lwe::poly::Polynomial;
use crate::zkp::mod_nizk::{ModNIZKProof, ModZKPParams, ModZKPPublicInfo, ModZKPWitness};
use alloc::vec;
use alloc::vec::Vec;
use rand::Rng;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

#[derive(Debug, Clone)]
pub struct ModPKEParams {
    pub k: usize,
    pub n: usize,
    pub q: u64,
    pub t: u64,
    pub delta: u64,
    pub psi: u64,
}

impl ModPKEParams {
    pub fn new(k: usize, n: usize, q: u64, t: u64, psi: u64) -> Self {
        assert!(k > 0 && n > 0, "Dimensions k and n must be > 0");
        assert!(t > 0 && q > t, "Moduli must satisfy q > t > 0");
        assert_eq!(
            pow_mod(psi, n as u64, q),
            q - 1,
            "psi must be a 2N-th root of unity satisfying psi^N == -1 mod q"
        );
        Self {
            k,
            n,
            q,
            t,
            delta: q / t,
            psi,
        }
    }

    pub fn max_ternary_noise_bound(&self) -> u64 {
        2 * (self.k as u64) * (self.n as u64) + 1
    }

    pub fn is_zero_failure_guaranteed(&self) -> bool {
        2 * self.max_ternary_noise_bound() < self.delta
    }

    pub fn find_psi(n: usize, q: u64) -> u64 {
        let two_n = 2 * (n as u64);
        assert_eq!(
            (q - 1) % two_n,
            0,
            "2N must divide q - 1 for a negacyclic NTT root of unity to exist"
        );
        let exp = (q - 1) / two_n;
        for g in 2..q {
            let psi = pow_mod(g, exp, q);
            if pow_mod(psi, n as u64, q) == q - 1 {
                return psi;
            }
        }
        panic!("No 2N-th root of unity found for n={n}, q={q}");
    }

    pub fn preset_toy_zero_failure() -> Self {
        Self::new(2, 4, 97, 2, 33)
    }

    pub fn preset_light_zero_failure() -> Self {
        let psi = Self::find_psi(256, 7681);
        Self::new(3, 256, 7681, 2, psi)
    }

    pub fn preset_standard_128bit() -> Self {
        let psi = Self::find_psi(256, 12289);
        Self::new(4, 256, 12289, 2, psi)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModPKESecretKey {
    pub s: Vec<Polynomial>,
    pub e: Vec<Polynomial>,
}

impl ModPKESecretKey {
    pub fn is_well_formed(&self, k: usize, n: usize, q: u64) -> bool {
        self.s.len() == k
            && self.e.len() == k
            && self
                .s
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q) && p.is_ternary(q))
            && self
                .e
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q) && p.is_ternary(q))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for p in &self.s {
            out.extend_from_slice(&p.to_bytes());
        }
        for p in &self.e {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], k: usize, n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        let total_polys = k.checked_mul(2)?;
        if bytes.len() != total_polys.checked_mul(poly_bytes)? {
            return None;
        }
        let mut offset = 0;
        let mut s = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            if !p.is_ternary(q) {
                return None;
            }
            offset += poly_bytes;
            s.push(p);
        }
        let mut e = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            if !p.is_ternary(q) {
                return None;
            }
            offset += poly_bytes;
            e.push(p);
        }
        Some(Self { s, e })
    }
}

impl Drop for ModPKESecretKey {
    fn drop(&mut self) {
        for p in self.s.iter_mut() {
            p.zeroize();
        }
        for p in self.e.iter_mut() {
            p.zeroize();
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModPKECompressedPublicKey {
    pub rho: [u8; 32],
    pub t: Vec<Polynomial>,
}

impl ModPKECompressedPublicKey {
    pub fn is_well_formed(&self, k: usize, n: usize, q: u64) -> bool {
        self.t.len() == k
            && self
                .t
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.rho);
        for p in &self.t {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], k: usize, n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        let expected_len = 32usize.checked_add(k.checked_mul(poly_bytes)?)?;
        if bytes.len() != expected_len {
            return None;
        }
        let mut rho = [0u8; 32];
        rho.copy_from_slice(&bytes[0..32]);
        let mut offset = 32;
        let mut t = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            offset += poly_bytes;
            t.push(p);
        }
        Some(Self { rho, t })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModPKEPublicKey {
    pub a: Vec<Vec<Polynomial>>,
    pub t: Vec<Polynomial>,
}

impl ModPKEPublicKey {
    pub fn is_well_formed(&self, k: usize, n: usize, q: u64) -> bool {
        self.a.len() == k
            && self.t.len() == k
            && self.a.iter().all(|row| {
                row.len() == k && row.iter().all(|p| p.coeffs.len() == n && p.is_canonical(q))
            })
            && self
                .t
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for row in &self.a {
            for poly in row {
                out.extend_from_slice(&poly.to_bytes());
            }
        }
        for poly in &self.t {
            out.extend_from_slice(&poly.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], k: usize, n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        let total_polys = k.checked_mul(k)?.checked_add(k)?;
        if bytes.len() != total_polys.checked_mul(poly_bytes)? {
            return None;
        }
        let mut offset = 0;
        let mut a = Vec::with_capacity(k);
        for _ in 0..k {
            let mut row = Vec::with_capacity(k);
            for _ in 0..k {
                let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
                offset += poly_bytes;
                row.push(p);
            }
            a.push(row);
        }
        let mut t = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            offset += poly_bytes;
            t.push(p);
        }
        Some(Self { a, t })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModPKECiphertext {
    pub u: Vec<Polynomial>,
    pub v: Polynomial,
}

impl ModPKECiphertext {
    pub fn is_well_formed(&self, k: usize, n: usize, q: u64) -> bool {
        self.u.len() == k
            && self.v.coeffs.len() == n
            && self.v.is_canonical(q)
            && self
                .u
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
    }

    pub fn ct_eq(&self, other: &Self) -> bool {
        if self.u.len() != other.u.len() {
            return false;
        }
        let mut eq = self.v.ct_eq(&other.v);
        for (u1, u2) in self.u.iter().zip(other.u.iter()) {
            eq &= u1.ct_eq(u2);
        }
        eq
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for poly in &self.u {
            out.extend_from_slice(&poly.to_bytes());
        }
        out.extend_from_slice(&self.v.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], k: usize, n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        let total_polys = k.checked_add(1)?;
        if bytes.len() != total_polys.checked_mul(poly_bytes)? {
            return None;
        }
        let mut offset = 0;
        let mut u = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            offset += poly_bytes;
            u.push(p);
        }
        let v = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
        Some(Self { u, v })
    }

    pub fn compress(&self, q: u64, d_u: u32, d_v: u32) -> Self {
        let u = self.u.iter().map(|p| p.compress(q, d_u)).collect();
        let v = self.v.compress(q, d_v);
        Self { u, v }
    }

    pub fn decompress(&self, q: u64, d_u: u32, d_v: u32) -> Self {
        let u = self.u.iter().map(|p| p.decompress(q, d_u)).collect();
        let v = self.v.decompress(q, d_v);
        Self { u, v }
    }
}

pub struct ModPKEContext {
    pub params: ModPKEParams,
    pub ntt_table: Option<NTTTable>,
}

impl ModPKEContext {
    pub fn new(k: usize, n: usize, q: u64, t: u64, psi: u64) -> Self {
        let params = ModPKEParams::new(k, n, q, t, psi);
        let ntt_table = if n.is_power_of_two() && q < (1u64 << 62) {
            Some(NTTTable::new(n, psi, q))
        } else {
            None
        };
        Self { params, ntt_table }
    }

    pub fn expand_matrix_a(&self, rho: &[u8; 32]) -> Vec<Vec<Polynomial>> {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;
        let bit_len = 64 - q.leading_zeros();
        let mask = if bit_len == 64 {
            u64::MAX
        } else {
            (1u64 << bit_len) - 1
        };

        let mut a = Vec::with_capacity(k);
        for i in 0..k {
            let mut row = Vec::with_capacity(k);
            for j in 0..k {
                let mut hasher = Shake256::default();
                hasher.update(b"LWE-RUST-MODPKE-MAT-A-V1");
                hasher.update(&(k as u64).to_le_bytes());
                hasher.update(&(n as u64).to_le_bytes());
                hasher.update(&q.to_le_bytes());
                hasher.update(&(i as u64).to_le_bytes());
                hasher.update(&(j as u64).to_le_bytes());
                hasher.update(rho);
                let mut reader = hasher.finalize_xof();

                let mut coeffs = Vec::with_capacity(n);
                let mut buf = [0u8; 8];
                while coeffs.len() < n {
                    reader.read(&mut buf);
                    let candidate = u64::from_le_bytes(buf) & mask;
                    if candidate < q {
                        coeffs.push(candidate);
                    }
                }
                row.push(Polynomial::new(coeffs));
            }
            a.push(row);
        }
        a
    }

    #[cfg(feature = "std")]
    pub fn keygen_compressed(
        &self,
    ) -> (ModPKESecretKey, ModPKEPublicKey, ModPKECompressedPublicKey) {
        let mut rng = rand::thread_rng();
        self.keygen_compressed_with_rng(&mut rng)
    }

    pub fn keygen_compressed_with_rng<R: Rng>(
        &self,
        rng: &mut R,
    ) -> (ModPKESecretKey, ModPKEPublicKey, ModPKECompressedPublicKey) {
        let k = self.params.k;
        let mut rho = [0u8; 32];
        rng.fill(&mut rho);
        let a = self.expand_matrix_a(&rho);
        let s: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let e: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();

        let t = if let Some(ref table) = self.ntt_table {
            let a_ntt = matrix_ntt_table(&a, table);
            let s_ntt = vector_ntt_table(&s, table);
            let e_ntt = vector_ntt_table(&e, table);
            let t_ntt = ntt_evaluate_table(&a_ntt, &s_ntt, &e_ntt, table);
            vector_intt_table(&t_ntt, table)
        } else {
            let a_ntt = matrix_ntt(&a, self.params.psi, self.params.q);
            let s_ntt = vector_ntt(&s, self.params.psi, self.params.q);
            let e_ntt = vector_ntt(&e, self.params.psi, self.params.q);
            let t_ntt = ntt_evaluate(&a_ntt, &s_ntt, &e_ntt, self.params.q);
            vector_intt(&t_ntt, self.params.psi, self.params.q)
        };

        let pk = ModPKEPublicKey { a, t: t.clone() };
        let cpk = ModPKECompressedPublicKey { rho, t };
        (ModPKESecretKey { s, e }, pk, cpk)
    }

    pub fn decompress_public_key(&self, cpk: &ModPKECompressedPublicKey) -> ModPKEPublicKey {
        let a = self.expand_matrix_a(&cpk.rho);
        ModPKEPublicKey {
            a,
            t: cpk.t.clone(),
        }
    }

    #[cfg(feature = "std")]
    pub fn keygen(&self) -> (ModPKESecretKey, ModPKEPublicKey) {
        let mut rng = rand::thread_rng();
        self.keygen_with_rng(&mut rng)
    }

    pub fn keygen_with_rng<R: Rng>(&self, rng: &mut R) -> (ModPKESecretKey, ModPKEPublicKey) {
        let k = self.params.k;
        let s: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let e: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let a: Vec<Vec<Polynomial>> = (0..k)
            .map(|_| (0..k).map(|_| self.gen_uniform_poly(rng)).collect())
            .collect();

        let t = if let Some(ref table) = self.ntt_table {
            let a_ntt = matrix_ntt_table(&a, table);
            let s_ntt = vector_ntt_table(&s, table);
            let e_ntt = vector_ntt_table(&e, table);
            let t_ntt = ntt_evaluate_table(&a_ntt, &s_ntt, &e_ntt, table);
            vector_intt_table(&t_ntt, table)
        } else {
            let a_ntt = matrix_ntt(&a, self.params.psi, self.params.q);
            let s_ntt = vector_ntt(&s, self.params.psi, self.params.q);
            let e_ntt = vector_ntt(&e, self.params.psi, self.params.q);
            let t_ntt = ntt_evaluate(&a_ntt, &s_ntt, &e_ntt, self.params.q);
            vector_intt(&t_ntt, self.params.psi, self.params.q)
        };

        (ModPKESecretKey { s, e }, ModPKEPublicKey { a, t })
    }

    #[cfg(feature = "std")]
    pub fn verifiable_keygen(
        &self,
        bound_b: u64,
        beta: u64,
    ) -> (ModPKESecretKey, ModPKEPublicKey, ModNIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.verifiable_keygen_with_rng(&mut rng, bound_b, beta)
    }

    pub fn verifiable_keygen_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        bound_b: u64,
        beta: u64,
    ) -> (ModPKESecretKey, ModPKEPublicKey, ModNIZKProof, u32) {
        let (sk, pk) = self.keygen_with_rng(rng);
        let zkp_params = ModZKPParams::new(
            self.params.k,
            self.params.k,
            self.params.n,
            self.params.q,
            bound_b,
            beta,
            self.params.psi,
        );
        let witness = ModZKPWitness {
            s: sk.s.clone(),
            e: sk.e.clone(),
        };
        let (pub_info, proof, attempts) = zkp_params.prove_with_rng(rng, &pk.a, &witness);
        debug_assert_eq!(pub_info.t, pk.t);
        (sk, pk, proof, attempts)
    }

    pub fn verify_public_key(
        &self,
        pk: &ModPKEPublicKey,
        proof: &ModNIZKProof,
        bound_b: u64,
        beta: u64,
    ) -> bool {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;
        if bound_b <= beta || bound_b >= q / 2 || !pk.is_well_formed(k, n, q) {
            return false;
        }
        let zkp_params = ModZKPParams::new(k, k, n, q, bound_b, beta, self.params.psi);
        let pub_info = ModZKPPublicInfo {
            a: pk.a.clone(),
            t: pk.t.clone(),
        };
        zkp_params.verify(&pub_info, proof)
    }

    #[cfg(feature = "std")]
    pub fn encrypt(&self, pk: &ModPKEPublicKey, pt: &Polynomial) -> ModPKECiphertext {
        let mut rng = rand::thread_rng();
        self.encrypt_with_rng(&mut rng, pk, pt)
    }

    pub fn encrypt_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &ModPKEPublicKey,
        pt: &Polynomial,
    ) -> ModPKECiphertext {
        let k = self.params.k;
        let mut r: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let mut e1: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let mut e2: Polynomial = self.gen_ternary_poly(rng);

        let ct = self.encrypt_with_randomness(pk, pt, &r, &e1, &e2);
        for p in r.iter_mut() {
            p.zeroize();
        }
        for p in e1.iter_mut() {
            p.zeroize();
        }
        e2.zeroize();
        ct
    }

    pub fn encrypt_deterministic(
        &self,
        pk: &ModPKEPublicKey,
        pt: &Polynomial,
        coins: &[u8; 32],
    ) -> ModPKECiphertext {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;

        let mut hasher = Shake256::default();
        hasher.update(b"LWE-RUST-MODPKE-COINS-V1");
        hasher.update(&(k as u64).to_le_bytes());
        hasher.update(&(n as u64).to_le_bytes());
        hasher.update(&q.to_le_bytes());
        hasher.update(coins);
        let mut reader = hasher.finalize_xof();

        let mut sample_xof_ternary_ct = || -> Polynomial {
            let mut buf = vec![0u8; n * 4];
            reader.read(&mut buf);
            let mut coeffs = Vec::with_capacity(n);
            for chunk in buf.chunks_exact(4) {
                let mut arr = [0u8; 4];
                arr.copy_from_slice(chunk);
                let x = u32::from_le_bytes(arr) as u64;
                let q3 = (x.wrapping_mul(0xAAAA_AAABu64)) >> 33;
                let rem = x.wrapping_sub(q3.wrapping_mul(3));
                let is_one = ((rem == 1) as u64).wrapping_neg();
                let is_two = ((rem == 2) as u64).wrapping_neg();
                let val = (1u64 & is_one) | ((q - 1) & is_two);
                coeffs.push(val);
            }
            Polynomial::new(coeffs)
        };

        let mut r: Vec<Polynomial> = (0..k).map(|_| sample_xof_ternary_ct()).collect();
        let mut e1: Vec<Polynomial> = (0..k).map(|_| sample_xof_ternary_ct()).collect();
        let mut e2: Polynomial = sample_xof_ternary_ct();

        let ct = self.encrypt_with_randomness(pk, pt, &r, &e1, &e2);
        for p in r.iter_mut() {
            p.zeroize();
        }
        for p in e1.iter_mut() {
            p.zeroize();
        }
        e2.zeroize();
        ct
    }

    pub fn encrypt_with_randomness(
        &self,
        pk: &ModPKEPublicKey,
        pt: &Polynomial,
        r: &[Polynomial],
        e1: &[Polynomial],
        e2: &Polynomial,
    ) -> ModPKECiphertext {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;
        let psi = self.params.psi;
        assert_eq!(pt.coeffs.len(), n);
        assert_eq!(r.len(), k);
        assert_eq!(e1.len(), k);
        assert_eq!(e2.coeffs.len(), n);

        let mut a_t = vec![vec![Polynomial::zero(n); k]; k];
        for i in 0..k {
            for j in 0..k {
                a_t[i][j] = pk.a[j][i].clone();
            }
        }

        let (u, tr) = if let Some(ref table) = self.ntt_table {
            let a_t_ntt = matrix_ntt_table(&a_t, table);
            let r_ntt = vector_ntt_table(r, table);
            let e1_ntt = vector_ntt_table(e1, table);
            let u_ntt = ntt_evaluate_table(&a_t_ntt, &r_ntt, &e1_ntt, table);
            let u = vector_intt_table(&u_ntt, table);

            let t_ntt = vector_ntt_table(&pk.t, table);
            let mut tr_ntt = vec![0u64; n];
            for i in 0..k {
                for x in 0..n {
                    let prod = table.barrett.mul_mod(t_ntt[i][x], r_ntt[i][x]);
                    tr_ntt[x] = add_mod(tr_ntt[x], prod, q);
                }
            }
            let tr = table.inverse(&tr_ntt);
            (u, tr)
        } else {
            let a_t_ntt = matrix_ntt(&a_t, psi, q);
            let r_ntt = vector_ntt(r, psi, q);
            let e1_ntt = vector_ntt(e1, psi, q);
            let u_ntt = ntt_evaluate(&a_t_ntt, &r_ntt, &e1_ntt, q);
            let u = vector_intt(&u_ntt, psi, q);

            let t_ntt = vector_ntt(&pk.t, psi, q);
            let mut tr_ntt = vec![0u64; n];
            for i in 0..k {
                for x in 0..n {
                    let prod = mul_mod(t_ntt[i][x], r_ntt[i][x], q);
                    tr_ntt[x] = add_mod(tr_ntt[x], prod, q);
                }
            }
            let tr = inv_ntt(&tr_ntt, psi, q);
            (u, tr)
        };

        let mut delta_m = pt.clone();
        for c in delta_m.coeffs.iter_mut() {
            *c = mul_mod(*c, self.params.delta, q);
        }

        let v = tr.add(e2, q).add(&delta_m, q);

        ModPKECiphertext { u, v }
    }

    pub fn encryption_matrix(&self, pk: &ModPKEPublicKey) -> Vec<Vec<Polynomial>> {
        let k = self.params.k;
        let n = self.params.n;
        let mut m_enc = vec![vec![Polynomial::zero(n); k]; k + 1];
        for i in 0..k {
            for j in 0..k {
                m_enc[i][j] = pk.a[j][i].clone();
            }
        }
        for j in 0..k {
            m_enc[k][j] = pk.t[j].clone();
        }
        m_enc
    }

    #[cfg(feature = "std")]
    pub fn verifiable_encrypt(
        &self,
        pk: &ModPKEPublicKey,
        pt: &Polynomial,
        bound_b: u64,
        beta: u64,
    ) -> (ModPKECiphertext, ModNIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.verifiable_encrypt_with_rng(&mut rng, pk, pt, bound_b, beta)
    }

    pub fn verifiable_encrypt_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &ModPKEPublicKey,
        pt: &Polynomial,
        bound_b: u64,
        beta: u64,
    ) -> (ModPKECiphertext, ModNIZKProof, u32) {
        let k = self.params.k;
        let r: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let e1: Vec<Polynomial> = (0..k).map(|_| self.gen_ternary_poly(rng)).collect();
        let e2: Polynomial = self.gen_ternary_poly(rng);

        let ct = self.encrypt_with_randomness(pk, pt, &r, &e1, &e2);

        let m_enc = self.encryption_matrix(pk);
        let mut e_ext = e1;
        e_ext.push(e2);
        let witness = ModZKPWitness { s: r, e: e_ext };

        let zkp_params = ModZKPParams::new(
            k + 1,
            k,
            self.params.n,
            self.params.q,
            bound_b,
            beta,
            self.params.psi,
        );
        let (_pub_info, proof, attempts) = zkp_params.prove_with_rng(rng, &m_enc, &witness);
        (ct, proof, attempts)
    }

    pub fn verify_ciphertext(
        &self,
        pk: &ModPKEPublicKey,
        ct: &ModPKECiphertext,
        pt: &Polynomial,
        proof: &ModNIZKProof,
        bound_b: u64,
        beta: u64,
    ) -> bool {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;
        if bound_b <= beta
            || bound_b >= q / 2
            || !pk.is_well_formed(k, n, q)
            || !ct.is_well_formed(k, n, q)
            || pt.coeffs.len() != n
            || !pt.is_canonical(self.params.t)
        {
            return false;
        }

        let mut delta_m = pt.clone();
        for c in delta_m.coeffs.iter_mut() {
            *c = mul_mod(*c, self.params.delta, q);
        }
        let v_minus_dm = ct.v.sub(&delta_m, q);

        let mut target = ct.u.clone();
        target.push(v_minus_dm);

        let m_enc = self.encryption_matrix(pk);
        let zkp_params = ModZKPParams::new(k + 1, k, n, q, bound_b, beta, self.params.psi);
        let pub_info = ModZKPPublicInfo {
            a: m_enc,
            t: target,
        };
        zkp_params.verify(&pub_info, proof)
    }

    pub fn decrypt(&self, sk: &ModPKESecretKey, ct: &ModPKECiphertext) -> Polynomial {
        let k = self.params.k;
        let n = self.params.n;
        let q = self.params.q;
        let psi = self.params.psi;

        let su = if let Some(ref table) = self.ntt_table {
            let s_ntt = vector_ntt_table(&sk.s, table);
            let u_ntt = vector_ntt_table(&ct.u, table);
            let mut su_ntt = vec![0u64; n];
            for i in 0..k {
                for x in 0..n {
                    let prod = table.barrett.mul_mod(s_ntt[i][x], u_ntt[i][x]);
                    su_ntt[x] = add_mod(su_ntt[x], prod, q);
                }
            }
            table.inverse(&su_ntt)
        } else {
            let s_ntt = vector_ntt(&sk.s, psi, q);
            let u_ntt = vector_ntt(&ct.u, psi, q);
            let mut su_ntt = vec![0u64; n];
            for i in 0..k {
                for x in 0..n {
                    let prod = mul_mod(s_ntt[i][x], u_ntt[i][x], q);
                    su_ntt[x] = add_mod(su_ntt[x], prod, q);
                }
            }
            inv_ntt(&su_ntt, psi, q)
        };

        let phase = ct.v.sub(&su, q);

        let mut m = Polynomial::zero(n);
        let t128 = self.params.t as u128;
        let q128 = q as u128;
        for i in 0..n {
            let val = phase.coeffs[i] as u128;
            m.coeffs[i] = (((val * t128 + q128 / 2) / q128) % t128) as u64;
        }
        m
    }

    fn gen_uniform_poly<R: Rng>(&self, rng: &mut R) -> Polynomial {
        let coeffs = (0..self.params.n)
            .map(|_| rng.gen_range(0..self.params.q))
            .collect();
        Polynomial::new(coeffs)
    }

    fn gen_ternary_poly<R: Rng>(&self, rng: &mut R) -> Polynomial {
        let q = self.params.q;
        let coeffs = (0..self.params.n)
            .map(|_| match rng.gen_range(0..3) {
                0 => 0,
                1 => 1,
                _ => q - 1,
            })
            .collect();
        Polynomial::new(coeffs)
    }
}
