use crate::lwe::math::mul_mod;
use crate::lwe::ntt::{pow_mod, NTTTable};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use rand::Rng;

pub struct BFVParams {
    pub n: usize,
    pub q: u64,
    pub t: u64,
    pub delta: u64,
    pub psi: Option<u64>,
}

impl BFVParams {
    pub fn is_mul_overflow_safe(&self) -> bool {
        let qm1 = (self.q.saturating_sub(1)) as u128;
        let max_prod = qm1
            .checked_mul(qm1)
            .and_then(|x| x.checked_mul((self.n as u128).saturating_mul(2)));
        match max_prod {
            Some(v) => v <= (i128::MAX as u128),
            None => false,
        }
    }

    pub fn new(n: usize, q: u64, t: u64) -> Self {
        assert!(n > 0, "Degree n must be > 0");
        assert!(t > 0 && q > t, "Moduli must satisfy q > t > 0");
        let params = Self {
            n,
            q,
            t,
            delta: q / t,
            psi: None,
        };
        assert!(
            params.is_mul_overflow_safe(),
            "BFV parameters (n={}, q={}) exceed i128 unreduced multiplication bound 2*N*(q-1)^2 <= i128::MAX",
            n,
            q
        );
        params
    }

    pub fn new_with_ntt(n: usize, q: u64, t: u64, psi: u64) -> Self {
        assert!(n > 0, "Degree n must be > 0");
        assert!(t > 0 && q > t, "Moduli must satisfy q > t > 0");
        assert_eq!(
            pow_mod(psi, n as u64, q),
            q - 1,
            "psi must be a 2N-th root of unity satisfying psi^N == -1 mod q"
        );
        let params = Self {
            n,
            q,
            t,
            delta: q / t,
            psi: Some(psi),
        };
        assert!(
            params.is_mul_overflow_safe(),
            "BFV parameters (n={}, q={}) exceed i128 unreduced multiplication bound 2*N*(q-1)^2 <= i128::MAX",
            n,
            q
        );
        params
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretKey(pub Polynomial);

impl SecretKey {
    pub fn is_well_formed(&self, n: usize, q: u64) -> bool {
        self.0.coeffs.len() == n && self.0.is_canonical(q) && self.0.is_ternary(q)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        let p = Polynomial::from_bytes(bytes, n, q)?;
        if !p.is_ternary(q) {
            return None;
        }
        Some(Self(p))
    }
}

impl Drop for SecretKey {
    fn drop(&mut self) {
        self.0.zeroize();
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub a: Polynomial,
    pub b: Polynomial,
}

impl PublicKey {
    pub fn is_well_formed(&self, n: usize, q: u64) -> bool {
        self.a.coeffs.len() == n
            && self.b.coeffs.len() == n
            && self.a.is_canonical(q)
            && self.b.is_canonical(q)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity((self.a.coeffs.len() + self.b.coeffs.len()) * 8);
        out.extend_from_slice(&self.a.to_bytes());
        out.extend_from_slice(&self.b.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        if bytes.len() != poly_bytes.checked_mul(2)? {
            return None;
        }
        let a = Polynomial::from_bytes(&bytes[..poly_bytes], n, q)?;
        let b = Polynomial::from_bytes(&bytes[poly_bytes..], n, q)?;
        Some(Self { a, b })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinKey {
    pub a_rk: Vec<Polynomial>,
    pub b_rk: Vec<Polynomial>,
    pub base: u64,
    pub l: usize,
}

impl RelinKey {
    pub fn is_well_formed(&self, n: usize, q: u64) -> bool {
        self.base >= 2
            && self.l > 0
            && self.a_rk.len() == self.l
            && self.b_rk.len() == self.l
            && self
                .a_rk
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
            && self
                .b_rk
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.base.to_le_bytes());
        out.extend_from_slice(&(self.l as u64).to_le_bytes());
        for p in &self.a_rk {
            out.extend_from_slice(&p.to_bytes());
        }
        for p in &self.b_rk {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        if bytes.len() < 16 {
            return None;
        }
        let mut arr8 = [0u8; 8];
        arr8.copy_from_slice(&bytes[0..8]);
        let base = u64::from_le_bytes(arr8);
        arr8.copy_from_slice(&bytes[8..16]);
        let l = u64::from_le_bytes(arr8) as usize;
        if base < 2 || l == 0 {
            return None;
        }
        let poly_bytes = n.checked_mul(8)?;
        let total_len = 16usize.checked_add(l.checked_mul(2)?.checked_mul(poly_bytes)?)?;
        if bytes.len() != total_len {
            return None;
        }
        let mut offset = 16;
        let mut a_rk = Vec::with_capacity(l);
        for _ in 0..l {
            a_rk.push(Polynomial::from_bytes(
                &bytes[offset..offset + poly_bytes],
                n,
                q,
            )?);
            offset += poly_bytes;
        }
        let mut b_rk = Vec::with_capacity(l);
        for _ in 0..l {
            b_rk.push(Polynomial::from_bytes(
                &bytes[offset..offset + poly_bytes],
                n,
                q,
            )?);
            offset += poly_bytes;
        }
        Some(Self {
            a_rk,
            b_rk,
            base,
            l,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaloisKey {
    pub g: usize,
    pub a_gk: Vec<Polynomial>,
    pub b_gk: Vec<Polynomial>,
    pub base: u64,
    pub l: usize,
}

impl GaloisKey {
    pub fn is_well_formed(&self, n: usize, q: u64) -> bool {
        self.g % 2 == 1
            && self.base >= 2
            && self.l > 0
            && self.a_gk.len() == self.l
            && self.b_gk.len() == self.l
            && self
                .a_gk
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
            && self
                .b_gk
                .iter()
                .all(|p| p.coeffs.len() == n && p.is_canonical(q))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.g as u64).to_le_bytes());
        out.extend_from_slice(&self.base.to_le_bytes());
        out.extend_from_slice(&(self.l as u64).to_le_bytes());
        for p in &self.a_gk {
            out.extend_from_slice(&p.to_bytes());
        }
        for p in &self.b_gk {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        if bytes.len() < 24 {
            return None;
        }
        let mut arr8 = [0u8; 8];
        arr8.copy_from_slice(&bytes[0..8]);
        let g = u64::from_le_bytes(arr8) as usize;
        arr8.copy_from_slice(&bytes[8..16]);
        let base = u64::from_le_bytes(arr8);
        arr8.copy_from_slice(&bytes[16..24]);
        let l = u64::from_le_bytes(arr8) as usize;
        if g % 2 == 0 || base < 2 || l == 0 {
            return None;
        }
        let poly_bytes = n.checked_mul(8)?;
        let total_len = 24usize.checked_add(l.checked_mul(2)?.checked_mul(poly_bytes)?)?;
        if bytes.len() != total_len {
            return None;
        }
        let mut offset = 24;
        let mut a_gk = Vec::with_capacity(l);
        for _ in 0..l {
            a_gk.push(Polynomial::from_bytes(
                &bytes[offset..offset + poly_bytes],
                n,
                q,
            )?);
            offset += poly_bytes;
        }
        let mut b_gk = Vec::with_capacity(l);
        for _ in 0..l {
            b_gk.push(Polynomial::from_bytes(
                &bytes[offset..offset + poly_bytes],
                n,
                q,
            )?);
            offset += poly_bytes;
        }
        Some(Self {
            g,
            a_gk,
            b_gk,
            base,
            l,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ciphertext {
    pub c0: Polynomial,
    pub c1: Polynomial,
}

impl Ciphertext {
    pub fn is_well_formed(&self, n: usize, q: u64) -> bool {
        self.c0.coeffs.len() == n
            && self.c1.coeffs.len() == n
            && self.c0.is_canonical(q)
            && self.c1.is_canonical(q)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity((self.c0.coeffs.len() + self.c1.coeffs.len()) * 8);
        out.extend_from_slice(&self.c0.to_bytes());
        out.extend_from_slice(&self.c1.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        if bytes.len() != poly_bytes.checked_mul(2)? {
            return None;
        }
        let c0 = Polynomial::from_bytes(&bytes[..poly_bytes], n, q)?;
        let c1 = Polynomial::from_bytes(&bytes[poly_bytes..], n, q)?;
        Some(Self { c0, c1 })
    }
}

pub fn decompose_poly(x: &Polynomial, base: u64, l: usize) -> Vec<Polynomial> {
    let n = x.coeffs.len();
    let mut digits = vec![Polynomial::zero(n); l];

    for i in 0..n {
        let mut val = x.coeffs[i];
        for j in 0..l {
            digits[j].coeffs[i] = val % base;
            val /= base;
        }
    }
    digits
}

pub struct BFVContext {
    pub params: BFVParams,
    pub ntt_table: Option<NTTTable>,
}

impl BFVContext {
    pub fn new(n: usize, q: u64, t: u64) -> Self {
        Self {
            params: BFVParams::new(n, q, t),
            ntt_table: None,
        }
    }

    pub fn new_with_ntt(n: usize, q: u64, t: u64, psi: u64) -> Self {
        let params = BFVParams::new_with_ntt(n, q, t, psi);
        let ntt_table = if n.is_power_of_two() && q < (1u64 << 62) {
            Some(NTTTable::new(n, psi, q))
        } else {
            None
        };
        Self { params, ntt_table }
    }

    #[inline]
    fn poly_mul(&self, a: &Polynomial, b: &Polynomial) -> Polynomial {
        if let Some(ref table) = self.ntt_table {
            table.mul_ntt(a, b)
        } else if let Some(psi) = self.params.psi {
            a.mul_ntt(b, psi, self.params.q)
        } else {
            a.mul_schoolbook(b, self.params.q)
        }
    }

    pub fn encode_plain(&self, pt: &Polynomial) -> Polynomial {
        let mut delta_m = pt.clone();
        for c in delta_m.coeffs.iter_mut() {
            *c = mul_mod(*c, self.params.delta, self.params.q);
        }
        delta_m
    }

    #[cfg(feature = "std")]
    pub fn keygen(&self) -> (SecretKey, PublicKey) {
        let mut rng = rand::thread_rng();
        self.keygen_with_rng(&mut rng)
    }

    pub fn keygen_with_rng<R: Rng>(&self, rng: &mut R) -> (SecretKey, PublicKey) {
        let s = self.gen_small_poly(rng);
        let a = self.gen_uniform_poly(rng);
        let e = self.gen_small_poly(rng);

        let as_mul = self.poly_mul(&a, &s);
        let as_plus_e = as_mul.add(&e, self.params.q);
        let b = Polynomial::zero(self.params.n).sub(&as_plus_e, self.params.q);

        (SecretKey(s), PublicKey { a, b })
    }

    #[cfg(feature = "std")]
    pub fn encrypt(&self, pk: &PublicKey, pt: &Polynomial) -> Ciphertext {
        let mut rng = rand::thread_rng();
        self.encrypt_with_rng(&mut rng, pk, pt)
    }

    pub fn encrypt_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &PublicKey,
        pt: &Polynomial,
    ) -> Ciphertext {
        let u = self.gen_small_poly(rng);
        let e0 = self.gen_small_poly(rng);
        let e1 = self.gen_small_poly(rng);

        let delta_m = self.encode_plain(pt);
        let bu = self.poly_mul(&pk.b, &u);
        let c0 = bu.add(&e0, self.params.q).add(&delta_m, self.params.q);

        let au = self.poly_mul(&pk.a, &u);
        let c1 = au.add(&e1, self.params.q);

        Ciphertext { c0, c1 }
    }

    pub fn phase(&self, sk: &SecretKey, ct: &Ciphertext) -> Polynomial {
        let c1s = self.poly_mul(&ct.c1, &sk.0);
        ct.c0.add(&c1s, self.params.q)
    }

    pub fn noise_poly(&self, sk: &SecretKey, ct: &Ciphertext, pt: &Polynomial) -> Polynomial {
        let v = self.phase(sk, ct);
        let delta_m = self.encode_plain(pt);
        v.sub(&delta_m, self.params.q)
    }

    pub fn noise_norm(&self, sk: &SecretKey, ct: &Ciphertext, pt: &Polynomial) -> u64 {
        self.noise_poly(sk, ct, pt).norm_inf(self.params.q)
    }

    pub fn noise_budget_bits(&self, sk: &SecretKey, ct: &Ciphertext, pt: &Polynomial) -> u32 {
        let e_norm = self.noise_norm(sk, ct, pt);
        if self.params.delta <= 1 || 2 * e_norm >= self.params.delta {
            return 0;
        }
        if e_norm == 0 {
            return (self.params.delta - 1).ilog2();
        }
        ((self.params.delta - 1) / (2 * e_norm)).ilog2()
    }

    pub fn modulus_switch(&self, ct: &Ciphertext, q_new: u64) -> Ciphertext {
        assert!(
            q_new > self.params.t,
            "Target modulus q_new must be > plaintext modulus t"
        );
        let q = self.params.q;
        let scale_poly = |p: &Polynomial| -> Polynomial {
            let mut coeffs = Vec::with_capacity(self.params.n);
            let q128 = q as i128;
            let q_new128 = q_new as i128;
            for &c in &p.coeffs {
                let lifted = crate::lwe::math::centered_lift(c, q) as i128;
                let rounded = if lifted >= 0 {
                    (lifted * q_new128 + q128 / 2) / q128
                } else {
                    -((-lifted * q_new128 + q128 / 2) / q128)
                };
                let mut rem = rounded % q_new128;
                if rem < 0 {
                    rem += q_new128;
                }
                coeffs.push(rem as u64);
            }
            Polynomial::new(coeffs)
        };
        Ciphertext {
            c0: scale_poly(&ct.c0),
            c1: scale_poly(&ct.c1),
        }
    }

    pub fn decrypt(&self, sk: &SecretKey, ct: &Ciphertext) -> Polynomial {
        let c0_plus_c1s = self.phase(sk, ct);

        let mut m = Polynomial::zero(self.params.n);
        let t = self.params.t as u128;
        let q = self.params.q as u128;
        for i in 0..self.params.n {
            let val = c0_plus_c1s.coeffs[i] as u128;
            let decoded = ((val * t + q / 2) / q) % t;
            m.coeffs[i] = decoded as u64;
        }
        m
    }

    pub fn add(&self, ct1: &Ciphertext, ct2: &Ciphertext) -> Ciphertext {
        Ciphertext {
            c0: ct1.c0.add(&ct2.c0, self.params.q),
            c1: ct1.c1.add(&ct2.c1, self.params.q),
        }
    }

    pub fn sub(&self, ct1: &Ciphertext, ct2: &Ciphertext) -> Ciphertext {
        Ciphertext {
            c0: ct1.c0.sub(&ct2.c0, self.params.q),
            c1: ct1.c1.sub(&ct2.c1, self.params.q),
        }
    }

    pub fn add_plain(&self, ct: &Ciphertext, pt: &Polynomial) -> Ciphertext {
        let delta_m = self.encode_plain(pt);
        Ciphertext {
            c0: ct.c0.add(&delta_m, self.params.q),
            c1: ct.c1.clone(),
        }
    }

    pub fn sub_plain(&self, ct: &Ciphertext, pt: &Polynomial) -> Ciphertext {
        let delta_m = self.encode_plain(pt);
        Ciphertext {
            c0: ct.c0.sub(&delta_m, self.params.q),
            c1: ct.c1.clone(),
        }
    }

    pub fn mul_plain(&self, ct: &Ciphertext, pt: &Polynomial) -> Ciphertext {
        Ciphertext {
            c0: self.poly_mul(&ct.c0, pt),
            c1: self.poly_mul(&ct.c1, pt),
        }
    }

    #[cfg(feature = "std")]
    pub fn keygen_relin(&self, sk: &SecretKey, base: u64, l: usize) -> RelinKey {
        let mut rng = rand::thread_rng();
        self.keygen_relin_with_rng(&mut rng, sk, base, l)
    }

    pub fn keygen_relin_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        sk: &SecretKey,
        base: u64,
        l: usize,
    ) -> RelinKey {
        let mut a_rk = Vec::with_capacity(l);
        let mut b_rk = Vec::with_capacity(l);

        let s2 = self.poly_mul(&sk.0, &sk.0);

        let mut current_g = 1u64;
        for _ in 0..l {
            let a = self.gen_uniform_poly(rng);
            let e = self.gen_small_poly(rng);

            let as_plus_e = self.poly_mul(&a, &sk.0).add(&e, self.params.q);

            let mut g_s2 = s2.clone();
            for c in g_s2.coeffs.iter_mut() {
                *c = mul_mod(*c, current_g, self.params.q);
            }

            let mut b = Polynomial::zero(self.params.n).sub(&as_plus_e, self.params.q);
            b = b.add(&g_s2, self.params.q);

            a_rk.push(a);
            b_rk.push(b);

            current_g = mul_mod(current_g, base, self.params.q);
        }
        RelinKey {
            a_rk,
            b_rk,
            base,
            l,
        }
    }

    pub fn mul(&self, ct1: &Ciphertext, ct2: &Ciphertext, rk: &RelinKey) -> Ciphertext {
        let d0_unred = ct1.c0.mul_schoolbook_unreduced(&ct2.c0);

        let c0c1 = ct1.c0.mul_schoolbook_unreduced(&ct2.c1);
        let c1c0 = ct1.c1.mul_schoolbook_unreduced(&ct2.c0);
        let mut d1_unred = vec![0i128; self.params.n];
        for i in 0..self.params.n {
            d1_unred[i] = c0c1[i] + c1c0[i];
        }

        let d2_unred = ct1.c1.mul_schoolbook_unreduced(&ct2.c1);

        let t = self.params.t as i128;
        let q = self.params.q as i128;
        let scale = |unreduced: &[i128]| -> Polynomial {
            let mut scaled = vec![0u64; self.params.n];
            for i in 0..self.params.n {
                let val = unreduced[i];
                let abs_val = val.unsigned_abs() as i128;
                let quot = (abs_val / q) % q;
                let rem = abs_val % q;
                let abs_rounded = (quot * (t % q) + (rem * t + q / 2) / q) % q;
                let div = if val >= 0 || abs_rounded == 0 {
                    abs_rounded
                } else {
                    q - abs_rounded
                };
                scaled[i] = div as u64;
            }
            Polynomial::new(scaled)
        };

        let d0 = scale(&d0_unred);
        let d1 = scale(&d1_unred);
        let d2 = scale(&d2_unred);

        let d2_dec = decompose_poly(&d2, rk.base, rk.l);
        let mut sum_a = Polynomial::zero(self.params.n);
        let mut sum_b = Polynomial::zero(self.params.n);

        for i in 0..rk.l {
            sum_a = sum_a.add(&self.poly_mul(&d2_dec[i], &rk.a_rk[i]), self.params.q);
            sum_b = sum_b.add(&self.poly_mul(&d2_dec[i], &rk.b_rk[i]), self.params.q);
        }

        let c0 = d0.add(&sum_b, self.params.q);
        let c1 = d1.add(&sum_a, self.params.q);

        Ciphertext { c0, c1 }
    }

    #[cfg(feature = "std")]
    pub fn keygen_galois(&self, sk: &SecretKey, g: usize, base: u64, l: usize) -> GaloisKey {
        let mut rng = rand::thread_rng();
        self.keygen_galois_with_rng(&mut rng, sk, g, base, l)
    }

    pub fn keygen_galois_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        sk: &SecretKey,
        g: usize,
        base: u64,
        l: usize,
    ) -> GaloisKey {
        assert!(g % 2 == 1, "Galois exponent g must be odd");
        let mut a_gk = Vec::with_capacity(l);
        let mut b_gk = Vec::with_capacity(l);

        let s_galois = sk.0.apply_galois(g, self.params.q);

        let mut current_g = 1u64;
        for _ in 0..l {
            let a = self.gen_uniform_poly(rng);
            let e = self.gen_small_poly(rng);

            let as_plus_e = self.poly_mul(&a, &sk.0).add(&e, self.params.q);

            let mut g_sg = s_galois.clone();
            for c in g_sg.coeffs.iter_mut() {
                *c = mul_mod(*c, current_g, self.params.q);
            }

            let mut b = Polynomial::zero(self.params.n).sub(&as_plus_e, self.params.q);
            b = b.add(&g_sg, self.params.q);

            a_gk.push(a);
            b_gk.push(b);

            current_g = mul_mod(current_g, base, self.params.q);
        }

        GaloisKey {
            g,
            a_gk,
            b_gk,
            base,
            l,
        }
    }

    pub fn apply_galois(&self, ct: &Ciphertext, gk: &GaloisKey) -> Ciphertext {
        let c0_g = ct.c0.apply_galois(gk.g, self.params.q);
        let c1_g = ct.c1.apply_galois(gk.g, self.params.q);

        let c1_dec = decompose_poly(&c1_g, gk.base, gk.l);
        let mut sum_a = Polynomial::zero(self.params.n);
        let mut sum_b = Polynomial::zero(self.params.n);

        for i in 0..gk.l {
            sum_a = sum_a.add(&self.poly_mul(&c1_dec[i], &gk.a_gk[i]), self.params.q);
            sum_b = sum_b.add(&self.poly_mul(&c1_dec[i], &gk.b_gk[i]), self.params.q);
        }

        let c0 = c0_g.add(&sum_b, self.params.q);
        let c1 = sum_a;

        Ciphertext { c0, c1 }
    }

    fn gen_uniform_poly<R: Rng>(&self, rng: &mut R) -> Polynomial {
        let mut coeffs = Vec::with_capacity(self.params.n);
        for _ in 0..self.params.n {
            coeffs.push(rng.gen_range(0..self.params.q));
        }
        Polynomial::new(coeffs)
    }

    fn gen_small_poly<R: Rng>(&self, rng: &mut R) -> Polynomial {
        let q = self.params.q;
        let mut coeffs = Vec::with_capacity(self.params.n);
        for _ in 0..self.params.n {
            let val = match rng.gen_range(0..3) {
                0 => 0,
                1 => 1,
                _ => q - 1,
            };
            coeffs.push(val);
        }
        Polynomial::new(coeffs)
    }
}

#[derive(Debug, Clone)]
pub struct BFVBatchEncoder {
    pub n: usize,
    pub t: u64,
    pub psi_t: u64,
    pub table: NTTTable,
}

impl BFVBatchEncoder {
    pub fn new(n: usize, t: u64, psi_t: u64) -> Self {
        let table = NTTTable::new(n, psi_t, t);
        Self { n, t, psi_t, table }
    }

    pub fn encode_simd(&self, slots: &[u64]) -> Polynomial {
        assert_eq!(slots.len(), self.n, "SIMD slot vector must have length N");
        let canonical: Vec<u64> = slots.iter().map(|&x| x % self.t).collect();
        self.table.inverse(&canonical)
    }

    pub fn decode_simd(&self, pt: &Polynomial) -> Vec<u64> {
        assert_eq!(
            pt.coeffs.len(),
            self.n,
            "Plaintext polynomial must have degree N"
        );
        self.table.forward(pt)
    }

    pub fn permute_slots(&self, slots: &[u64], g: usize) -> Vec<u64> {
        assert_eq!(slots.len(), self.n, "SIMD slot vector must have length N");
        assert!(g % 2 == 1, "Galois exponent g must be odd");
        let two_n = 2 * self.n;
        (0..self.n)
            .map(|i| {
                let odd_power = ((2 * i + 1) * g) % two_n;
                slots[(odd_power - 1) / 2] % self.t
            })
            .collect()
    }
}
