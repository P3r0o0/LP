use rand::Rng;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RingSample {
    pub a: u64,
    pub b: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RingSample2 {
    pub d0: u64,
    pub d1: u64,
    pub d2: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelinKey {
    pub a_rk: u64,
    pub b_rk: u64,
}

impl RelinKey {
    pub fn new(a_rk: u64, s: u64, e_rk: u64, q: u64) -> Self {
        let s2 = (s * s) % q;
        let b_rk = (a_rk * s + e_rk + s2) % q;
        Self { a_rk, b_rk }
    }
}

impl RingSample2 {
    pub fn relinearize(&self, rk: &RelinKey, q: u64) -> RingSample {
        let a = (self.d1 + self.d2 * rk.a_rk) % q;
        let b = (self.d0 + self.d2 * rk.b_rk) % q;
        RingSample { a, b }
    }

    pub fn gadget_relinearize(
        &self,
        rk: &GadgetRelinKey,
        base: u64,
        l: usize,
        q: u64,
    ) -> RingSample {
        let d2_dec = decompose(self.d2, base, l);
        let mut sum_a = 0u64;
        let mut sum_b = 0u64;

        for i in 0..l {
            sum_a = (sum_a + d2_dec[i] * rk.a_rk[i]) % q;
            sum_b = (sum_b + d2_dec[i] * rk.b_rk[i]) % q;
        }

        let a = (self.d1 + sum_a) % q;
        let b = (self.d0 + sum_b) % q;
        RingSample { a, b }
    }
}

#[derive(Debug, Clone)]
pub struct GadgetRelinKey {
    pub a_rk: Vec<u64>,
    pub b_rk: Vec<u64>,
}

impl GadgetRelinKey {
    pub fn new(a_rk: &[u64], s: u64, e_rk: &[u64], g: &[u64], q: u64) -> Self {
        let l = g.len();
        let mut b_rk = Vec::with_capacity(l);
        let s2 = (s * s) % q;
        for i in 0..l {
            let mut val = (a_rk[i] * s) % q;
            val = (val + e_rk[i]) % q;
            val = (val + g[i] * s2) % q;
            b_rk.push(val);
        }
        Self {
            a_rk: a_rk.to_vec(),
            b_rk,
        }
    }
}

pub fn decompose(mut x: u64, base: u64, l: usize) -> Vec<u64> {
    let mut digits = Vec::with_capacity(l);
    for _ in 0..l {
        digits.push(x % base);
        x /= base;
    }
    digits
}

impl RingSample {
    pub fn new(a: u64, s: u64, e: u64, q: u64) -> Self {
        let b = (a * s + e) % q;
        Self { a, b }
    }

    pub fn multiply(&self, other: &Self, q: u64) -> RingSample2 {
        let d0 = (self.b * other.b) % q;
        let d1 = (self.a * other.b + other.a * self.b) % q;
        let d2 = (self.a * other.a) % q;
        RingSample2 { d0, d1, d2 }
    }
}

pub fn centered_lift(x: u64, q: u64) -> i64 {
    let x = x % q;
    let half_q = q / 2;
    if x <= half_q {
        x as i64
    } else {
        (x as i64) - (q as i64)
    }
}

#[test]
fn test_ring_homomorphic_multiplication() {
    let mut rng = rand::thread_rng();
    let q = 3329;

    let s = rng.gen_range(0..2);
    let e1 = 2;
    let e2 = 3;

    let a1 = rng.gen_range(0..q);
    let a2 = rng.gen_range(0..q);

    let c1 = RingSample::new(a1, s, e1, q);
    let c2 = RingSample::new(a2, s, e2, q);

    let c_mul = c1.multiply(&c2, q);

    let s2 = (s * s) % q;
    let eval_d1 = (c_mul.d1 * s) % q;
    let eval_d2 = (c_mul.d2 * s2) % q;

    let mut eval = (c_mul.d0 + eval_d2) % q;
    eval = (eval + q - eval_d1) % q;

    let expected_noise = (e1 * e2) % q;

    assert_eq!(eval, expected_noise, "Multiplication Completeness Failed!");

    let norm_e1 = centered_lift(e1, q).abs();
    let norm_e2 = centered_lift(e2, q).abs();
    let norm_eval = centered_lift(eval, q).abs();

    println!(
        "Norm e1: {}, Norm e2: {}, Norm after multiplication: {}",
        norm_e1, norm_e2, norm_eval
    );
    assert_eq!(norm_eval, norm_e1 * norm_e2, "Noise multiplied as expected");

    let e_rk = 1;
    let a_rk = rng.gen_range(0..q);
    let rk = RelinKey::new(a_rk, s, e_rk, q);

    let c_relin = c_mul.relinearize(&rk, q);

    let eval_relin = (c_relin.b + q - (c_relin.a * s) % q) % q;

    let expected_noise_relin = (expected_noise + (c_mul.d2 * e_rk) % q) % q;

    assert_eq!(
        eval_relin, expected_noise_relin,
        "Relinearization Completeness Failed!"
    );

    let norm_eval_relin = centered_lift(eval_relin, q).abs();
    println!(
        "Norm after STANDARD relinearization (Explosion!): {}",
        norm_eval_relin
    );

    let base = 8;
    let l = 4;
    let g = vec![1, 8, 64, 512];

    let mut a_rk_gadget = vec![0; l];
    let mut e_rk_gadget = vec![0; l];
    for i in 0..l {
        a_rk_gadget[i] = rng.gen_range(0..q);
        e_rk_gadget[i] = 1;
    }
    let gadget_rk = GadgetRelinKey::new(&a_rk_gadget, s, &e_rk_gadget, &g, q);

    let c_relin_gadget = c_mul.gadget_relinearize(&gadget_rk, base, l, q);

    let eval_relin_gadget = (c_relin_gadget.b + q - (c_relin_gadget.a * s) % q) % q;

    let d2_dec = decompose(c_mul.d2, base, l);
    let mut expected_noise_gadget = expected_noise;
    for i in 0..l {
        expected_noise_gadget = (expected_noise_gadget + d2_dec[i] * e_rk_gadget[i]) % q;
    }

    assert_eq!(
        eval_relin_gadget, expected_noise_gadget,
        "Gadget Relinearization Completeness Failed!"
    );

    let norm_eval_relin_gadget = centered_lift(eval_relin_gadget, q).abs();
    println!(
        "Norm after GADGET relinearization (Controlled!): {}",
        norm_eval_relin_gadget
    );

    assert!(
        norm_eval_relin_gadget < 100,
        "Gadget noise should be well controlled"
    );
}
