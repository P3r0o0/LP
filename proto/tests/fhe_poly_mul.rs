use lwe_rust::lwe::poly::Polynomial;
use rand::Rng;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyRingSample {
    pub a: Polynomial,
    pub b: Polynomial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyRingSample2 {
    pub d0: Polynomial,
    pub d1: Polynomial,
    pub d2: Polynomial,
}

impl PolyRingSample {
    pub fn new(a: Polynomial, s: &Polynomial, e: &Polynomial, q: u64) -> Self {
        let as_mul = a.mul_schoolbook(s, q);
        let b = as_mul.add(e, q);
        Self { a, b }
    }

    pub fn multiply(&self, other: &Self, q: u64) -> PolyRingSample2 {
        let d0 = self.b.mul_schoolbook(&other.b, q);
        let a1b2 = self.a.mul_schoolbook(&other.b, q);
        let a2b1 = other.a.mul_schoolbook(&self.b, q);
        let d1 = a1b2.add(&a2b1, q);
        let d2 = self.a.mul_schoolbook(&other.a, q);
        PolyRingSample2 { d0, d1, d2 }
    }
}

#[derive(Debug, Clone)]
pub struct PolyGadgetRelinKey {
    pub a_rk: Vec<Polynomial>,
    pub b_rk: Vec<Polynomial>,
}

impl PolyGadgetRelinKey {
    pub fn new(
        a_rk: &[Polynomial],
        s: &Polynomial,
        e_rk: &[Polynomial],
        g: &[u64],
        q: u64,
    ) -> Self {
        let l = g.len();
        let mut b_rk = Vec::with_capacity(l);
        let s2 = s.mul_schoolbook(s, q);
        for i in 0..l {
            let as_mul = a_rk[i].mul_schoolbook(s, q);
            let mut val = as_mul.add(&e_rk[i], q);

            let mut g_s2 = s2.clone();
            for c in g_s2.coeffs.iter_mut() {
                *c = (*c * g[i]) % q;
            }
            val = val.add(&g_s2, q);
            b_rk.push(val);
        }
        Self {
            a_rk: a_rk.to_vec(),
            b_rk,
        }
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

impl PolyRingSample2 {
    pub fn gadget_relinearize(
        &self,
        rk: &PolyGadgetRelinKey,
        base: u64,
        l: usize,
        q: u64,
    ) -> PolyRingSample {
        let d2_dec = decompose_poly(&self.d2, base, l);
        let n = self.d0.coeffs.len();

        let mut sum_a = Polynomial::zero(n);
        let mut sum_b = Polynomial::zero(n);

        for i in 0..l {
            sum_a = sum_a.add(&d2_dec[i].mul_schoolbook(&rk.a_rk[i], q), q);
            sum_b = sum_b.add(&d2_dec[i].mul_schoolbook(&rk.b_rk[i], q), q);
        }

        let a = self.d1.add(&sum_a, q);
        let b = self.d0.add(&sum_b, q);
        PolyRingSample { a, b }
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

pub fn poly_norm_inf(p: &Polynomial, q: u64) -> u64 {
    p.coeffs
        .iter()
        .map(|&x| centered_lift(x, q).abs() as u64)
        .max()
        .unwrap_or(0)
}

#[test]
fn test_poly_homomorphic_multiplication() {
    let mut rng = rand::thread_rng();
    let q = 3329;
    let n = 16;

    let gen_poly = |rng: &mut rand::rngs::ThreadRng, bound: u64| -> Polynomial {
        let mut coeffs = Vec::with_capacity(n);
        for _ in 0..n {
            coeffs.push(rng.gen_range(0..bound));
        }
        Polynomial::new(coeffs)
    };

    let s = gen_poly(&mut rng, 2);
    let e1 = gen_poly(&mut rng, 2);
    let e2 = gen_poly(&mut rng, 2);

    let a1 = gen_poly(&mut rng, q);
    let a2 = gen_poly(&mut rng, q);

    let c1 = PolyRingSample::new(a1, &s, &e1, q);
    let c2 = PolyRingSample::new(a2, &s, &e2, q);

    let c_mul = c1.multiply(&c2, q);

    let expected_noise = e1.mul_schoolbook(&e2, q);

    let base = 8;
    let l = 4;
    let g = vec![1, 8, 64, 512];

    let mut a_rk_gadget = Vec::with_capacity(l);
    let mut e_rk_gadget = Vec::with_capacity(l);
    for _ in 0..l {
        a_rk_gadget.push(gen_poly(&mut rng, q));
        e_rk_gadget.push(gen_poly(&mut rng, 2));
    }
    let gadget_rk = PolyGadgetRelinKey::new(&a_rk_gadget, &s, &e_rk_gadget, &g, q);

    let c_relin_gadget = c_mul.gadget_relinearize(&gadget_rk, base, l, q);

    let as_mul_relin = c_relin_gadget.a.mul_schoolbook(&s, q);
    let eval_relin_gadget = c_relin_gadget.b.sub(&as_mul_relin, q);

    let d2_dec = decompose_poly(&c_mul.d2, base, l);
    let mut expected_noise_gadget = expected_noise.clone();
    for i in 0..l {
        let dec_rk_mul = d2_dec[i].mul_schoolbook(&e_rk_gadget[i], q);
        expected_noise_gadget = expected_noise_gadget.add(&dec_rk_mul, q);
    }

    assert_eq!(
        eval_relin_gadget.coeffs, expected_noise_gadget.coeffs,
        "Poly Gadget Relin Failed"
    );

    let norm_eval_relin = poly_norm_inf(&eval_relin_gadget, q);
    println!(
        "Poly Norm after GADGET relinearization: {}",
        norm_eval_relin
    );
}
