use crate::kyber::ntt::{barrett_reduce, intt, montgomery_reduce, ntt, KYBER_N};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Poly {
    pub coeffs: [i16; KYBER_N],
}

impl Poly {
    pub fn new() -> Self {
        Self {
            coeffs: [0; KYBER_N],
        }
    }

    pub fn ntt(&mut self) {
        ntt(&mut self.coeffs);
    }

    pub fn intt(&mut self) {
        intt(&mut self.coeffs);
    }

    pub fn add(&mut self, other: &Poly) {
        for i in 0..KYBER_N {
            self.coeffs[i] = self.coeffs[i] + other.coeffs[i];
        }
    }

    pub fn reduce(&mut self) {
        for i in 0..KYBER_N {
            self.coeffs[i] = barrett_reduce(self.coeffs[i]);
        }
    }
}

pub fn poly_basemul_montgomery(c: &mut Poly, a: &Poly, b: &Poly) {
    for i in 0..(KYBER_N / 4) {
        let (rx, ry) = basemul(
            a.coeffs[4 * i],
            a.coeffs[4 * i + 1],
            b.coeffs[4 * i],
            b.coeffs[4 * i + 1],
            crate::kyber::ntt::ZETAS[64 + i],
        );
        c.coeffs[4 * i] = rx;
        c.coeffs[4 * i + 1] = ry;

        let (rx, ry) = basemul(
            a.coeffs[4 * i + 2],
            a.coeffs[4 * i + 3],
            b.coeffs[4 * i + 2],
            b.coeffs[4 * i + 3],
            -crate::kyber::ntt::ZETAS[64 + i],
        );
        c.coeffs[4 * i + 2] = rx;
        c.coeffs[4 * i + 3] = ry;
    }
}

fn basemul(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16) -> (i16, i16) {
    let r0 = montgomery_reduce((a1 as i32) * (b1 as i32));
    let r0 = montgomery_reduce((r0 as i32) * (zeta as i32));
    let r0 = r0 + montgomery_reduce((a0 as i32) * (b0 as i32));

    let r1 = montgomery_reduce((a0 as i32) * (b1 as i32));
    let r1 = r1 + montgomery_reduce((a1 as i32) * (b0 as i32));

    (r0, r1)
}
