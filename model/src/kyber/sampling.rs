use crate::kyber::ntt::KYBER_Q;
use crate::kyber::poly::Poly;

pub fn parse_ntt(stream: &[u8]) -> Poly {
    let mut poly = Poly::new();
    let mut i = 0;
    let mut j = 0;
    while j < 256 && i + 3 <= stream.len() {
        let b1 = stream[i] as u32;
        let b2 = stream[i + 1] as u32;
        let b3 = stream[i + 2] as u32;
        i += 3;

        let d1 = (b1 | ((b2 & 0x0F) << 8)) as i16;
        let d2 = ((b2 >> 4) | (b3 << 4)) as i16;

        if d1 < KYBER_Q {
            poly.coeffs[j] = d1;
            j += 1;
        }
        if d2 < KYBER_Q && j < 256 {
            poly.coeffs[j] = d2;
            j += 1;
        }
    }
    poly
}

pub fn sample_cbd(stream: &[u8], eta: usize) -> Poly {
    let mut poly = Poly::new();
    if eta == 2 {
        for i in 0..128 {
            let b = stream[i];
            let a_0 = (b & 0x01) + ((b >> 1) & 0x01);
            let b_0 = ((b >> 2) & 0x01) + ((b >> 3) & 0x01);
            let a_1 = ((b >> 4) & 0x01) + ((b >> 5) & 0x01);
            let b_1 = ((b >> 6) & 0x01) + ((b >> 7) & 0x01);

            poly.coeffs[2 * i] = (a_0 as i16) - (b_0 as i16);
            poly.coeffs[2 * i + 1] = (a_1 as i16) - (b_1 as i16);
        }
    } else if eta == 3 {
        for i in 0..64 {
            let b0 = stream[3 * i] as u32;
            let b1 = stream[3 * i + 1] as u32;
            let b2 = stream[3 * i + 2] as u32;
            let b = b0 | (b1 << 8) | (b2 << 16);

            for j in 0..4 {
                let a = ((b >> (6 * j)) & 0x07).count_ones();
                let c = ((b >> (6 * j + 3)) & 0x07).count_ones();
                poly.coeffs[4 * i + j] = (a as i16) - (c as i16);
            }
        }
    }
    poly
}
