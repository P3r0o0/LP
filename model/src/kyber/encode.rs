use crate::kyber::compress::{compress, decompress};
use crate::kyber::poly::Poly;

pub fn encode(poly: &Poly, bits: u8, out: &mut [u8]) {
    let mut bit_idx = 0;

    for i in 0..256 {
        let val = if bits == 12 {
            let mut c = poly.coeffs[i] % (crate::kyber::ntt::KYBER_Q as i16);
            if c < 0 {
                c += crate::kyber::ntt::KYBER_Q as i16;
            }
            c as u32
        } else {
            compress(poly.coeffs[i], bits)
        };

        for j in 0..bits {
            let bit = (val >> j) & 1;
            out[bit_idx / 8] |= (bit as u8) << (bit_idx % 8);
            bit_idx += 1;
        }
    }
}

pub fn decode(bytes: &[u8], bits: u8) -> Poly {
    let mut poly = Poly::new();
    let mut bit_idx = 0;

    for i in 0..256 {
        let mut val = 0u32;
        for j in 0..bits {
            let bit = (bytes[bit_idx / 8] >> (bit_idx % 8)) & 1;
            val |= (bit as u32) << j;
            bit_idx += 1;
        }

        poly.coeffs[i] = if bits == 12 {
            val as i16
        } else {
            decompress(val, bits)
        };
    }
    poly
}
