use crate::kyber::ntt::KYBER_Q;

pub fn compress(x: i16, d: u8) -> u32 {
    let mut x = x % KYBER_Q;
    if x < 0 {
        x += KYBER_Q;
    }
    let x = x as u32;
    let mut shifted = x << d;
    shifted += (KYBER_Q as u32) / 2;
    let res = shifted / (KYBER_Q as u32);
    res & ((1 << d) - 1)
}

pub fn decompress(x: u32, d: u8) -> i16 {
    let mut shifted = x * (KYBER_Q as u32);
    shifted += 1 << (d - 1);
    let res = shifted >> d;
    (res as i16) % KYBER_Q
}
