use crate::kyber::poly::Poly;
use crate::kyber::sampling::{parse_ntt, sample_cbd};
use crate::kyber::sym::{prf, xof};

pub fn expand_a(rho: &[u8; 32], k: usize, a_hat: &mut [[Poly; 4]; 4]) {
    let mut stream = [0u8; 840];
    for i in 0..k {
        for j in 0..k {
            xof(rho, j as u8, i as u8, &mut stream);
            let poly = parse_ntt(&stream);
            a_hat[i][j] = poly;
        }
    }
}

pub fn expand_s_and_e(sigma: &[u8; 32], k: usize, eta1: usize, s: &mut [Poly; 4], e: &mut [Poly; 4]) {
    let mut nonce = 0;

    let mut stream = [0u8; 192];
    
    let l = if eta1 == 2 { 128 } else { 192 };

    for i in 0..k {
        prf(sigma, nonce, &mut stream[0..l]);
        s[i] = sample_cbd(&stream[0..l], eta1);
        nonce += 1;
    }
    for i in 0..k {
        prf(sigma, nonce, &mut stream[0..l]);
        e[i] = sample_cbd(&stream[0..l], eta1);
        nonce += 1;
    }
}

pub fn expand_encrypt_errors(
    rho_prime: &[u8; 32],
    k: usize,
    eta1: usize,
    eta2: usize,
    r: &mut [Poly; 4],
    e1: &mut [Poly; 4],
    e2: &mut Poly,
) {
    let mut nonce = 0;

    let mut stream1 = [0u8; 128];
    let mut stream2 = [0u8; 192];

    let l1 = if eta1 == 2 { 128 } else { 192 };
    let l2 = if eta2 == 2 { 128 } else { 192 };

    for i in 0..k {
        prf(rho_prime, nonce, &mut stream2[0..l1]);
        r[i] = sample_cbd(&stream2[0..l1], eta1);
        nonce += 1;
    }
    for i in 0..k {
        prf(rho_prime, nonce, &mut stream2[0..l2]);
        e1[i] = sample_cbd(&stream2[0..l2], eta2);
        nonce += 1;
    }
    prf(rho_prime, nonce, &mut stream2[0..l2]);
    *e2 = sample_cbd(&stream2[0..l2], eta2);
}
