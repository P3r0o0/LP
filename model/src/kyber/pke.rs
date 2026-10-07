use crate::kyber::encode::{decode, encode};
use crate::kyber::gen::{expand_a, expand_encrypt_errors, expand_s_and_e};
use crate::kyber::poly::{poly_basemul_montgomery, Poly};
use crate::kyber::sym::g;

#[derive(Clone)]
pub struct PkeParams {
    pub k: usize,
    pub eta1: usize,
    pub eta2: usize,
    pub du: u8,
    pub dv: u8,
}

pub const ML_KEM_512: PkeParams = PkeParams {
    k: 2,
    eta1: 3,
    eta2: 2,
    du: 10,
    dv: 4,
};
pub const ML_KEM_768: PkeParams = PkeParams {
    k: 3,
    eta1: 2,
    eta2: 2,
    du: 10,
    dv: 4,
};
pub const ML_KEM_1024: PkeParams = PkeParams {
    k: 4,
    eta1: 2,
    eta2: 2,
    du: 11,
    dv: 5,
};

pub fn keygen(params: &PkeParams, d: &[u8; 32], ek_out: &mut [u8], dk_out: &mut [u8]) {
    let mut d_k = d.to_vec();
    d_k.push(params.k as u8);
    let g_out = g(&d_k);

    let mut rho = [0u8; 32];
    let mut sigma = [0u8; 32];
    rho.copy_from_slice(&g_out[0..32]);
    sigma.copy_from_slice(&g_out[32..64]);

    let mut a_hat = [[Poly::new(); 4]; 4];
    expand_a(&rho, params.k, &mut a_hat);
    
    let mut s = [Poly::new(); 4];
    let mut e = [Poly::new(); 4];
    expand_s_and_e(&sigma, params.k, params.eta1, &mut s, &mut e);

    for i in 0..params.k {
        s[i].ntt();
        e[i].ntt();
    }

    let mut t_hat = [Poly::new(); 4];
    for i in 0..params.k {
        for j in 0..params.k {
            let mut prod = Poly::new();
            poly_basemul_montgomery(&mut prod, &a_hat[i][j], &s[j]);
            t_hat[i].add(&prod);
        }
        crate::kyber::ntt::tomont(&mut t_hat[i].coeffs);
        t_hat[i].add(&e[i]);
        t_hat[i].reduce();
    }

    let mut ek_offset = 0;
    for i in 0..params.k {
        let enc_len = 256 * 12 / 8;
        encode(&t_hat[i], 12, &mut ek_out[ek_offset..ek_offset + enc_len]);
        ek_offset += enc_len;
    }
    ek_out[ek_offset..ek_offset + 32].copy_from_slice(&rho);

    let mut dk_offset = 0;
    for i in 0..params.k {
        let enc_len = 256 * 12 / 8;
        encode(&s[i], 12, &mut dk_out[dk_offset..dk_offset + enc_len]);
        dk_offset += enc_len;
    }
}

pub fn encrypt(params: &PkeParams, ek: &[u8], m: &[u8], r_seed: &[u8; 32], c_out: &mut [u8]) {
    let mut t_hat = [Poly::new(); 4];
    let offset = params.k * 384;
    for i in 0..params.k {
        t_hat[i] = decode(&ek[i * 384..(i + 1) * 384], 12);
    }
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&ek[offset..offset + 32]);

    let mut a_hat = [[Poly::new(); 4]; 4];
    expand_a(&rho, params.k, &mut a_hat);
    
    let mut r = [Poly::new(); 4];
    let mut e1 = [Poly::new(); 4];
    let mut e2 = Poly::new();
    expand_encrypt_errors(r_seed, params.k, params.eta1, params.eta2, &mut r, &mut e1, &mut e2);

    for i in 0..params.k {
        r[i].ntt();
    }

    let mut u = [Poly::new(); 4];
    for i in 0..params.k {
        for j in 0..params.k {
            let mut prod = Poly::new();

            poly_basemul_montgomery(&mut prod, &a_hat[j][i], &r[j]);
            u[i].add(&prod);
        }
        u[i].intt();
        u[i].add(&e1[i]);
        u[i].reduce();
    }

    let mut v = Poly::new();
    for i in 0..params.k {
        let mut prod = Poly::new();
        poly_basemul_montgomery(&mut prod, &t_hat[i], &r[i]);
        v.add(&prod);
    }
    v.intt();
    v.add(&e2);

    let m_poly = decode(m, 1);
    v.add(&m_poly);
    v.reduce();

    let mut c_offset = 0;
    let enc_len_du = 256 * (params.du as usize) / 8;
    for i in 0..params.k {
        encode(&u[i], params.du, &mut c_out[c_offset..c_offset + enc_len_du]);
        c_offset += enc_len_du;
    }
    let enc_len_dv = 256 * (params.dv as usize) / 8;
    encode(&v, params.dv, &mut c_out[c_offset..c_offset + enc_len_dv]);
}

pub fn decrypt(params: &PkeParams, dk: &[u8], c: &[u8], m_out: &mut [u8]) {
    let mut u = [Poly::new(); 4];
    let du_bytes = 256 * (params.du as usize) / 8;
    for i in 0..params.k {
        u[i] = decode(&c[i * du_bytes..(i + 1) * du_bytes], params.du);
        u[i].ntt();
    }

    let mut v = decode(&c[params.k * du_bytes..], params.dv);

    let mut s_hat = [Poly::new(); 4];
    for i in 0..params.k {
        s_hat[i] = decode(&dk[i * 384..(i + 1) * 384], 12);
    }

    let mut m_poly = Poly::new();
    for i in 0..params.k {
        let mut prod = Poly::new();
        poly_basemul_montgomery(&mut prod, &s_hat[i], &u[i]);
        m_poly.add(&prod);
    }
    m_poly.intt();
    for i in 0..256 {
        v.coeffs[i] = v.coeffs[i] - m_poly.coeffs[i];
    }
    v.reduce();

    encode(&v, 1, m_out);
}
