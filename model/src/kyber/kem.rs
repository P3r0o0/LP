use crate::kyber::pke::{
    decrypt as pke_decrypt, encrypt as pke_encrypt, keygen as pke_keygen, PkeParams,
};
use crate::kyber::sym::{g, h};
use zeroize::{Zeroize, ZeroizeOnDrop};
use rand_core::CryptoRngCore;

#[derive(Clone, PartialEq, Eq)]
pub struct EncapsulationKey<const EK_LEN: usize>(pub [u8; EK_LEN]);

#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct DecapsulationKey<const DK_LEN: usize>(pub [u8; DK_LEN]);

#[derive(Clone, PartialEq, Eq)]
pub struct Ciphertext<const C_LEN: usize>(pub [u8; C_LEN]);

#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct SharedSecret(pub [u8; 32]);

pub fn keygen_internal<const EK_LEN: usize, const DK_LEN: usize>(
    params: &PkeParams,
    d: &[u8; 32],
    z: &[u8; 32]
) -> (EncapsulationKey<EK_LEN>, DecapsulationKey<DK_LEN>) {
    let mut ek = [0u8; EK_LEN];
    let mut dk_pke = [0u8; DK_LEN];
    
    pke_keygen(params, d, &mut ek, &mut dk_pke[0..384 * params.k]);
    let ek_hash = h(&ek);

    let dk_pke_len = 384 * params.k;
    dk_pke[dk_pke_len..dk_pke_len + EK_LEN].copy_from_slice(&ek);
    dk_pke[dk_pke_len + EK_LEN..dk_pke_len + EK_LEN + 32].copy_from_slice(&ek_hash);
    dk_pke[dk_pke_len + EK_LEN + 32..dk_pke_len + EK_LEN + 64].copy_from_slice(z);

    (EncapsulationKey(ek), DecapsulationKey(dk_pke))
}

pub fn encaps_internal<const EK_LEN: usize, const C_LEN: usize>(
    params: &PkeParams,
    ek: &EncapsulationKey<EK_LEN>,
    m: &[u8; 32]
) -> (SharedSecret, Ciphertext<C_LEN>) {
    let mut g_input = [0u8; 64];
    g_input[0..32].copy_from_slice(m);
    g_input[32..64].copy_from_slice(&h(&ek.0));
    let g_out = g(&g_input);

    let mut k = [0u8; 32];
    let mut r = [0u8; 32];
    k.copy_from_slice(&g_out[0..32]);
    r.copy_from_slice(&g_out[32..64]);

    let mut c = [0u8; C_LEN];
    pke_encrypt(params, &ek.0, m, &r, &mut c);
    (SharedSecret(k), Ciphertext(c))
}

pub fn decaps_internal<const EK_LEN: usize, const DK_LEN: usize, const C_LEN: usize>(
    params: &PkeParams,
    dk: &DecapsulationKey<DK_LEN>,
    c: &Ciphertext<C_LEN>
) -> SharedSecret {
    let dk_bytes = &dk.0;
    let dk_pke = &dk_bytes[0..384 * params.k];
    let ek = &dk_bytes[384 * params.k..384 * params.k + EK_LEN];
    let h_ek = &dk_bytes[384 * params.k + EK_LEN..384 * params.k + EK_LEN + 32];
    let z = &dk_bytes[384 * params.k + EK_LEN + 32..384 * params.k + EK_LEN + 64];

    let mut m_prime = [0u8; 32];
    pke_decrypt(params, dk_pke, &c.0, &mut m_prime);

    let mut g_input = [0u8; 64];
    g_input[0..32].copy_from_slice(&m_prime);
    g_input[32..64].copy_from_slice(h_ek);
    let g_out = g(&g_input);

    let mut k_prime = [0u8; 32];
    let mut r_prime = [0u8; 32];
    k_prime.copy_from_slice(&g_out[0..32]);
    r_prime.copy_from_slice(&g_out[32..64]);

    let mut c_prime = [0u8; C_LEN];
    pke_encrypt(params, ek, &m_prime, &r_prime, &mut c_prime);

    use subtle::{ConstantTimeEq, ConditionallySelectable};

    let mut hasher = sha3::Shake256::default();
    sha3::digest::Update::update(&mut hasher, z);
    sha3::digest::Update::update(&mut hasher, &c.0);
    let mut reader = sha3::digest::ExtendableOutput::finalize_xof(hasher);
    let mut implicit_rej_secret = [0u8; 32];
    sha3::digest::XofReader::read(&mut reader, &mut implicit_rej_secret);

    let mut is_valid = 1u8;
    for i in 0..C_LEN {
        if c.0[i] != c_prime[i] {
            is_valid = 0;
        }
    }
    let is_valid_ct = subtle::Choice::from(is_valid);

    let mut final_secret = [0u8; 32];
    for i in 0..32 {
        final_secret[i] = u8::conditional_select(&implicit_rej_secret[i], &k_prime[i], is_valid_ct);
    }

    m_prime.zeroize();
    k_prime.zeroize();
    r_prime.zeroize();
    implicit_rej_secret.zeroize();

    SharedSecret(final_secret)
}

pub struct MlKem512;
impl MlKem512 {
    pub fn generate_keypair(rng: &mut impl CryptoRngCore) -> (EncapsulationKey<800>, DecapsulationKey<1632>) {
        let mut d = [0u8; 32];
        let mut z = [0u8; 32];
        rng.fill_bytes(&mut d);
        rng.fill_bytes(&mut z);
        keygen_internal::<800, 1632>(&crate::kyber::pke::ML_KEM_512, &d, &z)
    }
    pub fn encapsulate(ek: &EncapsulationKey<800>, rng: &mut impl CryptoRngCore) -> (SharedSecret, Ciphertext<768>) {
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        encaps_internal::<800, 768>(&crate::kyber::pke::ML_KEM_512, ek, &m)
    }
    pub fn decapsulate(dk: &DecapsulationKey<1632>, c: &Ciphertext<768>) -> SharedSecret {
        decaps_internal::<800, 1632, 768>(&crate::kyber::pke::ML_KEM_512, dk, c)
    }
}

pub struct MlKem768;
impl MlKem768 {
    pub fn generate_keypair(rng: &mut impl CryptoRngCore) -> (EncapsulationKey<1184>, DecapsulationKey<2400>) {
        let mut d = [0u8; 32];
        let mut z = [0u8; 32];
        rng.fill_bytes(&mut d);
        rng.fill_bytes(&mut z);
        keygen_internal::<1184, 2400>(&crate::kyber::pke::ML_KEM_768, &d, &z)
    }
    pub fn encapsulate(ek: &EncapsulationKey<1184>, rng: &mut impl CryptoRngCore) -> (SharedSecret, Ciphertext<1088>) {
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        encaps_internal::<1184, 1088>(&crate::kyber::pke::ML_KEM_768, ek, &m)
    }
    pub fn decapsulate(dk: &DecapsulationKey<2400>, c: &Ciphertext<1088>) -> SharedSecret {
        decaps_internal::<1184, 2400, 1088>(&crate::kyber::pke::ML_KEM_768, dk, c)
    }
}

pub struct MlKem1024;
impl MlKem1024 {
    pub fn generate_keypair(rng: &mut impl CryptoRngCore) -> (EncapsulationKey<1568>, DecapsulationKey<3168>) {
        let mut d = [0u8; 32];
        let mut z = [0u8; 32];
        rng.fill_bytes(&mut d);
        rng.fill_bytes(&mut z);
        keygen_internal::<1568, 3168>(&crate::kyber::pke::ML_KEM_1024, &d, &z)
    }
    pub fn encapsulate(ek: &EncapsulationKey<1568>, rng: &mut impl CryptoRngCore) -> (SharedSecret, Ciphertext<1568>) {
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        encaps_internal::<1568, 1568>(&crate::kyber::pke::ML_KEM_1024, ek, &m)
    }
    pub fn decapsulate(dk: &DecapsulationKey<3168>, c: &Ciphertext<1568>) -> SharedSecret {
        decaps_internal::<1568, 3168, 1568>(&crate::kyber::pke::ML_KEM_1024, dk, c)
    }
}
