use sha3::Shake128;
use sha3::Shake256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Digest, Sha3_256, Sha3_512,
};

pub fn g(input: &[u8]) -> [u8; 64] {
    let mut hasher = Sha3_512::new();
    Update::update(&mut hasher, input);
    let result = hasher.finalize();
    let mut out = [0u8; 64];
    out.copy_from_slice(&result);
    out
}

pub fn h(input: &[u8]) -> [u8; 32] {
    let mut hasher = Sha3_256::new();
    Update::update(&mut hasher, input);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

pub fn prf(key: &[u8; 32], nonce: u8, out: &mut [u8]) {
    let mut hasher = Shake256::default();
    hasher.update(key);
    hasher.update(&[nonce]);
    let mut reader = hasher.finalize_xof();
    reader.read(out);
}

pub fn xof(seed: &[u8; 32], i: u8, j: u8, out: &mut [u8]) {
    let mut hasher = Shake128::default();
    hasher.update(seed);
    hasher.update(&[i, j]);
    let mut reader = hasher.finalize_xof();
    reader.read(out);
}
