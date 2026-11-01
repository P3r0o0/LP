#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LweParams {
    pub n: usize,

    pub m: usize,

    pub q: u64,
}

impl LweParams {
    pub fn new(n: usize, m: usize, q: u64) -> Self {
        assert!(n > 0 && m > 0, "Dimensions n and m must be > 0");
        assert!(q >= 2, "Modulus q must be >= 2");
        Self { n, m, q }
    }
}
