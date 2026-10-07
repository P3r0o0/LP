#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LweParams {
    pub n: usize,

    pub m: usize,

    pub q: u64,
}

impl LweParams {
    pub fn new(n: usize, m: usize, q: u64) -> Self {
        Self { n, m, q }
    }
}
