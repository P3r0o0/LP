use alloc::vec::Vec;
pub type Matrix = Vec<Vec<u64>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LweSample {
    pub a: Matrix,
    pub b: Vec<u64>,
}

impl LweSample {
    pub fn new(a: Matrix, b: Vec<u64>) -> Self {
        Self { a, b }
    }
}
