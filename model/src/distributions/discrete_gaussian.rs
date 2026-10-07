use alloc::vec::Vec;
use crate::distributions::ErrorDistribution;
use crate::params::LweParams;
use rand::Rng;

pub struct DiscreteGaussian {
    pub eta: usize,
}

impl ErrorDistribution for DiscreteGaussian {
    fn sample(&self, params: &LweParams) -> Vec<u64> {
        let mut rng = rand::thread_rng();
        let mut error = Vec::with_capacity(params.m);
        for _ in 0..params.m {
            let mut a = 0;
            let mut b = 0;
            for _ in 0..self.eta {
                a += rng.gen_range(0..2);
                b += rng.gen_range(0..2);
            }

            let val = (a + params.q - b) % params.q;
            error.push(val);
        }
        error
    }
}
