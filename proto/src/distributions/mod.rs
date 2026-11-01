use crate::params::LweParams;
use alloc::vec::Vec;

pub mod discrete_gaussian;
pub mod uniform;

pub trait ErrorDistribution {
    #[cfg(feature = "std")]
    fn sample(&self, params: &LweParams) -> Vec<u64> {
        let mut rng = rand::thread_rng();
        self.sample_with_rng(&mut rng, params)
    }
    fn sample_with_rng(&self, rng: &mut dyn rand::RngCore, params: &LweParams) -> Vec<u64>;
}
