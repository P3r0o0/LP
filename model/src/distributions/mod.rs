use alloc::vec::Vec;
use crate::params::LweParams;

pub mod discrete_gaussian;
pub mod uniform;

pub trait ErrorDistribution {
    fn sample(&self, params: &LweParams) -> Vec<u64>;
}
