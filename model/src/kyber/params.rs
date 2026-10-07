pub trait KemParams {
    const K: usize;
    const ETA1: usize;
    const ETA2: usize;
    const DU: u8;
    const DV: u8;
    const EK_LEN: usize;
    const DK_LEN: usize;
    const C_LEN: usize;
}

pub struct MlKem512;
impl KemParams for MlKem512 {
    const K: usize = 2;
    const ETA1: usize = 3;
    const ETA2: usize = 2;
    const DU: u8 = 10;
    const DV: u8 = 4;
    const EK_LEN: usize = 800;
    const DK_LEN: usize = 1632;
    const C_LEN: usize = 768;
}

pub struct MlKem768;
impl KemParams for MlKem768 {
    const K: usize = 3;
    const ETA1: usize = 2;
    const ETA2: usize = 2;
    const DU: u8 = 10;
    const DV: u8 = 4;
    const EK_LEN: usize = 1184;
    const DK_LEN: usize = 2400;
    const C_LEN: usize = 1088;
}

pub struct MlKem1024;
impl KemParams for MlKem1024 {
    const K: usize = 4;
    const ETA1: usize = 2;
    const ETA2: usize = 2;
    const DU: u8 = 11;
    const DV: u8 = 5;
    const EK_LEN: usize = 1568;
    const DK_LEN: usize = 3168;
    const C_LEN: usize = 1568;
}
