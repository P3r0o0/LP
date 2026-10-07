pub const KYBER_Q: i16 = 3329;
pub const KYBER_N: usize = 256;

pub fn montgomery_reduce(a: i32) -> i16 {
    let qinv = 62209i32;
    let t = (a.wrapping_mul(qinv)) as i16 as i32;
    let mut u = a - t * (KYBER_Q as i32);
    u >>= 16;
    u as i16
}

pub fn barrett_reduce(a: i16) -> i16 {
    let v = ((1i32 << 26) + (KYBER_Q as i32) / 2) / (KYBER_Q as i32);
    let t = ((v * (a as i32)) + (1 << 25)) >> 26;
    a - (t as i16) * KYBER_Q
}

pub const ZETAS: [i16; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

pub fn ntt(r: &mut [i16; 256]) {
    let mut k = 1;
    let mut len = 128;
    while len >= 2 {
        let mut start = 0;
        while start < 256 {
            let zeta = ZETAS[k];
            k += 1;
            for j in start..(start + len) {
                let t = montgomery_reduce((zeta as i32) * (r[j + len] as i32));
                r[j + len] = r[j] - t;
                r[j] = r[j] + t;
            }
            start = start + 2 * len;
        }
        len >>= 1;
    }
}

pub fn intt(r: &mut [i16; 256]) {
    let mut k = 127;
    let mut len = 2;
    while len <= 128 {
        let mut start = 0;
        while start < 256 {
            let zeta = -ZETAS[k];
            k -= 1;
            for j in start..(start + len) {
                let t = r[j];
                r[j] = barrett_reduce(t + r[j + len]);
                r[j + len] = t - r[j + len];
                r[j + len] = montgomery_reduce((zeta as i32) * (r[j + len] as i32));
            }
            start = start + 2 * len;
        }
        len <<= 1;
    }

    let f = 1441;
    for j in 0..256 {
        r[j] = montgomery_reduce((r[j] as i32) * f);
    }
}

pub fn tomont(r: &mut [i16; 256]) {
    let f = 1353;
    for j in 0..256 {
        r[j] = montgomery_reduce((r[j] as i32) * f);
    }
}
