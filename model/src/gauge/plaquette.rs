use crate::gauge::abelian_proj::{abelian_projection, SU2Link, U1Link};

impl SU2Link {
    pub fn dagger(&self) -> Self {
        SU2Link {
            a0: self.a0,
            a1: -self.a1,
            a2: -self.a2,
            a3: -self.a3,
        }
    }

    pub fn mul(&self, other: &SU2Link) -> Self {
        SU2Link {
            a0: self.a0 * other.a0 - self.a1 * other.a1 - self.a2 * other.a2 - self.a3 * other.a3,
            a1: self.a0 * other.a1 + self.a1 * other.a0 - self.a2 * other.a3 + self.a3 * other.a2,
            a2: self.a0 * other.a2 + self.a2 * other.a0 - self.a3 * other.a1 + self.a1 * other.a3,
            a3: self.a0 * other.a3 + self.a3 * other.a0 - self.a1 * other.a2 + self.a2 * other.a1,
        }
    }
}

pub fn compute_plaquette_su2(u1: &SU2Link, u2: &SU2Link, u3: &SU2Link, u4: &SU2Link) -> SU2Link {
    let p1 = u1.mul(u2);
    let p2 = u3.dagger().mul(&u4.dagger());
    p1.mul(&p2)
}

pub fn compute_plaquette_u1(u1: &U1Link, u2: &U1Link, u3: &U1Link, u4: &U1Link) -> U1Link {
    let mut phase = u1.phase + u2.phase - u3.phase - u4.phase;

    while phase > core::f64::consts::PI {
        phase -= 2.0 * core::f64::consts::PI;
    }
    while phase < -core::f64::consts::PI {
        phase += 2.0 * core::f64::consts::PI;
    }
    U1Link::new(phase)
}

pub fn extract_lwe_noise_from_plaquette(
    u1: &SU2Link,
    u2: &SU2Link,
    u3: &SU2Link,
    u4: &SU2Link,
    q: i64,
) -> i64 {
    let plaq_su2 = compute_plaquette_su2(u1, u2, u3, u4);
    let (plaq_su2_proj, _) = abelian_projection(&plaq_su2);

    let (p1, _) = abelian_projection(u1);
    let (p2, _) = abelian_projection(u2);
    let (p3, _) = abelian_projection(u3);
    let (p4, _) = abelian_projection(u4);
    let plaq_u1 = compute_plaquette_u1(&p1, &p2, &p3, &p4);

    let mut diff = plaq_su2_proj.phase - plaq_u1.phase;
    while diff > core::f64::consts::PI {
        diff -= 2.0 * core::f64::consts::PI;
    }
    while diff < -core::f64::consts::PI {
        diff += 2.0 * core::f64::consts::PI;
    }

    let scale = (q as f64) / (2.0 * core::f64::consts::PI);
    let mut discrete_e = (diff * scale).round() as i64;
    discrete_e = discrete_e % q;
    if discrete_e < 0 {
        discrete_e += q;
    }

    if discrete_e > q / 2 {
        discrete_e -= q;
    }
    discrete_e
}
