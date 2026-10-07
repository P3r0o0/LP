#[derive(Clone, Copy, Debug)]
pub struct SU2Link {
    pub a0: f64,
    pub a1: f64,
    pub a2: f64,
    pub a3: f64,
}

impl SU2Link {
    pub fn new(a0: f64, a1: f64, a2: f64, a3: f64) -> Self {
        let norm = (a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3).sqrt();
        SU2Link {
            a0: a0 / norm,
            a1: a1 / norm,
            a2: a2 / norm,
            a3: a3 / norm,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct U1Link {
    pub phase: f64,
}

impl U1Link {
    pub fn new(phase: f64) -> Self {
        U1Link { phase }
    }
}

pub fn abelian_projection(link: &SU2Link) -> (U1Link, f64) {
    let _norm_diag = (link.a0 * link.a0 + link.a3 * link.a3).sqrt();
    let phase = link.a3.atan2(link.a0);

    let norm_offdiag = (link.a1 * link.a1 + link.a2 * link.a2).sqrt();

    (U1Link::new(phase), norm_offdiag)
}
