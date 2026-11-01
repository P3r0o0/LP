use lwe_rust::fhe::bfv::{
    BFVContext, BFVParams, Ciphertext as BFVCiphertext, GaloisKey, PublicKey as BFVPublicKey,
    RelinKey, SecretKey as BFVSecretKey,
};
use lwe_rust::lwe::math::{
    add_mod, centered_lift, compress_coeff, decompress_coeff, mul_mod, norm, sub_mod,
    BarrettModulus,
};
use lwe_rust::lwe::ntt::{inv_ntt_naive, ntt_naive, pow_mod, NTTTable};
use lwe_rust::lwe::pke::{
    ModPKECiphertext, ModPKECompressedPublicKey, ModPKEPublicKey, ModPKESecretKey,
};
use lwe_rust::lwe::poly::Polynomial;
use lwe_rust::lwe::sample::LweSample;
use lwe_rust::zkp::mod_nizk::ModNIZKProof;
use lwe_rust::zkp::nizk::NIZKProof;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

#[test]
fn test_barrett_modulus_boundary_and_random_property() {
    let moduli: [u64; 12] = [
        2,
        3,
        17,
        97,
        3329,
        65537,
        (1u64 << 31) - 1,
        (1u64 << 32) - 5,
        (1u64 << 32) + 15,
        (1u64 << 50) + 15,
        29 * (1u64 << 57) + 1,
        (1u64 << 62) - 57,
    ];

    let mut rng = StdRng::seed_from_u64(0x2026_1028_CAFE_BEEF);

    for &q in &moduli {
        let barrett = BarrettModulus::new(q);

        let mut boundaries = vec![0u64, 1, q / 2, q - 1];
        if q >= 4 {
            boundaries.push(2);
            boundaries.push(q / 2 - 1);
            boundaries.push((q / 2 + 1).min(q - 1));
            boundaries.push(q - 2);
        }

        for &a in &boundaries {
            for &b in &boundaries {
                let got = barrett.mul_mod(a, b);
                let expected = mul_mod(a, b, q);
                assert_eq!(
                    got, expected,
                    "Boundary mismatch for q={}, a={}, b={}: got {}, expected {}",
                    q, a, b, got, expected
                );
            }
        }

        for _ in 0..20_000 {
            let a = rng.gen_range(0..q);
            let b = rng.gen_range(0..q);
            assert_eq!(barrett.mul_mod(a, b), mul_mod(a, b, q));
            assert_eq!(
                add_mod(a, b, q),
                ((a as u128 + b as u128) % (q as u128)) as u64
            );
            assert_eq!(
                sub_mod(a, b, q),
                (((a as u128) + (q as u128) - (b as u128)) % (q as u128)) as u64
            );
        }
    }
}

#[test]
fn test_exhaustive_centered_lift_norm_and_compression_bounds() {
    for &q in &[2u64, 3, 16, 17, 256, 257, 3329] {
        for x in 0..q {
            let lift = centered_lift(x, q);
            let n_val = norm(x, q);

            let expected_lift = if x <= q / 2 {
                x as i64
            } else {
                -((q - x) as i64)
            };
            assert_eq!(
                lift, expected_lift,
                "centered_lift mismatch for x={}, q={}",
                x, q
            );
            assert_eq!(
                lift.unsigned_abs(),
                n_val,
                "norm must equal |centered_lift| for x={}, q={}",
                x,
                q
            );
        }

        for d in 1..=11u32 {
            if (1u64 << d) > q * 2 {
                break;
            }
            let max_bound = (q + (1u64 << d)) / (1u64 << (d + 1));
            for x in 0..q {
                let y = compress_coeff(x, q, d);
                assert!(y < (1u64 << d));
                let x_rec = decompress_coeff(y, q, d);
                assert!(x_rec < q);
                let diff = sub_mod(x, x_rec, q);
                let err = norm(diff, q);
                assert!(
                    err <= max_bound,
                    "Compression error {} > bound {} for q={}, d={}, x={}",
                    err,
                    max_bound,
                    q,
                    d,
                    x
                );
            }
        }
    }
}

#[test]
fn test_ntt_table_vs_naive_across_all_small_degrees() {
    let q = 65537u64;
    let mut rng = StdRng::seed_from_u64(0x7777_8888_9999_AAAA);

    for &n in &[1usize, 2, 4, 8, 16, 32, 64] {
        let psi = pow_mod(3, (q - 1) / ((2 * n) as u64), q);
        assert_eq!(pow_mod(psi, n as u64, q), q - 1);

        let table = NTTTable::new(n, psi, q);
        let p1 = Polynomial::new((0..n).map(|_| rng.gen_range(0..q)).collect());
        let p2 = Polynomial::new((0..n).map(|_| rng.gen_range(0..q)).collect());

        let fwd_table = table.forward(&p1);
        let fwd_naive = ntt_naive(&p1, psi, q);
        assert_eq!(
            fwd_table, fwd_naive,
            "NTTTable::forward != ntt_naive for N={}",
            n
        );

        let inv_table = table.inverse(&fwd_table);
        let inv_naive = inv_ntt_naive(&fwd_naive, psi, q);
        assert_eq!(
            inv_table, p1,
            "NTTTable::inverse failed round-trip for N={}",
            n
        );
        assert_eq!(
            inv_table, inv_naive,
            "NTTTable::inverse != inv_ntt_naive for N={}",
            n
        );

        let prod_table = table.mul_ntt(&p1, &p2);
        let prod_school = p1.mul_schoolbook(&p2, q);
        assert_eq!(
            prod_table, prod_school,
            "NTTTable::mul_ntt != mul_schoolbook for N={}",
            n
        );
    }
}

#[test]
fn test_bfv_60bit_modulus_large_t_no_i128_overflow() {
    let n = 8;
    let q: u64 = (1u64 << 59) + 55;
    let t: u64 = 65537;
    let ctx = BFVContext::new(n, q, t);
    assert!(ctx.params.is_mul_overflow_safe());

    let (sk, pk) = ctx.keygen();
    let rk = ctx.keygen_relin(&sk, 1u64 << 20, 3);

    let pt1 = Polynomial::new(vec![100, 200, 300, 400, 50, 60, 70, 80]);
    let pt2 = Polynomial::new(vec![3, 5, 7, 11, 13, 17, 19, 23]);
    let ct1 = ctx.encrypt(&pk, &pt1);
    let ct2 = ctx.encrypt(&pk, &pt2);

    let ct_mul = ctx.mul(&ct1, &ct2, &rk);
    let dec = ctx.decrypt(&sk, &ct_mul);
    assert_eq!(dec, pt1.mul_schoolbook(&pt2, t));
}

#[test]
#[should_panic(expected = "exceed i128 unreduced multiplication bound")]
fn test_bfv_params_rejects_i128_overflow_configuration() {
    let _ = BFVParams::new(4096, 1u64 << 62, 16);
}

#[test]
fn test_fuzz_deserialization_never_panics_on_random_bytes() {
    let mut rng = StdRng::seed_from_u64(0xF022_BA5E_1234_5678);
    let k = 2;
    let l = 2;
    let n = 8;
    let q = 3329u64;

    for len in [0usize, 1, 7, 8, 16, 24, 32, 64, 128, 160, 256, 384, 512] {
        for _ in 0..50 {
            let mut bytes = vec![0u8; len];
            rng.fill(&mut bytes[..]);

            let _ = Polynomial::from_bytes(&bytes, n, q);
            let _ = LweSample::from_bytes(&bytes, k, n, q);
            let _ = ModPKEPublicKey::from_bytes(&bytes, k, n, q);
            let _ = ModPKECompressedPublicKey::from_bytes(&bytes, k, n, q);
            let _ = ModPKESecretKey::from_bytes(&bytes, k, n, q);
            let _ = ModPKECiphertext::from_bytes(&bytes, k, n, q);
            let _ = NIZKProof::from_bytes(&bytes, n, q);
            let _ = ModNIZKProof::from_bytes(&bytes, k, l, n, q);
            let _ = BFVPublicKey::from_bytes(&bytes, n, q);
            let _ = BFVSecretKey::from_bytes(&bytes, n, q);
            let _ = BFVCiphertext::from_bytes(&bytes, n, q);
            let _ = RelinKey::from_bytes(&bytes, n, q);
            let _ = GaloisKey::from_bytes(&bytes, n, q);
        }
    }
}
