use std::hint::black_box;
use std::sync::Mutex;
use std::time::Instant;

static TIMING_LOCK: Mutex<()> = Mutex::new(());

use lwe_rust::fhe::bfv::{BFVBatchEncoder, BFVContext};
use lwe_rust::lwe::kem::ModKEMContext;
use lwe_rust::lwe::math::{centered_lift, compress_coeff, decompress_coeff, norm, BarrettModulus};
use lwe_rust::lwe::ntt::NTTTable;
use lwe_rust::lwe::poly::Polynomial;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

fn cropped_welch_t_stat(mut class0_ns: Vec<f64>, mut class1_ns: Vec<f64>) -> f64 {
    class0_ns.sort_by(|a, b| a.partial_cmp(b).unwrap());
    class1_ns.sort_by(|a, b| a.partial_cmp(b).unwrap());

    let keep0 = (class0_ns.len() * 95) / 100;
    let keep1 = (class1_ns.len() * 95) / 100;
    let s0 = &class0_ns[..keep0];
    let s1 = &class1_ns[..keep1];

    let n0 = s0.len() as f64;
    let n1 = s1.len() as f64;
    let mean0 = s0.iter().sum::<f64>() / n0;
    let mean1 = s1.iter().sum::<f64>() / n1;

    let var0 = s0.iter().map(|&x| (x - mean0).powi(2)).sum::<f64>() / (n0 - 1.0);
    let var1 = s1.iter().map(|&x| (x - mean1).powi(2)).sum::<f64>() / (n1 - 1.0);

    let denom = (var0 / n0 + var1 / n1).sqrt();
    if denom < 1e-12 {
        0.0
    } else {
        (mean0 - mean1).abs() / denom
    }
}

fn median_welch_t_stat<F>(rounds: usize, mut run_round: F) -> f64
where
    F: FnMut() -> (Vec<f64>, Vec<f64>),
{
    let mut stats = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let (c0, c1) = run_round();
        stats.push(cropped_welch_t_stat(c0, c1));
    }
    stats.sort_by(|a, b| a.partial_cmp(b).unwrap());
    stats[rounds / 2]
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn ct_probe_barrett_mul(b: &BarrettModulus, x: u64, y: u64) -> u64 {
    b.mul_mod(x, y)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn ct_probe_norm_and_lift(x: u64, q: u64) -> u64 {
    norm(x, q) ^ (centered_lift(x, q) as u64)
}

#[test]
fn test_machine_code_branchless_and_division_free_isa() {
    let _guard = TIMING_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let b = BarrettModulus::new(3329);
    assert_eq!(ct_probe_barrett_mul(black_box(&b), 10, 20), 200);
    assert_ne!(ct_probe_norm_and_lift(black_box(2000), 3329), 0);

    let exe = std::env::current_exe().expect("current_exe");
    for sym in ["ct_probe_barrett_mul", "ct_probe_norm_and_lift"] {
        let out = std::process::Command::new("objdump")
            .args(["-d", &format!("--disassemble={sym}"), exe.to_str().unwrap()])
            .output()
            .expect("objdump execution");
        let disasm = String::from_utf8_lossy(&out.stdout);
        assert!(
            disasm.contains(&format!("<{sym}>:")),
            "Symbol {sym} not found in objdump output"
        );

        for line in disasm.lines() {
            let parts: Vec<&str> = line.split('\t').collect();
            if parts.len() >= 3 {
                let instr = parts[2].trim();
                let mnemonic = instr.split_whitespace().next().unwrap_or("");
                assert!(
                    mnemonic != "div"
                        && mnemonic != "idiv"
                        && mnemonic != "divq"
                        && mnemonic != "idivq",
                    "Found forbidden hardware division instruction `{instr}` in `{sym}`"
                );
                if !cfg!(debug_assertions) {
                    let is_cond_jmp =
                        mnemonic.starts_with('j') && mnemonic != "jmp" && mnemonic != "jmpq";
                    assert!(
                        !is_cond_jmp,
                        "Found forbidden conditional branch `{instr}` in optimized `{sym}`"
                    );
                }
            }
        }
    }
}

#[inline(never)]
fn run_barrett_norm_batch(barrett: &BarrettModulus, q: u64, inputs: &[u64]) -> u64 {
    let mut acc = 0u64;
    for &x in inputs {
        let v = black_box(x);
        acc ^= ct_probe_barrett_mul(barrett, v, v) ^ ct_probe_norm_and_lift(v, q);
    }
    black_box(acc)
}

#[test]
fn test_constant_time_barrett_and_norm_welch_t() {
    let _guard = TIMING_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let q = (1u64 << 61) - 1;
    let barrett = BarrettModulus::new(q);

    let batch = 512usize;
    let inputs0: Vec<u64> = (0..batch).map(|i| i as u64).collect();
    let inputs1: Vec<u64> = (0..batch).map(|i| q - 1 - (i as u64)).collect();
    let mut work_buf = vec![0u64; batch];

    work_buf.copy_from_slice(&inputs0);
    black_box(run_barrett_norm_batch(
        black_box(&barrett),
        black_box(q),
        black_box(&work_buf),
    ));
    work_buf.copy_from_slice(&inputs1);
    black_box(run_barrett_norm_batch(
        black_box(&barrett),
        black_box(q),
        black_box(&work_buf),
    ));

    let median_t = median_welch_t_stat(5, || {
        let trials = 200;
        let mut c0 = Vec::with_capacity(trials);
        let mut c1 = Vec::with_capacity(trials);

        for t in 0..trials {
            if t % 2 == 0 {
                work_buf.copy_from_slice(&inputs0);
                black_box(run_barrett_norm_batch(&barrett, q, &work_buf[..8]));
                let start0 = Instant::now();
                black_box(run_barrett_norm_batch(
                    black_box(&barrett),
                    black_box(q),
                    black_box(&work_buf),
                ));
                c0.push(start0.elapsed().as_nanos() as f64);

                work_buf.copy_from_slice(&inputs1);
                black_box(run_barrett_norm_batch(&barrett, q, &work_buf[..8]));
                let start1 = Instant::now();
                black_box(run_barrett_norm_batch(
                    black_box(&barrett),
                    black_box(q),
                    black_box(&work_buf),
                ));
                c1.push(start1.elapsed().as_nanos() as f64);
            } else {
                work_buf.copy_from_slice(&inputs1);
                black_box(run_barrett_norm_batch(&barrett, q, &work_buf[..8]));
                let start1 = Instant::now();
                black_box(run_barrett_norm_batch(
                    black_box(&barrett),
                    black_box(q),
                    black_box(&work_buf),
                ));
                c1.push(start1.elapsed().as_nanos() as f64);

                work_buf.copy_from_slice(&inputs0);
                black_box(run_barrett_norm_batch(&barrett, q, &work_buf[..8]));
                let start0 = Instant::now();
                black_box(run_barrett_norm_batch(
                    black_box(&barrett),
                    black_box(q),
                    black_box(&work_buf),
                ));
                c0.push(start0.elapsed().as_nanos() as f64);
            }
        }
        (c0, c1)
    });

    println!("Barrett / norm 5-round median Welch |t|-stat: {median_t:.2}");
    assert!(
        median_t < 4.5,
        "Barrett / norm median Welch |t|-statistic exceeded dudect 4.5 threshold: {median_t:.2}"
    );
}

#[inline(never)]
fn run_decaps_batch(
    kem: &ModKEMContext,
    sk: &lwe_rust::lwe::kem::ModKEMSecretKey,
    ct: &lwe_rust::lwe::pke::ModPKECiphertext,
    batch: usize,
) -> u8 {
    let mut acc = 0u8;
    for _ in 0..batch {
        let ss = kem.decaps(black_box(sk), black_box(ct));
        acc ^= ss[0];
    }
    black_box(acc)
}

#[test]
fn test_constant_time_kem_decaps_implicit_rejection_welch_t() {
    let _guard = TIMING_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let kem = ModKEMContext::preset_toy_zero_failure();
    let mut rng = StdRng::seed_from_u64(0xDEC0_FFEE);
    let (sk, pk) = kem.keygen_with_rng(&mut rng);
    let (valid_ct, valid_ss) = kem.encaps_with_rng(&mut rng, &pk);

    let mut invalid_ct = valid_ct.clone();
    invalid_ct.v.coeffs[0] = (invalid_ct.v.coeffs[0] + 24) % 97;
    let invalid_ss = kem.decaps(&sk, &invalid_ct);
    assert_ne!(
        valid_ss, invalid_ss,
        "Implicit rejection must produce a distinct pseudorandom key"
    );

    let mut work_ct = valid_ct.clone();
    black_box(run_decaps_batch(&kem, &sk, &work_ct, 16));

    let median_t = median_welch_t_stat(5, || {
        let trials = 160;
        let batch = 16;
        let mut c0 = Vec::with_capacity(trials);
        let mut c1 = Vec::with_capacity(trials);

        for t in 0..trials {
            if t % 2 == 0 {
                work_ct.v.coeffs[0] = valid_ct.v.coeffs[0];
                black_box(run_decaps_batch(&kem, &sk, &work_ct, 1));
                let start0 = Instant::now();
                black_box(run_decaps_batch(&kem, &sk, &work_ct, batch));
                c0.push(start0.elapsed().as_nanos() as f64);

                work_ct.v.coeffs[0] = invalid_ct.v.coeffs[0];
                black_box(run_decaps_batch(&kem, &sk, &work_ct, 1));
                let start1 = Instant::now();
                black_box(run_decaps_batch(&kem, &sk, &work_ct, batch));
                c1.push(start1.elapsed().as_nanos() as f64);
            } else {
                work_ct.v.coeffs[0] = invalid_ct.v.coeffs[0];
                black_box(run_decaps_batch(&kem, &sk, &work_ct, 1));
                let start1 = Instant::now();
                black_box(run_decaps_batch(&kem, &sk, &work_ct, batch));
                c1.push(start1.elapsed().as_nanos() as f64);

                work_ct.v.coeffs[0] = valid_ct.v.coeffs[0];
                black_box(run_decaps_batch(&kem, &sk, &work_ct, 1));
                let start0 = Instant::now();
                black_box(run_decaps_batch(&kem, &sk, &work_ct, batch));
                c0.push(start0.elapsed().as_nanos() as f64);
            }
        }
        (c0, c1)
    });

    println!("KEM decaps 5-round median Welch |t|-stat: {median_t:.2}");
    assert!(
        median_t < 4.5,
        "KEM decaps valid vs invalid ciphertext median Welch |t|-statistic exceeded 4.5: {median_t:.2}"
    );
}

#[test]
fn test_fips203_mlkem_compress_decompress_kat() {
    let q = 3329u64;
    for &d in &[1u32, 4, 5, 10, 11] {
        let two_d = 1u64 << d;
        for x in 0..q {
            let expected_c = (((x as u128) * (1u128 << (d + 1)) + (q as u128)) / (2 * (q as u128)))
                as u64
                % two_d;
            let actual_c = compress_coeff(x, q, d);
            assert_eq!(actual_c, expected_c, "FIPS 203 Compress_{d}({x}) mismatch");
        }

        for y in 0..two_d {
            let expected_x = (((y as u128) * (q as u128) * 2 + (two_d as u128)) >> (d + 1)) as u64;
            let actual_x = decompress_coeff(y, q, d);
            assert_eq!(
                actual_x, expected_x,
                "FIPS 203 Decompress_{d}({y}) mismatch"
            );
        }
    }

    assert_eq!(compress_coeff(0, 3329, 1), 0);
    assert_eq!(compress_coeff(832, 3329, 1), 0);
    assert_eq!(compress_coeff(833, 3329, 1), 1);
    assert_eq!(compress_coeff(2496, 3329, 1), 1);
    assert_eq!(compress_coeff(2497, 3329, 1), 0);
    assert_eq!(decompress_coeff(0, 3329, 1), 0);
    assert_eq!(decompress_coeff(1, 3329, 1), 1665);
}

#[test]
fn test_negacyclic_ntt_and_bfv_simd_kat_vectors() {
    let table = NTTTable::new(4, 33, 97);
    let p = Polynomial::new(vec![1u64, 2, 3, 4]);
    let q_poly = Polynomial::new(vec![5u64, 6, 7, 8]);
    let prod = table.mul_ntt(&p, &q_poly);
    assert_eq!(prod.coeffs, vec![41, 61, 2, 60]);

    let ctx = BFVContext::new_with_ntt(4, 65537, 17, 16);
    let encoder = BFVBatchEncoder::new(4, 17, 2);

    let slots_a = vec![3u64, 10, 5, 14];
    let slots_b = vec![4u64, 7, 11, 2];
    let pt_a = encoder.encode_simd(&slots_a);
    let pt_b = encoder.encode_simd(&slots_b);

    let mut rng = StdRng::seed_from_u64(0xBF70_2026);
    let (sk, pk) = ctx.keygen_with_rng(&mut rng);
    let rlk = ctx.keygen_relin_with_rng(&mut rng, &sk, 16, 4);

    let ct_a = ctx.encrypt_with_rng(&mut rng, &pk, &pt_a);
    let ct_b = ctx.encrypt_with_rng(&mut rng, &pk, &pt_b);
    let ct_prod = ctx.mul(&ct_a, &ct_b, &rlk);
    let ct_sum = ctx.add(&ct_prod, &ct_a);

    let dec_poly = ctx.decrypt(&sk, &ct_sum);
    let dec_slots = encoder.decode_simd(&dec_poly);

    let expected_slots: Vec<u64> = slots_a
        .iter()
        .zip(slots_b.iter())
        .map(|(&a, &b)| (a * b + a) % 17)
        .collect();
    assert_eq!(dec_slots, expected_slots);
    assert_eq!(dec_slots, vec![15, 12, 9, 8]);

    assert_eq!(centered_lift(0, 3329), 0);
    assert_eq!(centered_lift(1664, 3329), 1664);
    assert_eq!(centered_lift(1665, 3329), -1664);
    assert_eq!(centered_lift(3328, 3329), -1);

    let kem = ModKEMContext::preset_toy_zero_failure();
    let mut kat_rng = StdRng::seed_from_u64(0x004B_4154);
    let (kem_sk, kem_pk) = kem.keygen_with_rng(&mut kat_rng);
    let (kem_ct, kem_ss1) = kem.encaps_with_rng(&mut kat_rng, &kem_pk);
    let kem_ss2 = kem.decaps(&kem_sk, &kem_ct);
    assert_eq!(kem_ss1, kem_ss2);

    let mut r_poly = Polynomial::zero(4);
    for c in r_poly.coeffs.iter_mut() {
        *c = kat_rng.gen_range(0..97);
    }
    let orig = r_poly.coeffs.clone();
    let ntt_r = table.forward(&r_poly);
    let inv_r = table.inverse(&ntt_r);
    assert_eq!(inv_r.coeffs, orig);
}
