Educational reference implementation of LWE-family cryptography in Rust, with a Lean 4 formalization (`src/LWEBasic.lean`).
Not a production cryptographic library.


- LWE (Regev), Ring-LWE, Module-LWE primitives
- Verifiable Module-LWE PKE and Fujisaki–Okamoto IND-CCA2 KEM
- BFV FHE (including SIMD batch encoding)
- Lattice NIZK / signatures
- Security and decryption-failure estimator
- `no_std` + `alloc` supported


```rust
use lwe_rust::lwe::kem::ModKEMContext;
use rand::{rngs::StdRng, SeedableRng};

let kem = ModKEMContext::preset_standard_128bit();
let mut rng = StdRng::from_entropy();
let (sk, pk) = kem.keygen_with_rng(&mut rng);
let (ct, shared) = kem.encaps_with_rng(&mut rng, &pk);
assert_eq!(kem.decaps(&sk, &ct), shared);
```


```bash
cargo check --no-default-features                # no_std build
cargo test                                       # all tests
cargo test --release --test ct_kat_test          # constant-time checks
cargo test --test estimator_test -- --nocapture  # security estimates
lake build LWEBasic                              # Lean proofs (run from repo root)
```