import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Complex.Basic
import Minkowski

namespace Geometry

open Matrix Set Complex

lemma vec4_0 (v0 v1 v2 v3 : ℂ) : ![v0, v1, v2, v3] 0 = v0 := rfl
lemma vec4_1 (v0 v1 v2 v3 : ℂ) : ![v0, v1, v2, v3] 1 = v1 := rfl
lemma vec4_2 (v0 v1 v2 v3 : ℂ) : ![v0, v1, v2, v3] 2 = v2 := rfl
lemma vec4_3 (v0 v1 v2 v3 : ℂ) : ![v0, v1, v2, v3] 3 = v3 := rfl

noncomputable def givens_xy (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  1, 0, 0, 0;
  0, c, -s, 0;
  0, s, c, 0;
  0, 0, 0, 1
]

lemma givens_xy_is_lorentz (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  (givens_xy c s)ᵀ * minkowskiMetric * (givens_xy c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_xy, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_yz (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  1, 0, 0, 0;
  0, 1, 0, 0;
  0, 0, c, -s;
  0, 0, s, c
]

lemma givens_yz_is_lorentz (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  (givens_yz c s)ᵀ * minkowskiMetric * (givens_yz c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_yz, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_zx (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  1, 0, 0, 0;
  0, c, 0, s;
  0, 0, 1, 0;
  0, -s, 0, c
]

lemma givens_zx_is_lorentz (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  (givens_zx c s)ᵀ * minkowskiMetric * (givens_zx c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_zx, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_t_x (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  c, -s, 0, 0;
  -s, c, 0, 0;
  0, 0, 1, 0;
  0, 0, 0, 1
]

lemma givens_t_x_is_lorentz (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  (givens_t_x c s)ᵀ * minkowskiMetric * (givens_t_x c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_t_x, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_t_y (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  c, 0, -s, 0;
  0, 1, 0, 0;
  -s, 0, c, 0;
  0, 0, 0, 1
]

lemma givens_t_y_is_lorentz (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  (givens_t_y c s)ᵀ * minkowskiMetric * (givens_t_y c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_t_y, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_t_z (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := !![
  c, 0, 0, -s;
  0, 1, 0, 0;
  0, 0, 1, 0;
  -s, 0, 0, c
]

lemma givens_t_z_is_lorentz (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  (givens_t_z c s)ᵀ * minkowskiMetric * (givens_t_z c s) = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_t_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp;
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )


theorem complex_exists_sq (z : ℂ) : ∃ w : ℂ, w ^ 2 = z :=
  ⟨z ^ ((2 : ℕ)⁻¹ : ℂ), Complex.cpow_nat_inv_pow z (by norm_num)⟩



lemma givens_reduce_step (v1 v2 : ℂ) (h : v1 ^ 2 + v2 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c ^ 2 + s ^ 2 = 1 ∧ s * v1 + c * v2 = 0 ∧ (c * v1 - s * v2) ^ 2 = v1 ^ 2 + v2 ^ 2 := by
  
  have ⟨R, hRsq⟩ := complex_exists_sq (v1 ^ 2 + v2 ^ 2)
  have hR_ne_0 : R ≠ 0 := by
    intro H
    rw [H, zero_pow (by decide)] at hRsq
    exact h hRsq.symm
  let c := v1 / R
  let s := -v2 / R
  use c, s
  refine ⟨?_, ?_, ?_⟩
  · calc (v1 / R) ^ 2 + (-v2 / R) ^ 2 = (v1 ^ 2 + v2 ^ 2) / R ^ 2 := by ring
      _ = R ^ 2 / R ^ 2 := by rw [hRsq]
      _ = 1 := div_self (pow_ne_zero 2 hR_ne_0)
  · calc (-v2 / R) * v1 + (v1 / R) * v2 = (-v2 * v1 + v1 * v2) / R := by ring
      _ = 0 / R := by ring
      _ = 0 := zero_div R
  · calc ((v1 / R) * v1 - (-v2 / R) * v2) ^ 2 = ((v1 ^ 2 + v2 ^ 2) / R) ^ 2 := by ring
      _ = (R ^ 2 / R) ^ 2 := by rw [hRsq]
      _ = R ^ 2 := by
        have H : R ^ 2 / R = R := by
          calc R ^ 2 / R = R * R / R := by ring
            _ = R := mul_div_cancel_right₀ R hR_ne_0
        rw [H]
      _ = v1 ^ 2 + v2 ^ 2 := hRsq

lemma isotropic_sum_zero (v1 v2 v3 : ℂ) (h1 : v1 ^ 2 + v2 ^ 2 = 0) (h2 : v2 ^ 2 + v3 ^ 2 = 0) (h3 : v3 ^ 2 + v1 ^ 2 = 0) :
  v1 = 0 ∧ v2 = 0 ∧ v3 = 0 := by
  have H2 : 2 * v2^2 = 0 := by
    calc 2 * v2^2 = (v1^2 + v2^2) + (v2^2 + v3^2) - (v3^2 + v1^2) := by ring
    _ = 0 + 0 - 0 := by rw [h1, h2, h3]
    _ = 0 := by ring
  have Hv2 : v2 = 0 := by
    cases mul_eq_zero.mp H2 with
    | inl h => norm_num at h
    | inr h => exact sq_eq_zero_iff.mp h
  have H1 : 2 * v1^2 = 0 := by
    calc 2 * v1^2 = (v1^2 + v2^2) - (v2^2 + v3^2) + (v3^2 + v1^2) := by ring
    _ = 0 - 0 + 0 := by rw [h1, h2, h3]
    _ = 0 := by ring
  have Hv1 : v1 = 0 := by
    cases mul_eq_zero.mp H1 with
    | inl h => norm_num at h
    | inr h => exact sq_eq_zero_iff.mp h
  have H3 : 2 * v3^2 = 0 := by
    calc 2 * v3^2 = -(v1^2 + v2^2) + (v2^2 + v3^2) + (v3^2 + v1^2) := by ring
    _ = -0 + 0 + 0 := by rw [h1, h2, h3]
    _ = 0 := by ring
  have Hv3 : v3 = 0 := by
    cases mul_eq_zero.mp H3 with
    | inl h => norm_num at h
    | inr h => exact sq_eq_zero_iff.mp h
  exact ⟨Hv1, Hv2, Hv3⟩

lemma givens_xy_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_xy c s) v = ![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] := by
  ext i; dsimp [givens_xy, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_yz_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_yz c s) v = ![v 0, v 1, c * v 2 - s * v 3, s * v 2 + c * v 3] := by
  ext i; dsimp [givens_yz, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_zx_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_zx c s) v = ![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] := by
  ext i; dsimp [givens_zx, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_t_x_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_t_x c s) v = ![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] := by
  ext i; dsimp [givens_t_x, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_t_y_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_t_y c s) v = ![c * v 0 - s * v 2, v 1, -s * v 0 + c * v 2, v 3] := by
  ext i; dsimp [givens_t_y, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_t_z_mulVec (c s : ℂ) (v : Fin 4 → ℂ) :
  mulVec (givens_t_z c s) v = ![c * v 0 - s * v 3, v 1, v 2, -s * v 0 + c * v 3] := by
  ext i; dsimp [givens_t_z, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

def act_xy (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (v0, c * v1 - s * v2, s * v1 + c * v2, v3)

def act_yz (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (v0, v1, c * v2 - s * v3, s * v2 + c * v3)

def act_zx (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (v0, s * v3 + c * v1, v2, c * v3 - s * v1)

def act_tx (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (c * v0 - s * v1, -s * v0 + c * v1, v2, v3)

def act_ty (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (c * v0 - s * v2, v1, -s * v0 + c * v2, v3)

def act_tz (c s v0 v1 v2 v3 : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (c * v0 - s * v3, v1, v2, -s * v0 + c * v3)

lemma reduce_phase2_yz (v0 v1 v2 v3 : ℂ) (hS : v2 ^ 2 + v3 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c^2 + s^2 = 1 ∧ (act_yz c s v0 v1 v2 v3).2.2.2 = 0 ∧ (act_yz c s v0 v1 v2 v3).2.2.1^2 = v2^2 + v3^2 := by
  have ⟨z, hz⟩ := complex_exists_sq (v2^2 + v3^2)
  have hz_ne_0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz
    exact hS hz.symm
  use v2 / z, -v3 / z
  have hcs : (v2 / z)^2 + (-v3 / z)^2 = 1 := by
    calc (v2 / z)^2 + (-v3 / z)^2 = (v2^2 + v3^2) / z^2 := by ring
      _ = z^2 / z^2 := by rw [hz]
      _ = 1 := div_self (by exact (pow_ne_zero 2 hz_ne_0))
  refine ⟨hcs, ?_, ?_⟩
  · dsimp [act_yz]
    calc (-v3 / z) * v2 + (v2 / z) * v3 = (-v3 * v2 + v2 * v3) / z := by ring
      _ = 0 / z := by ring_nf
      _ = 0 := zero_div z
  · dsimp [act_yz]
    calc ((v2 / z) * v2 - (-v3 / z) * v3)^2 = ((v2^2 + v3^2) / z)^2 := by ring
      _ = (z^2 / z)^2 := by rw [hz]
      _ = (z * z / z)^2 := by rw [sq z]
      _ = z^2 := by rw [mul_div_cancel_right₀ z hz_ne_0]
      _ = v2^2 + v3^2 := hz

lemma complex_exists_sq_of_ne_zero {c : ℂ} (hc : c ≠ 0) : ∃ z : ℂ, z^2 = c ∧ z ≠ 0 := by
  obtain ⟨z, hz⟩ := complex_exists_sq c
  refine ⟨z, hz, ?_⟩
  rintro rfl
  rw [zero_pow (by decide)] at hz
  exact hc hz.symm

inductive IsGivens : Matrix (Fin 4) (Fin 4) ℂ → Prop
| xy (c s : ℂ) (h : c^2 + s^2 = 1) : IsGivens (givens_xy c s)
| yz (c s : ℂ) (h : c^2 + s^2 = 1) : IsGivens (givens_yz c s)
| zx (c s : ℂ) (h : c^2 + s^2 = 1) : IsGivens (givens_zx c s)
| tx (c s : ℂ) (h : c^2 - s^2 = 1) : IsGivens (givens_t_x c s)
| ty (c s : ℂ) (h : c^2 - s^2 = 1) : IsGivens (givens_t_y c s)
| tz (c s : ℂ) (h : c^2 - s^2 = 1) : IsGivens (givens_t_z c s)
| one : IsGivens 1
| mul {A B} (hA : IsGivens A) (hB : IsGivens B) : IsGivens (A * B)

lemma mulVec_mulVec (v : Fin 4 → ℂ) (G1 G2 : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.mulVec (G1 * G2) v = Matrix.mulVec G1 (Matrix.mulVec G2 v) := by
  rw [Matrix.mulVec_mulVec]

lemma IsGivens_preserves_mass_shell {G} (hG : IsGivens G) (v : Fin 4 → ℂ) :
  (Matrix.mulVec G v) 0 ^ 2 - ((Matrix.mulVec G v) 1 ^ 2 + (Matrix.mulVec G v) 2 ^ 2 + (Matrix.mulVec G v) 3 ^ 2) =
  v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
  induction hG generalizing v with
  | xy c s h =>
    rw [givens_xy_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc v 0 ^ 2 - ((c * v 1 - s * v 2) ^ 2 + (s * v 1 + c * v 2) ^ 2 + v 3 ^ 2)
      = v 0 ^ 2 - ((c^2 + s^2) * (v 1 ^ 2 + v 2 ^ 2) + v 3 ^ 2) := by ring
      _ = v 0 ^ 2 - (1 * (v 1 ^ 2 + v 2 ^ 2) + v 3 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | yz c s h =>
    rw [givens_yz_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc v 0 ^ 2 - (v 1 ^ 2 + (c * v 2 - s * v 3) ^ 2 + (s * v 2 + c * v 3) ^ 2)
      = v 0 ^ 2 - (v 1 ^ 2 + (c^2 + s^2) * (v 2 ^ 2 + v 3 ^ 2)) := by ring
      _ = v 0 ^ 2 - (v 1 ^ 2 + 1 * (v 2 ^ 2 + v 3 ^ 2)) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | zx c s h =>
    rw [givens_zx_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc v 0 ^ 2 - ((c * v 1 + s * v 3) ^ 2 + v 2 ^ 2 + (-s * v 1 + c * v 3) ^ 2)
      = v 0 ^ 2 - ((c^2 + s^2) * (v 1 ^ 2 + v 3 ^ 2) + v 2 ^ 2) := by ring
      _ = v 0 ^ 2 - (1 * (v 1 ^ 2 + v 3 ^ 2) + v 2 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | tx c s h =>
    rw [givens_t_x_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc (c * v 0 - s * v 1) ^ 2 - ((-s * v 0 + c * v 1) ^ 2 + v 2 ^ 2 + v 3 ^ 2)
      = (c^2 - s^2) * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by ring
      _ = 1 * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | ty c s h =>
    rw [givens_t_y_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc (c * v 0 - s * v 2) ^ 2 - (v 1 ^ 2 + (-s * v 0 + c * v 2) ^ 2 + v 3 ^ 2)
      = (c^2 - s^2) * (v 0 ^ 2 - v 2 ^ 2) - (v 1 ^ 2 + v 3 ^ 2) := by ring
      _ = 1 * (v 0 ^ 2 - v 2 ^ 2) - (v 1 ^ 2 + v 3 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | tz c s h =>
    rw [givens_t_z_mulVec, vec4_0, vec4_1, vec4_2, vec4_3]
    calc (c * v 0 - s * v 3) ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + (-s * v 0 + c * v 3) ^ 2)
      = (c^2 - s^2) * (v 0 ^ 2 - v 3 ^ 2) - (v 1 ^ 2 + v 2 ^ 2) := by ring
      _ = 1 * (v 0 ^ 2 - v 3 ^ 2) - (v 1 ^ 2 + v 2 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | one =>
    rw [Matrix.one_mulVec]
  | mul h1 h2 ih1 ih2 =>
    rw [mulVec_mulVec, ih1, ih2]

lemma is_givens_xy_swap : IsGivens (givens_xy 0 1) := by
  have : (0:ℂ)^2 + (1:ℂ)^2 = 1 := by norm_num
  exact IsGivens.xy 0 1 this

lemma is_givens_yz_swap : IsGivens (givens_yz 0 1) := by
  have : (0:ℂ)^2 + (1:ℂ)^2 = 1 := by norm_num
  exact IsGivens.yz 0 1 this

lemma is_givens_zx_swap : IsGivens (givens_zx 0 1) := by
  have : (0:ℂ)^2 + (1:ℂ)^2 = 1 := by norm_num
  exact IsGivens.zx 0 1 this

def PreservesE0 (G : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Matrix.mulVec G ![1, 0, 0, 0] = ![1, 0, 0, 0]

def PreservesE1 (G : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Matrix.mulVec G ![0, 1, 0, 0] = ![0, 1, 0, 0]

lemma PreservesE0_mul {A B : Matrix (Fin 4) (Fin 4) ℂ} (hA : PreservesE0 A) (hB : PreservesE0 B) : PreservesE0 (A * B) := by
  dsimp [PreservesE0] at *
  rw [mulVec_mulVec, hB, hA]

lemma PreservesE1_mul {A B : Matrix (Fin 4) (Fin 4) ℂ} (hA : PreservesE1 A) (hB : PreservesE1 B) : PreservesE1 (A * B) := by
  dsimp [PreservesE1] at *
  rw [mulVec_mulVec, hB, hA]

lemma givens_xy_PreservesE0 (c s : ℂ) : PreservesE0 (givens_xy c s) := by
  dsimp [PreservesE0]
  ext i; fin_cases i <;> simp [givens_xy_mulVec, vec4_2, vec4_3]

lemma givens_yz_PreservesE0 (c s : ℂ) : PreservesE0 (givens_yz c s) := by
  dsimp [PreservesE0]
  ext i; fin_cases i <;> simp [givens_yz_mulVec, vec4_2, vec4_3]

lemma givens_zx_PreservesE0 (c s : ℂ) : PreservesE0 (givens_zx c s) := by
  dsimp [PreservesE0]
  ext i; fin_cases i <;> simp [givens_zx_mulVec, vec4_2, vec4_3]

lemma givens_yz_PreservesE1 (c s : ℂ) : PreservesE1 (givens_yz c s) := by
  dsimp [PreservesE1]
  ext i; fin_cases i <;> simp [givens_yz_mulVec, vec4_2, vec4_3]

lemma extract_col0 (G M1 M2 : Matrix (Fin 4) (Fin 4) ℂ)
  (h_M2 : M2 = G * M1)
  (h_M1_col0 : ∀ i, M1 i 0 = if i = 0 then 1 else 0)
  (hG : PreservesE0 G) :
  ∀ i, M2 i 0 = if i = 0 then 1 else 0 := by
  intro i
  have h_col : (fun j => M1 j 0) = ![1, 0, 0, 0] := by
    ext j; fin_cases j <;> simp [h_M1_col0]
  have H : M2 i 0 = (Matrix.mulVec G (fun j => M1 j 0)) i := by
    calc M2 i 0 = (G * M1) i 0 := by rw [h_M2]
      _ = (Matrix.mulVec G (fun j => M1 j 0)) i := rfl
  rw [H, h_col, hG]
  fin_cases i <;> rfl

lemma extract_col1 (G M1 M2 : Matrix (Fin 4) (Fin 4) ℂ)
  (h_M2 : M2 = G * M1)
  (h_M1_col1 : ∀ i, M1 i 1 = if i = 1 then 1 else 0)
  (hG : PreservesE1 G) :
  ∀ i, M2 i 1 = if i = 1 then 1 else 0 := by
  intro i
  have h_col : (fun j => M1 j 1) = ![0, 1, 0, 0] := by
    ext j; fin_cases j <;> simp [h_M1_col1]
  have H : M2 i 1 = (Matrix.mulVec G (fun j => M1 j 1)) i := by
    calc M2 i 1 = (G * M1) i 1 := by rw [h_M2]
      _ = (Matrix.mulVec G (fun j => M1 j 1)) i := rfl
  rw [H, h_col, hG]
  fin_cases i <;> rfl

lemma reduce_phase2_zx (v0 v1 v2 v3 : ℂ) (hS : v1 ^ 2 + v3 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c^2 + s^2 = 1 ∧ (act_zx c s v0 v1 v2 v3).2.2.2 = 0 ∧ (act_zx c s v0 v1 v2 v3).2.1^2 = v1^2 + v3^2 := by
  have ⟨z, hz⟩ := complex_exists_sq (v1^2 + v3^2)
  have hz_ne_0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz
    exact hS hz.symm
  use v1 / z, v3 / z
  have hcs : (v1 / z)^2 + (v3 / z)^2 = 1 := by
    calc (v1 / z)^2 + (v3 / z)^2 = (v1^2 + v3^2) / z^2 := by ring
      _ = z^2 / z^2 := by rw [hz]
      _ = 1 := div_self (by exact (pow_ne_zero 2 hz_ne_0))
  refine ⟨hcs, ?_, ?_⟩
  · dsimp [act_zx]
    calc (v1 / z) * v3 - (v3 / z) * v1 = (v1 * v3 - v3 * v1) / z := by ring
      _ = 0 / z := by ring_nf
      _ = 0 := zero_div z
  · dsimp [act_zx]
    calc (v3 / z * v3 + (v1 / z) * v1)^2 = ((v1^2 + v3^2) / z)^2 := by ring
      _ = (z^2 / z)^2 := by rw [hz]
      _ = (z * z / z)^2 := by rw [sq z]
      _ = z^2 := by rw [mul_div_cancel_right₀ z hz_ne_0]
      _ = v1^2 + v3^2 := hz

lemma reduce_v2_to_zero_xy (v0 v1 v2 v3 : ℂ) (hS : v1 ^ 2 + v2 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c^2 + s^2 = 1 ∧ (act_xy c s v0 v1 v2 v3).2.2.1 = 0 ∧ (act_xy c s v0 v1 v2 v3).2.1^2 = v1^2 + v2^2 := by
  have ⟨z, hz⟩ := complex_exists_sq (v1^2 + v2^2)
  have hz_ne_0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz
    exact hS hz.symm
  use v1 / z, -v2 / z
  have hcs : (v1 / z)^2 + (-v2 / z)^2 = 1 := by
    calc (v1 / z)^2 + (-v2 / z)^2 = (v1^2 + v2^2) / z^2 := by ring
      _ = z^2 / z^2 := by rw [hz]
      _ = 1 := div_self (by exact (pow_ne_zero 2 hz_ne_0))
  refine ⟨hcs, ?_, ?_⟩
  · dsimp [act_xy]
    calc (-v2 / z) * v1 + (v1 / z) * v2 = (-v2 * v1 + v1 * v2) / z := by ring
      _ = 0 / z := by ring_nf
      _ = 0 := zero_div z
  · dsimp [act_xy]
    calc ((v1 / z) * v1 - (-v2 / z) * v2)^2 = ((v1^2 + v2^2) / z)^2 := by ring
      _ = (z^2 / z)^2 := by rw [hz]
      _ = (z * z / z)^2 := by rw [sq z]
      _ = z^2 := by rw [mul_div_cancel_right₀ z hz_ne_0]
      _ = v1^2 + v2^2 := hz

lemma reduce_spatial_path1 (v : Fin 4 → ℂ) (h12 : v 1 ^ 2 + v 2 ^ 2 ≠ 0) (hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ let v' := mulVec G v; v' 2 = 0 ∧ v' 3 = 0 ∧ v' 1 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  have ⟨c1, s1, hc1, hxy_v2, hxy_v1⟩ := reduce_v2_to_zero_xy (v 0) (v 1) (v 2) (v 3) h12
  let G1 := givens_xy c1 s1
  let v' := mulVec G1 v
  have hv'_2 : v' 2 = 0 := by
    dsimp [v', G1]
    rw [givens_xy_mulVec]
    exact hxy_v2
  have hv'_1 : v' 1 ^ 2 = v 1 ^ 2 + v 2 ^ 2 := by
    dsimp [v', G1]
    rw [givens_xy_mulVec]
    exact hxy_v1
  have hv'_3 : v' 3 = v 3 := by
    dsimp [v', G1]
    rw [givens_xy_mulVec]
    rfl
  have hv'_13 : v' 1 ^ 2 + v' 3 ^ 2 ≠ 0 := by rw [hv'_1, hv'_3]; exact hS
  have ⟨c2, s2, hc2, hzx_v3, hzx_v1⟩ := reduce_phase2_zx (v' 0) (v' 1) (v' 2) (v' 3) hv'_13
  let G2 := givens_zx c2 s2
  use G2 * G1
  refine ⟨IsGivens.mul (IsGivens.zx c2 s2 hc2) (IsGivens.xy c1 s1 hc1), PreservesE0_mul (givens_zx_PreservesE0 c2 s2) (givens_xy_PreservesE0 c1 s1), ?_⟩
  dsimp only
  have hv'' : mulVec (G2 * G1) v = mulVec G2 v' := mulVec_mulVec v G2 G1
  rw [hv'']
  refine ⟨?_, ?_, ?_⟩
  · rw [givens_zx_mulVec]
    exact hv'_2
  · rw [givens_zx_mulVec]
    have h : -s2 * v' 1 + c2 * v' 3 = 0 := by
      calc -s2 * v' 1 + c2 * v' 3 = c2 * v' 3 - s2 * v' 1 := by ring
        _ = (act_zx c2 s2 (v' 0) (v' 1) (v' 2) (v' 3)).2.2.2 := rfl
        _ = 0 := hzx_v3
    exact h
  · rw [givens_zx_mulVec]
    calc (c2 * v' 1 + s2 * v' 3) ^ 2 = (s2 * v' 3 + c2 * v' 1) ^ 2 := by ring
      _ = (act_zx c2 s2 (v' 0) (v' 1) (v' 2) (v' 3)).2.1 ^ 2 := rfl
      _ = v' 1 ^ 2 + v' 3 ^ 2 := hzx_v1
      _ = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by rw [hv'_1, hv'_3]

lemma reduce_spatial_path2 (v : Fin 4 → ℂ) (h23 : v 2 ^ 2 + v 3 ^ 2 ≠ 0) (hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ let v' := mulVec G v; v' 2 = 0 ∧ v' 3 = 0 ∧ v' 1 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  have ⟨c1, s1, hc1, hyz_v3, hyz_v2⟩ := reduce_phase2_yz (v 0) (v 1) (v 2) (v 3) h23
  let G1 := givens_yz c1 s1
  let v' := mulVec G1 v
  have hv'_3 : v' 3 = 0 := by
    dsimp [v', G1]
    rw [givens_yz_mulVec]
    exact hyz_v3
  have hv'_2 : v' 2 ^ 2 = v 2 ^ 2 + v 3 ^ 2 := by
    dsimp [v', G1]
    rw [givens_yz_mulVec]
    exact hyz_v2
  have hv'_1 : v' 1 = v 1 := by
    dsimp [v', G1]
    rw [givens_yz_mulVec]
    rfl
  have hv'_12 : v' 1 ^ 2 + v' 2 ^ 2 ≠ 0 := by
    rw [hv'_1, hv'_2]
    have h : v 1 ^ 2 + (v 2 ^ 2 + v 3 ^ 2) = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring
    rw [h]
    exact hS
  have ⟨c2, s2, hc2, hxy_v2, hxy_v1⟩ := reduce_v2_to_zero_xy (v' 0) (v' 1) (v' 2) (v' 3) hv'_12
  let G2 := givens_xy c2 s2
  use G2 * G1
  refine ⟨IsGivens.mul (IsGivens.xy c2 s2 hc2) (IsGivens.yz c1 s1 hc1), PreservesE0_mul (givens_xy_PreservesE0 c2 s2) (givens_yz_PreservesE0 c1 s1), ?_⟩
  dsimp only
  have hv'' : mulVec (G2 * G1) v = mulVec G2 v' := mulVec_mulVec v G2 G1
  rw [hv'']
  refine ⟨?_, ?_, ?_⟩
  · rw [givens_xy_mulVec]
    exact hxy_v2
  · rw [givens_xy_mulVec]
    exact hv'_3
  · rw [givens_xy_mulVec]
    calc (c2 * v' 1 - s2 * v' 2) ^ 2 = (act_xy c2 s2 (v' 0) (v' 1) (v' 2) (v' 3)).2.1 ^ 2 := rfl
      _ = v' 1 ^ 2 + v' 2 ^ 2 := hxy_v1
      _ = v 1 ^ 2 + (v 2 ^ 2 + v 3 ^ 2) := by rw [hv'_1, hv'_2]
      _ = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring

lemma reduce_spatial_path3 (v : Fin 4 → ℂ) (h13 : v 1 ^ 2 + v 3 ^ 2 ≠ 0) (hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ let v' := mulVec G v; v' 2 = 0 ∧ v' 3 = 0 ∧ v' 1 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  have ⟨c1, s1, hc1, hzx_v3, hzx_v1⟩ := reduce_phase2_zx (v 0) (v 1) (v 2) (v 3) h13
  let G1 := givens_zx c1 s1
  let v' := mulVec G1 v
  have hv'_3 : v' 3 = 0 := by
    dsimp [v', G1]
    rw [givens_zx_mulVec]
    have h : -s1 * v 1 + c1 * v 3 = 0 := by
      calc -s1 * v 1 + c1 * v 3 = c1 * v 3 - s1 * v 1 := by ring
        _ = (act_zx c1 s1 (v 0) (v 1) (v 2) (v 3)).2.2.2 := rfl
        _ = 0 := hzx_v3
    exact h
  have hv'_1 : v' 1 ^ 2 = v 1 ^ 2 + v 3 ^ 2 := by
    dsimp [v', G1]
    rw [givens_zx_mulVec]
    calc (c1 * v 1 + s1 * v 3) ^ 2 = (s1 * v 3 + c1 * v 1) ^ 2 := by ring
      _ = (act_zx c1 s1 (v 0) (v 1) (v 2) (v 3)).2.1 ^ 2 := rfl
      _ = v 1 ^ 2 + v 3 ^ 2 := hzx_v1
  have hv'_2 : v' 2 = v 2 := by
    dsimp [v', G1]
    rw [givens_zx_mulVec]
    rfl
  have hv'_12 : v' 1 ^ 2 + v' 2 ^ 2 ≠ 0 := by
    rw [hv'_1, hv'_2]
    have h : v 1 ^ 2 + v 3 ^ 2 + v 2 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring
    rw [h]
    exact hS
  have ⟨c2, s2, hc2, hxy_v2, hxy_v1⟩ := reduce_v2_to_zero_xy (v' 0) (v' 1) (v' 2) (v' 3) hv'_12
  let G2 := givens_xy c2 s2
  use G2 * G1
  refine ⟨IsGivens.mul (IsGivens.xy c2 s2 hc2) (IsGivens.zx c1 s1 hc1), PreservesE0_mul (givens_xy_PreservesE0 c2 s2) (givens_zx_PreservesE0 c1 s1), ?_⟩
  dsimp only
  have hv'' : mulVec (G2 * G1) v = mulVec G2 v' := mulVec_mulVec v G2 G1
  rw [hv'']
  refine ⟨?_, ?_, ?_⟩
  · rw [givens_xy_mulVec]
    exact hxy_v2
  · rw [givens_xy_mulVec]
    exact hv'_3
  · rw [givens_xy_mulVec]
    calc (c2 * v' 1 - s2 * v' 2) ^ 2 = (act_xy c2 s2 (v' 0) (v' 1) (v' 2) (v' 3)).2.1 ^ 2 := rfl
      _ = v' 1 ^ 2 + v' 2 ^ 2 := hxy_v1
      _ = (v 1 ^ 2 + v 3 ^ 2) + v 2 ^ 2 := by rw [hv'_1, hv'_2]
      _ = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring

lemma reduce_spatial_to_zero (v : Fin 4 → ℂ) (hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ let v' := mulVec G v; v' 2 = 0 ∧ v' 3 = 0 ∧ v' 1 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  by_cases h12 : v 1 ^ 2 + v 2 ^ 2 ≠ 0
  · exact reduce_spatial_path1 v h12 hS
  · push_neg at h12
    by_cases h23 : v 2 ^ 2 + v 3 ^ 2 ≠ 0
    · exact reduce_spatial_path2 v h23 hS
    · push_neg at h23
      have h13 : v 1 ^ 2 + v 3 ^ 2 ≠ 0 := by
        intro h13
        have h1 : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0 + 0 + 0 := by
          calc v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = (v 1 ^ 2 + v 2 ^ 2) + (v 2 ^ 2 + v 3 ^ 2) + (v 1 ^ 2 + v 3 ^ 2) := by ring
            _ = 0 + 0 + 0 := by rw [h12, h23, h13]
        
        have h2 : (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * 2 = 0 := by
          calc (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring
            _ = 0 + 0 + 0 := h1
            _ = 0 := by ring
        have h3 : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0 := by
          calc v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = ((v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * 2) / 2 := by ring
            _ = 0 / 2 := by rw [h2]
            _ = 0 := by ring
        exact hS h3
      exact reduce_spatial_path3 v h13 hS

lemma reduce_phase3 (v0 r : ℂ) (h : v0 ^ 2 - r ^ 2 = 1) :
  act_tx v0 r v0 r 0 0 = (1, 0, 0, 0) := by
  simp [act_tx]
  constructor
  · calc v0 * v0 - r * r = v0 ^ 2 - r ^ 2 := by ring
      _ = 1 := h
  · ring

lemma reduce_phase2 (v0 v1 v2 : ℂ) (h : v1 ^ 2 + v2 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c ^ 2 + s ^ 2 = 1 ∧ (act_xy c s v0 v1 v2 0).2.2.1 = 0 ∧ (act_xy c s v0 v1 v2 0).2.1 ^ 2 = v1 ^ 2 + v2 ^ 2 := by
  have ⟨c, s, hcs, hzero, hsq⟩ := givens_reduce_step v1 v2 h
  use c, s
  refine ⟨hcs, ?_, ?_⟩
  · simp [act_xy]
    exact hzero
  · simp [act_xy]
    exact hsq

lemma reduce_phase1 (v0 v1 v2 v3 : ℂ) (h1 : v0 ^ 2 - (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) = 1) (hS : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 0) (hv1_ne : v1 ^ 2 ≠ 1) (hv1_ne_0 : v1 ^ 2 ≠ 0) :
  ∃ c s : ℂ, c ^ 2 - s ^ 2 = 1 ∧ (-s * v0 + c * v1) ^ 2 + v2 ^ 2 + v3 ^ 2 ≠ 0 := by
  have hv0 : v0 ^ 2 = 1 := by
    calc v0 ^ 2 = v0 ^ 2 - (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) + (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by ring
      _ = 1 + 0 := by rw [h1, hS]
      _ = 1 := by ring
  have h_den : 1 - v1 ^ 2 ≠ 0 := by
    intro H
    have : v1 ^ 2 = 1 := by
      calc v1 ^ 2 = 1 - (1 - v1 ^ 2) := by ring
        _ = 1 - 0 := by rw [H]
        _ = 1 := by ring
    exact hv1_ne this
  have ⟨c, hc⟩ := complex_exists_sq (1 / (1 - v1 ^ 2))
  have hc_ne_0 : c ≠ 0 := by
    intro H
    rw [H, zero_pow (by decide)] at hc
    have : (1 : ℂ) / (1 - v1 ^ 2) = 0 := hc.symm
    have Hdiv := div_eq_zero_iff.mp this
    cases Hdiv with
    | inl h => norm_num at h
    | inr h => exact h_den h
  have hc_sq_ne_0 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc_ne_0
  have hc_sq : c ^ 2 = 1 / (1 - v1 ^ 2) := hc
  have hv0_ne_0 : v0 ≠ 0 := by
    intro H
    rw [H, zero_pow (by decide)] at hv0
    norm_num at hv0
  let s := c * v1 / v0
  use c, s
  have hcs : c ^ 2 - s ^ 2 = 1 := by
    calc c ^ 2 - s ^ 2 = c ^ 2 - (c * v1 / v0) ^ 2 := rfl
      _ = c ^ 2 - c ^ 2 * v1 ^ 2 / v0 ^ 2 := by ring
      _ = c ^ 2 - c ^ 2 * v1 ^ 2 / 1 := by rw [hv0]
      _ = c ^ 2 * (1 - v1 ^ 2) := by ring
      _ = (1 / (1 - v1 ^ 2)) * (1 - v1 ^ 2) := by rw [hc_sq]
      _ = 1 := div_mul_cancel₀ 1 h_den
  refine ⟨hcs, ?_⟩
  intro H'
  have Hzero : -s * v0 + c * v1 = 0 := by
    calc -s * v0 + c * v1 = -(c * v1 / v0) * v0 + c * v1 := rfl
      _ = -c * v1 * (v0 / v0) + c * v1 := by ring
      _ = -c * v1 * 1 + c * v1 := by rw [div_self hv0_ne_0]
      _ = 0 := by ring
  rw [Hzero, zero_pow (by decide), zero_add] at H'
  have H2 : v1 ^ 2 = 0 := by
    calc v1 ^ 2 = (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) - (v2 ^ 2 + v3 ^ 2) := by ring
      _ = 0 - 0 := by rw [hS, H']
      _ = 0 := by ring
  exact hv1_ne_0 H2

lemma exists_good_component (v1 v2 v3 : ℂ) (hS : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 0) (h_not_all : ¬(v1 = 0 ∧ v2 = 0 ∧ v3 = 0)) :
  (v1^2 ≠ 0 ∧ v1^2 ≠ 1) ∨ (v2^2 ≠ 0 ∧ v2^2 ≠ 1) ∨ (v3^2 ≠ 0 ∧ v3^2 ≠ 1) := by
  by_cases h1 : v1^2 = 0 ∨ v1^2 = 1
  swap; · exact Or.inl (not_or.mp h1)
  by_cases h2 : v2^2 = 0 ∨ v2^2 = 1
  swap; · exact Or.inr (Or.inl (not_or.mp h2))
  by_cases h3 : v3^2 = 0 ∨ v3^2 = 1
  swap; · exact Or.inr (Or.inr (not_or.mp h3))
  exfalso
  rcases h1 with h1_0 | h1_1
  · rcases h2 with h2_0 | h2_1
    · rcases h3 with h3_0 | h3_1
      · have hv1 : v1 = 0 := sq_eq_zero_iff.mp h1_0
        have hv2 : v2 = 0 := sq_eq_zero_iff.mp h2_0
        have hv3 : v3 = 0 := sq_eq_zero_iff.mp h3_0
        exact h_not_all ⟨hv1, hv2, hv3⟩
      · have H : (0 : ℂ) + 0 + 1 = 0 := by
          calc (0 : ℂ) + 0 + 1 = v1^2 + v2^2 + v3^2 := by rw [h1_0, h2_0, h3_1]
            _ = 0 := hS
        norm_num at H
    · rcases h3 with h3_0 | h3_1
      · have H : (0 : ℂ) + 1 + 0 = 0 := by
          calc (0 : ℂ) + 1 + 0 = v1^2 + v2^2 + v3^2 := by rw [h1_0, h2_1, h3_0]
            _ = 0 := hS
        norm_num at H
      · have H : (0 : ℂ) + 1 + 1 = 0 := by
          calc (0 : ℂ) + 1 + 1 = v1^2 + v2^2 + v3^2 := by rw [h1_0, h2_1, h3_1]
            _ = 0 := hS
        norm_num at H
  · rcases h2 with h2_0 | h2_1
    · rcases h3 with h3_0 | h3_1
      · have H : (1 : ℂ) + 0 + 0 = 0 := by
          calc (1 : ℂ) + 0 + 0 = v1^2 + v2^2 + v3^2 := by rw [h1_1, h2_0, h3_0]
            _ = 0 := hS
        norm_num at H
      · have H : (1 : ℂ) + 0 + 1 = 0 := by
          calc (1 : ℂ) + 0 + 1 = v1^2 + v2^2 + v3^2 := by rw [h1_1, h2_0, h3_1]
            _ = 0 := hS
        norm_num at H
    · rcases h3 with h3_0 | h3_1
      · have H : (1 : ℂ) + 1 + 0 = 0 := by
          calc (1 : ℂ) + 1 + 0 = v1^2 + v2^2 + v3^2 := by rw [h1_1, h2_1, h3_0]
            _ = 0 := hS
        norm_num at H
      · have H : (1 : ℂ) + 1 + 1 = 0 := by
          calc (1 : ℂ) + 1 + 1 = v1^2 + v2^2 + v3^2 := by rw [h1_1, h2_1, h3_1]
            _ = 0 := hS
        norm_num at H

lemma reduce_isotropic_to_non_isotropic (v : Fin 4 → ℂ) (h1 : v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) = 1) (hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0) (h_not_all : ¬(v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0)) :
  ∃ G, IsGivens G ∧ let v' := mulVec G v; v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2 ≠ 0 ∧ v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = 1 := by
  have Hgood := exists_good_component (v 1) (v 2) (v 3) hS h_not_all
  rcases Hgood with ⟨hv1_0, hv1_1⟩ | ⟨hv2_0, hv2_1⟩ | ⟨hv3_0, hv3_1⟩
  · have ⟨c, s, hcs, hS'⟩ := reduce_phase1 (v 0) (v 1) (v 2) (v 3) h1 hS hv1_1 hv1_0
    use givens_t_x c s
    refine ⟨IsGivens.tx c s hcs, ?_⟩
    dsimp only
    rw [givens_t_x_mulVec]
    refine ⟨hS', ?_⟩
    calc (c * v 0 - s * v 1) ^ 2 - ((-s * v 0 + c * v 1) ^ 2 + v 2 ^ 2 + v 3 ^ 2) = (c^2 - s^2) * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by ring
      _ = 1 * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by rw [hcs]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
      _ = 1 := h1
  · let G1 := givens_xy 0 (-1)
    have hG1 : IsGivens G1 := by apply IsGivens.xy; ring
    let v' := mulVec G1 v
    have hv'_0 : v' 0 = v 0 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_0]
    have hv'_1 : v' 1 = v 2 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_1]; ring
    have hv'_2 : v' 2 = -v 1 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_2]; ring
    have hv'_3 : v' 3 = v 3 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_3]
    have h1' : v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = 1 := by
      rw [hv'_0, hv'_1, hv'_2, hv'_3]
      calc v 0 ^ 2 - (v 2 ^ 2 + (-v 1) ^ 2 + v 3 ^ 2) = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
        _ = 1 := h1
    have hS' : v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2 = 0 := by
      rw [hv'_1, hv'_2, hv'_3]
      calc v 2 ^ 2 + (-v 1) ^ 2 + v 3 ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring
        _ = 0 := hS
    have ⟨c, s, hcs, hS''⟩ := reduce_phase1 (v' 0) (v' 1) (v' 2) (v' 3) h1' hS' (by rw [hv'_1]; exact hv2_1) (by rw [hv'_1]; exact hv2_0)
    use givens_t_x c s * G1
    refine ⟨IsGivens.mul (IsGivens.tx c s hcs) hG1, ?_⟩
    dsimp only
    rw [mulVec_mulVec, givens_t_x_mulVec]
    refine ⟨hS'', ?_⟩
    calc (c * v' 0 - s * v' 1) ^ 2 - ((-s * v' 0 + c * v' 1) ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = (c^2 - s^2) * (v' 0 ^ 2 - v' 1 ^ 2) - (v' 2 ^ 2 + v' 3 ^ 2) := by ring
      _ = 1 * (v' 0 ^ 2 - v' 1 ^ 2) - (v' 2 ^ 2 + v' 3 ^ 2) := by rw [hcs]
      _ = v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) := by ring
      _ = 1 := h1'
  · let G1 := givens_zx 0 1
    have hG1 : IsGivens G1 := by apply IsGivens.zx; ring
    let v' := mulVec G1 v
    have hv'_0 : v' 0 = v 0 := by dsimp [v', G1]; rw [givens_zx_mulVec, vec4_0]
    have hv'_1 : v' 1 = v 3 := by dsimp [v', G1]; rw [givens_zx_mulVec, vec4_1]; ring
    have hv'_2 : v' 2 = v 2 := by dsimp [v', G1]; rw [givens_zx_mulVec, vec4_2]
    have hv'_3 : v' 3 = -v 1 := by dsimp [v', G1]; rw [givens_zx_mulVec, vec4_3]; ring
    have h1' : v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = 1 := by
      rw [hv'_0, hv'_1, hv'_2, hv'_3]
      calc v 0 ^ 2 - (v 3 ^ 2 + v 2 ^ 2 + (-v 1) ^ 2) = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
        _ = 1 := h1
    have hS' : v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2 = 0 := by
      rw [hv'_1, hv'_2, hv'_3]
      calc v 3 ^ 2 + v 2 ^ 2 + (-v 1) ^ 2 = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by ring
        _ = 0 := hS
    have ⟨c, s, hcs, hS''⟩ := reduce_phase1 (v' 0) (v' 1) (v' 2) (v' 3) h1' hS' (by rw [hv'_1]; exact hv3_1) (by rw [hv'_1]; exact hv3_0)
    use givens_t_x c s * G1
    refine ⟨IsGivens.mul (IsGivens.tx c s hcs) hG1, ?_⟩
    dsimp only
    rw [mulVec_mulVec, givens_t_x_mulVec]
    refine ⟨hS'', ?_⟩
    calc (c * v' 0 - s * v' 1) ^ 2 - ((-s * v' 0 + c * v' 1) ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = (c^2 - s^2) * (v' 0 ^ 2 - v' 1 ^ 2) - (v' 2 ^ 2 + v' 3 ^ 2) := by ring
      _ = 1 * (v' 0 ^ 2 - v' 1 ^ 2) - (v' 2 ^ 2 + v' 3 ^ 2) := by rw [hcs]
      _ = v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) := by ring
      _ = 1 := h1'


lemma reduce_to_e0 (v : Fin 4 → ℂ) (h : v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) = 1) :
  ∃ G, IsGivens G ∧ mulVec G v = ![1, 0, 0, 0] := by
  by_cases hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0
  · by_cases h_all : v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0
    · have hv0 : v 0 ^ 2 = 1 := by
        calc v 0 ^ 2 = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) + (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
          _ = 1 + 0 := by rw [h, hS]
          _ = 1 := by ring
      use givens_t_x (v 0) 0
      refine ⟨IsGivens.tx (v 0) 0 (by rw [zero_pow (by decide), sub_zero]; exact hv0), ?_⟩
      ext i; fin_cases i
      · change (givens_t_x (v 0) 0 *ᵥ v) 0 = 1
        simp only [givens_t_x_mulVec, vec4_0]; linear_combination hv0
      · change (givens_t_x (v 0) 0 *ᵥ v) 1 = 0
        simp only [givens_t_x_mulVec, vec4_1]; rw [h_all.1]; ring
      · change (givens_t_x (v 0) 0 *ᵥ v) 2 = 0
        simp only [givens_t_x_mulVec, vec4_2]; exact h_all.2.1
      · change (givens_t_x (v 0) 0 *ᵥ v) 3 = 0
        simp only [givens_t_x_mulVec, vec4_3]; exact h_all.2.2
    · have ⟨G1, hG1, h_prop⟩ := reduce_isotropic_to_non_isotropic v h hS h_all
      have hS' : (mulVec G1 v) 1 ^ 2 + (mulVec G1 v) 2 ^ 2 + (mulVec G1 v) 3 ^ 2 ≠ 0 := h_prop.1
      have ⟨G2, hG2, hv'⟩ := reduce_spatial_to_zero (mulVec G1 v) hS'
      let v'' := mulVec G2 (mulVec G1 v)
      have h_mass : v'' 0 ^ 2 - (v'' 1 ^ 2 + v'' 2 ^ 2 + v'' 3 ^ 2) = 1 := by
        calc v'' 0 ^ 2 - (v'' 1 ^ 2 + v'' 2 ^ 2 + v'' 3 ^ 2)
          = (mulVec (G2 * G1) v) 0 ^ 2 - ((mulVec (G2 * G1) v) 1 ^ 2 + (mulVec (G2 * G1) v) 2 ^ 2 + (mulVec (G2 * G1) v) 3 ^ 2) := by dsimp [v'']; rw [←mulVec_mulVec]
          _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := IsGivens_preserves_mass_shell (IsGivens.mul hG2 hG1) v
          _ = 1 := h
      have hv''0 : v'' 0 ^ 2 - v'' 1 ^ 2 = 1 := by
        calc v'' 0 ^ 2 - v'' 1 ^ 2 = v'' 0 ^ 2 - (v'' 1 ^ 2 + v'' 2 ^ 2 + v'' 3 ^ 2) := by dsimp [v'']; rw [hv'.2.1, hv'.2.2.1]; ring
          _ = 1 := h_mass
      use givens_t_x (v'' 0) (v'' 1) * (G2 * G1)
      refine ⟨IsGivens.mul (IsGivens.tx (v'' 0) (v'' 1) hv''0) (IsGivens.mul hG2 hG1), ?_⟩
      ext i; fin_cases i
      · change ((givens_t_x (v'' 0) (v'' 1) * (G2 * G1)) *ᵥ v) 0 = 1
        simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_0]; linear_combination hv''0
      · change ((givens_t_x (v'' 0) (v'' 1) * (G2 * G1)) *ᵥ v) 1 = 0
        simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_1]; ring
      · change ((givens_t_x (v'' 0) (v'' 1) * (G2 * G1)) *ᵥ v) 2 = 0
        simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_2]; exact hv'.2.1
      · change ((givens_t_x (v'' 0) (v'' 1) * (G2 * G1)) *ᵥ v) 3 = 0
        simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_3]; exact hv'.2.2.1
  · have hS_ne : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0 := hS
    have ⟨G1, hG1, hv'⟩ := reduce_spatial_to_zero v hS_ne
    let v' := mulVec G1 v
    have h_mass : v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) = 1 := by
      calc v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2)
        = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := IsGivens_preserves_mass_shell hG1 v
        _ = 1 := h
    have hv'0 : v' 0 ^ 2 - v' 1 ^ 2 = 1 := by
      calc v' 0 ^ 2 - v' 1 ^ 2 = v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) := by dsimp [v']; rw [hv'.2.1, hv'.2.2.1]; ring
        _ = 1 := h_mass
    use givens_t_x (v' 0) (v' 1) * G1
    refine ⟨IsGivens.mul (IsGivens.tx (v' 0) (v' 1) hv'0) hG1, ?_⟩
    ext i; fin_cases i
    · change ((givens_t_x (v' 0) (v' 1) * G1) *ᵥ v) 0 = 1
      simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_0]; linear_combination hv'0
    · change ((givens_t_x (v' 0) (v' 1) * G1) *ᵥ v) 1 = 0
      simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_1]; ring
    · change ((givens_t_x (v' 0) (v' 1) * G1) *ᵥ v) 2 = 0
      simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_2]; exact hv'.2.1
    · change ((givens_t_x (v' 0) (v' 1) * G1) *ᵥ v) 3 = 0
      simp only [mulVec_mulVec, givens_t_x_mulVec, vec4_3]; exact hv'.2.2.1

lemma reduce_spatial_3d_to_e1 (v : Fin 4 → ℂ) (h1 : v 0 = 0) (h_norm : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ (Matrix.mulVec G v) 0 = 0 ∧ (Matrix.mulVec G v) 1 = 1 ∧ (Matrix.mulVec G v) 2 = 0 ∧ (Matrix.mulVec G v) 3 = 0 := by
  by_cases hS : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0
  · rw [hS] at h_norm; norm_num at h_norm
  · have hS_ne : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≠ 0 := hS
    have ⟨G1, hG1, hv'⟩ := reduce_spatial_to_zero v hS_ne
    let v' := Matrix.mulVec G1 v
    have hv'1 : v' 1 ^ 2 = 1 := by rw [hv'.2.2.2, h_norm]
    let G2 := givens_xy (v' 1) 0
    have hG2 : IsGivens G2 := IsGivens.xy (v' 1) 0 (by rw [zero_pow (by decide), add_zero]; exact hv'1)
    use G2 * G1
    refine ⟨IsGivens.mul hG2 hG1, PreservesE0_mul (givens_xy_PreservesE0 (v' 1) 0) hv'.1, ?_, ?_, ?_, ?_⟩
    · change ((givens_xy (v' 1) 0 * G1) *ᵥ v) 0 = 0
      simp only [mulVec_mulVec, givens_xy_mulVec, vec4_0]
      have hv'0 : (G1 *ᵥ v) 0 = 0 := by
        have h_sq : (G1 *ᵥ v) 0 ^ 2 = 0 := by
          have h_mass : (G1 *ᵥ v) 0 ^ 2 - ((G1 *ᵥ v) 1 ^ 2 + (G1 *ᵥ v) 2 ^ 2 + (G1 *ᵥ v) 3 ^ 2) = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := IsGivens_preserves_mass_shell hG1 v
          rw [h1, hv'.2.1, hv'.2.2.1] at h_mass
          rw [hv'.2.2.2, h_norm] at h_mass
          linear_combination h_mass
        exact sq_eq_zero_iff.mp h_sq
      exact hv'0
    · change ((givens_xy (v' 1) 0 * G1) *ᵥ v) 1 = 1
      simp only [mulVec_mulVec, givens_xy_mulVec, vec4_1]
      have hv'1_eq : v' 1 * v' 1 = 1 := by linear_combination hv'1
      linear_combination hv'1_eq
    · change ((givens_xy (v' 1) 0 * G1) *ᵥ v) 2 = 0
      simp only [mulVec_mulVec, givens_xy_mulVec, vec4_2]
      rw [hv'.2.1]; ring
    · change ((givens_xy (v' 1) 0 * G1) *ᵥ v) 3 = 0
      simp only [mulVec_mulVec, givens_xy_mulVec, vec4_3]
      exact hv'.2.2.1

lemma reduce_spatial_2d_to_e2 (v : Fin 4 → ℂ) (h0 : v 0 = 0) (h1 : v 1 = 0) (h_norm : v 2 ^ 2 + v 3 ^ 2 = 1) :
  ∃ G, IsGivens G ∧ PreservesE0 G ∧ PreservesE1 G ∧ (Matrix.mulVec G v) 0 = 0 ∧ (Matrix.mulVec G v) 1 = 0 ∧ (Matrix.mulVec G v) 2 = 1 ∧ (Matrix.mulVec G v) 3 = 0 := by
  let G := givens_yz (v 2) (-v 3)
  have hG : IsGivens G := IsGivens.yz (v 2) (-v 3) (by linear_combination h_norm)
  use G
  refine ⟨hG, givens_yz_PreservesE0 (v 2) (-v 3), givens_yz_PreservesE1 (v 2) (-v 3), ?_, ?_, ?_, ?_⟩
  · change (givens_yz (v 2) (-v 3) *ᵥ v) 0 = 0
    simp only [givens_yz_mulVec, vec4_0]; exact h0
  · change (givens_yz (v 2) (-v 3) *ᵥ v) 1 = 0
    simp only [givens_yz_mulVec, vec4_1]; exact h1
  · change (givens_yz (v 2) (-v 3) *ᵥ v) 2 = 1
    simp only [givens_yz_mulVec, vec4_2]; linear_combination h_norm
  · change (givens_yz (v 2) (-v 3) *ᵥ v) 3 = 0
    simp only [givens_yz_mulVec, vec4_3]; ring

lemma is_givens_inv_xy c s (h : c ^ 2 + s ^ 2 = 1) : givens_xy c s * givens_xy c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_xy, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_yz c s (h : c ^ 2 + s ^ 2 = 1) : givens_yz c s * givens_yz c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_yz, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_zx c s (h : c ^ 2 + s ^ 2 = 1) : givens_zx c s * givens_zx c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_zx, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_tx c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_x c s * givens_t_x c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_x, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_ty c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_y c s * givens_t_y c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_y, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_tz c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_z c s * givens_t_z c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_z, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_xy_r c s (h : c ^ 2 + s ^ 2 = 1) : givens_xy c (-s) * givens_xy c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_xy, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_yz_r c s (h : c ^ 2 + s ^ 2 = 1) : givens_yz c (-s) * givens_yz c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_yz, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_zx_r c s (h : c ^ 2 + s ^ 2 = 1) : givens_zx c (-s) * givens_zx c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_zx, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_tx_r c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_x c (-s) * givens_t_x c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_x, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_ty_r c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_y c (-s) * givens_t_y c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_y, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma is_givens_inv_tz_r c s (h : c ^ 2 - s ^ 2 = 1) : givens_t_z c (-s) * givens_t_z c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [givens_t_z, Matrix.mul_apply, Fin.sum_univ_four] <;> try ring_nf <;> try linear_combination h <;> try linear_combination -h

lemma IsGivens_inv {G : Matrix (Fin 4) (Fin 4) ℂ} (h : IsGivens G) : ∃ G_inv, IsGivens G_inv ∧ G_inv * G = 1 ∧ G * G_inv = 1 := by
  induction h with
  | xy c s h => use givens_xy c (-s); refine ⟨IsGivens.xy c (-s) (by ring_nf; exact h), is_givens_inv_xy_r c s h, is_givens_inv_xy c s h⟩
  | yz c s h => use givens_yz c (-s); refine ⟨IsGivens.yz c (-s) (by ring_nf; exact h), is_givens_inv_yz_r c s h, is_givens_inv_yz c s h⟩
  | zx c s h => use givens_zx c (-s); refine ⟨IsGivens.zx c (-s) (by ring_nf; exact h), is_givens_inv_zx_r c s h, is_givens_inv_zx c s h⟩
  | tx c s h => use givens_t_x c (-s); refine ⟨IsGivens.tx c (-s) (by ring_nf; exact h), is_givens_inv_tx_r c s h, is_givens_inv_tx c s h⟩
  | ty c s h => use givens_t_y c (-s); refine ⟨IsGivens.ty c (-s) (by ring_nf; exact h), is_givens_inv_ty_r c s h, is_givens_inv_ty c s h⟩
  | tz c s h => use givens_t_z c (-s); refine ⟨IsGivens.tz c (-s) (by ring_nf; exact h), is_givens_inv_tz_r c s h, is_givens_inv_tz c s h⟩
  | one => use 1; refine ⟨IsGivens.one, mul_one 1, mul_one 1⟩
  | mul hA hB ihA ihB =>
    rcases ihA with ⟨A_inv, hA_inv, hA_mul, hA_mul2⟩
    rcases ihB with ⟨B_inv, hB_inv, hB_mul, hB_mul2⟩
    use B_inv * A_inv
    refine ⟨IsGivens.mul hB_inv hA_inv, ?_, ?_⟩
    · rw [Matrix.mul_assoc, ←Matrix.mul_assoc A_inv, hA_mul, Matrix.one_mul, hB_mul]
    · rw [Matrix.mul_assoc, ←Matrix.mul_assoc _ B_inv A_inv, hB_mul2, Matrix.one_mul, hA_mul2]

lemma IsGivens_preserves_metric {G : Matrix (Fin 4) (Fin 4) ℂ} (h : IsGivens G) : Gᵀ * minkowskiMetric * G = minkowskiMetric := by
  induction h with
  | xy c s h => exact givens_xy_is_lorentz c s h
  | yz c s h => exact givens_yz_is_lorentz c s h
  | zx c s h => exact givens_zx_is_lorentz c s h
  | tx c s h => exact givens_t_x_is_lorentz c s h
  | ty c s h => exact givens_t_y_is_lorentz c s h
  | tz c s h => exact givens_t_z_is_lorentz c s h
  | one => simp
  | @mul A B hA hB ihA ihB =>
    simp only [Matrix.transpose_mul]
    rw [Matrix.mul_assoc Bᵀ Aᵀ]
    rw [Matrix.mul_assoc Bᵀ (Aᵀ * minkowskiMetric)]
    rw [←Matrix.mul_assoc (Aᵀ * minkowskiMetric) A B]
    rw [ihA]
    rw [←Matrix.mul_assoc Bᵀ minkowskiMetric B]
    exact ihB

lemma givens_xy_det c s (h : c ^ 2 + s ^ 2 = 1) : (givens_xy c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_xy c s) 0 0 = 1 := rfl
  have h1 : (givens_xy c s) 0 1 = 0 := rfl
  have h2 : (givens_xy c s) 0 2 = 0 := rfl
  have h3 : (givens_xy c s) 0 3 = 0 := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_xy]; ring_nf; linear_combination h

lemma givens_yz_det c s (h : c ^ 2 + s ^ 2 = 1) : (givens_yz c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_yz c s) 0 0 = 1 := rfl
  have h1 : (givens_yz c s) 0 1 = 0 := rfl
  have h2 : (givens_yz c s) 0 2 = 0 := rfl
  have h3 : (givens_yz c s) 0 3 = 0 := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_yz]; ring_nf; linear_combination h

lemma givens_zx_det c s (h : c ^ 2 + s ^ 2 = 1) : (givens_zx c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_zx c s) 0 0 = 1 := rfl
  have h1 : (givens_zx c s) 0 1 = 0 := rfl
  have h2 : (givens_zx c s) 0 2 = 0 := rfl
  have h3 : (givens_zx c s) 0 3 = 0 := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_zx]; ring_nf; linear_combination h

lemma givens_t_x_det c s (h : c ^ 2 - s ^ 2 = 1) : (givens_t_x c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_t_x c s) 0 0 = c := rfl
  have h1 : (givens_t_x c s) 0 1 = -s := rfl
  have h2 : (givens_t_x c s) 0 2 = 0 := rfl
  have h3 : (givens_t_x c s) 0 3 = 0 := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_t_x]; ring_nf; linear_combination h

lemma givens_t_y_det c s (h : c ^ 2 - s ^ 2 = 1) : (givens_t_y c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_t_y c s) 0 0 = c := rfl
  have h1 : (givens_t_y c s) 0 1 = 0 := rfl
  have h2 : (givens_t_y c s) 0 2 = -s := rfl
  have h3 : (givens_t_y c s) 0 3 = 0 := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_t_y]; ring_nf; linear_combination h

lemma givens_t_z_det c s (h : c ^ 2 - s ^ 2 = 1) : (givens_t_z c s).det = 1 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four]
  have h0 : (givens_t_z c s) 0 0 = c := rfl
  have h1 : (givens_t_z c s) 0 1 = 0 := rfl
  have h2 : (givens_t_z c s) 0 2 = 0 := rfl
  have h3 : (givens_t_z c s) 0 3 = -s := rfl
  rw [h0, h1, h2, h3]; simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, givens_t_z]; ring_nf; linear_combination h

lemma IsGivens_det {G : Matrix (Fin 4) (Fin 4) ℂ} (h : IsGivens G) : G.det = 1 := by
  induction h with
  | xy c s h => exact givens_xy_det c s h
  | yz c s h => exact givens_yz_det c s h
  | zx c s h => exact givens_zx_det c s h
  | tx c s h => exact givens_t_x_det c s h
  | ty c s h => exact givens_t_y_det c s h
  | tz c s h => exact givens_t_z_det c s h
  | one => simp
  | mul hA hB ihA ihB => rw [Matrix.det_mul, ihA, ihB, mul_one]

lemma so4c_generated_by_givens (M : Matrix (Fin 4) (Fin 4) ℂ)
  (hM : Mᵀ * minkowskiMetric * M = minkowskiMetric)
  (hDet : M.det = 1) :
  ∃ G, IsGivens G ∧ M = G := by
  let v := fun i => M i 0
  have h_mass_shell : v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) = 1 := by
    have hM00 : (Mᵀ * minkowskiMetric * M) 0 0 = minkowskiMetric 0 0 := by rw [hM]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at hM00
    linear_combination hM00

  have ⟨G1, hG1, hG1_v⟩ := reduce_to_e0 v h_mass_shell

  let M1 := G1 * M
  have h_M1_col0 : ∀ i, M1 i 0 = if i = 0 then 1 else 0 := by
    intro i
    have : M1 i 0 = (G1 *ᵥ v) i := rfl
    rw [this]
    fin_cases i
    · change (G1 *ᵥ v) 0 = 1; rw [hG1_v]; rfl
    · change (G1 *ᵥ v) 1 = 0; rw [hG1_v]; rfl
    · change (G1 *ᵥ v) 2 = 0; rw [hG1_v]; rfl
    · change (G1 *ᵥ v) 3 = 0; rw [hG1_v]; rfl

  have h_M1_metric : M1ᵀ * minkowskiMetric * M1 = minkowskiMetric := by
    calc M1ᵀ * minkowskiMetric * M1 = Mᵀ * (G1ᵀ * minkowskiMetric * G1) * M := by
          simp only [M1, Matrix.transpose_mul]
          rw [Matrix.mul_assoc Mᵀ G1ᵀ minkowskiMetric]
          rw [Matrix.mul_assoc Mᵀ (G1ᵀ * minkowskiMetric) (G1 * M)]
          rw [←Matrix.mul_assoc (G1ᵀ * minkowskiMetric) G1 M]
          rw [Matrix.mul_assoc Mᵀ _ M]
      _ = Mᵀ * minkowskiMetric * M := by rw [IsGivens_preserves_metric hG1]
      _ = minkowskiMetric := hM

  have h_M1_row0 : ∀ j > 0, M1 0 j = 0 := by
    intro j hj
    have h_0j : (M1ᵀ * minkowskiMetric * M1) j 0 = minkowskiMetric j 0 := by rw [h_M1_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_0j
    have h0 : M1 0 0 = 1 := by exact h_M1_col0 0
    have h1 : M1 1 0 = 0 := by exact h_M1_col0 1
    have h2 : M1 2 0 = 0 := by exact h_M1_col0 2
    have h3 : M1 3 0 = 0 := by exact h_M1_col0 3
    rw [h0, h1, h2, h3] at h_0j
    revert h_0j hj
    fin_cases j <;> simp

  let v2 := fun i => M1 i 1
  have h_v2_0 : v2 0 = 0 := by exact h_M1_row0 1 (by decide)
  have h_v2_mass : v2 1 ^ 2 + v2 2 ^ 2 + v2 3 ^ 2 = 1 := by
    have hM11 : (M1ᵀ * minkowskiMetric * M1) 1 1 = minkowskiMetric 1 1 := by rw [h_M1_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at hM11
    have h0 : M1 0 1 = 0 := h_v2_0
    rw [h0] at hM11
    ring_nf at hM11
    linear_combination -hM11

  have ⟨G2, hG2, hG2_preserves0, hG2_v2⟩ := reduce_spatial_3d_to_e1 v2 h_v2_0 h_v2_mass
  let M2 := G2 * M1

  have h_M2_col0 : ∀ i, M2 i 0 = if i = 0 then 1 else 0 := extract_col0 G2 M1 M2 rfl h_M1_col0 hG2_preserves0

  have h_M2_col1 : ∀ i, M2 i 1 = if i = 1 then 1 else 0 := by
    intro i
    have : M2 i 1 = (G2 *ᵥ v2) i := rfl
    rw [this]
    fin_cases i
    · change (G2 *ᵥ v2) 0 = 0; rw [hG2_v2.1]
    · change (G2 *ᵥ v2) 1 = 1; rw [hG2_v2.2.1]
    · change (G2 *ᵥ v2) 2 = 0; rw [hG2_v2.2.2.1]
    · change (G2 *ᵥ v2) 3 = 0; rw [hG2_v2.2.2.2]

  have h_M2_metric : M2ᵀ * minkowskiMetric * M2 = minkowskiMetric := by
    calc M2ᵀ * minkowskiMetric * M2 = M1ᵀ * (G2ᵀ * minkowskiMetric * G2) * M1 := by
          simp only [M2, Matrix.transpose_mul]
          rw [Matrix.mul_assoc M1ᵀ G2ᵀ minkowskiMetric]
          rw [Matrix.mul_assoc M1ᵀ (G2ᵀ * minkowskiMetric) (G2 * M1)]
          rw [←Matrix.mul_assoc (G2ᵀ * minkowskiMetric) G2 M1]
          rw [Matrix.mul_assoc M1ᵀ _ M1]
      _ = M1ᵀ * minkowskiMetric * M1 := by rw [IsGivens_preserves_metric hG2]
      _ = minkowskiMetric := h_M1_metric

  have h_M2_row1 : ∀ j > 1, M2 1 j = 0 := by
    intro j hj
    have h_1j : (M2ᵀ * minkowskiMetric * M2) j 1 = minkowskiMetric j 1 := by rw [h_M2_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_1j
    have h0 : M2 0 1 = 0 := by exact h_M2_col1 0
    have h1 : M2 1 1 = 1 := by exact h_M2_col1 1
    have h2 : M2 2 1 = 0 := by exact h_M2_col1 2
    have h3 : M2 3 1 = 0 := by exact h_M2_col1 3
    rw [h0, h1, h2, h3] at h_1j
    revert h_1j hj
    fin_cases j <;> simp

  have h_M2_row0 : ∀ j > 0, M2 0 j = 0 := by
    intro j hj
    have h_0j : (M2ᵀ * minkowskiMetric * M2) j 0 = minkowskiMetric j 0 := by rw [h_M2_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_0j
    have h0 : M2 0 0 = 1 := by exact h_M2_col0 0
    have h1 : M2 1 0 = 0 := by exact h_M2_col0 1
    have h2 : M2 2 0 = 0 := by exact h_M2_col0 2
    have h3 : M2 3 0 = 0 := by exact h_M2_col0 3
    rw [h0, h1, h2, h3] at h_0j
    revert h_0j hj
    fin_cases j <;> simp

  let v3 := fun i => M2 i 2
  have h_v3_0 : v3 0 = 0 := by exact h_M2_row0 2 (by decide)
  have h_v3_1 : v3 1 = 0 := by exact h_M2_row1 2 (by decide)
  have h_v3_mass : v3 2 ^ 2 + v3 3 ^ 2 = 1 := by
    have hM22 : (M2ᵀ * minkowskiMetric * M2) 2 2 = minkowskiMetric 2 2 := by rw [h_M2_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at hM22
    have h0 : M2 0 2 = 0 := h_v3_0
    have h1 : M2 1 2 = 0 := h_v3_1
    rw [h0, h1] at hM22
    ring_nf at hM22
    linear_combination -hM22

  have ⟨G3, hG3, hG3_preserves0, hG3_preserves1, hG3_v3⟩ := reduce_spatial_2d_to_e2 v3 h_v3_0 h_v3_1 h_v3_mass
  let M3 := G3 * M2

  have h_M3_col0 : ∀ i, M3 i 0 = if i = 0 then 1 else 0 := extract_col0 G3 M2 M3 rfl h_M2_col0 hG3_preserves0

  have h_M3_col1 : ∀ i, M3 i 1 = if i = 1 then 1 else 0 := extract_col1 G3 M2 M3 rfl h_M2_col1 hG3_preserves1

  have h_M3_col2 : ∀ i, M3 i 2 = if i = 2 then 1 else 0 := by
    intro i
    have : M3 i 2 = (G3 *ᵥ v3) i := rfl
    rw [this]
    fin_cases i
    · change (G3 *ᵥ v3) 0 = 0; rw [hG3_v3.1]
    · change (G3 *ᵥ v3) 1 = 0; rw [hG3_v3.2.1]
    · change (G3 *ᵥ v3) 2 = 1; rw [hG3_v3.2.2.1]
    · change (G3 *ᵥ v3) 3 = 0; rw [hG3_v3.2.2.2]

  have h_M3_metric : M3ᵀ * minkowskiMetric * M3 = minkowskiMetric := by
    calc M3ᵀ * minkowskiMetric * M3 = M2ᵀ * (G3ᵀ * minkowskiMetric * G3) * M2 := by
          simp only [M3, Matrix.transpose_mul]
          rw [Matrix.mul_assoc M2ᵀ G3ᵀ minkowskiMetric]
          rw [Matrix.mul_assoc M2ᵀ (G3ᵀ * minkowskiMetric) (G3 * M2)]
          rw [←Matrix.mul_assoc (G3ᵀ * minkowskiMetric) G3 M2]
          rw [Matrix.mul_assoc M2ᵀ _ M2]
      _ = M2ᵀ * minkowskiMetric * M2 := by rw [IsGivens_preserves_metric hG3]
      _ = minkowskiMetric := h_M2_metric

  have h_M3_col3_3 : M3 3 3 ^ 2 = 1 := by
    have hM33 : (M3ᵀ * minkowskiMetric * M3) 3 3 = minkowskiMetric 3 3 := by rw [h_M3_metric]
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at hM33
    have h0 : M3 0 3 = 0 := by
      have h_03 : (M3ᵀ * minkowskiMetric * M3) 3 0 = minkowskiMetric 3 0 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_03
      have c0 : M3 0 0 = 1 := by exact h_M3_col0 0
      have c1 : M3 1 0 = 0 := by exact h_M3_col0 1
      have c2 : M3 2 0 = 0 := by exact h_M3_col0 2
      have c3 : M3 3 0 = 0 := by exact h_M3_col0 3
      rw [c0, c1, c2, c3] at h_03
      linear_combination h_03
    have h1 : M3 1 3 = 0 := by
      have h_13 : (M3ᵀ * minkowskiMetric * M3) 3 1 = minkowskiMetric 3 1 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_13
      have c0 : M3 0 1 = 0 := by exact h_M3_col1 0
      have c1 : M3 1 1 = 1 := by exact h_M3_col1 1
      have c2 : M3 2 1 = 0 := by exact h_M3_col1 2
      have c3 : M3 3 1 = 0 := by exact h_M3_col1 3
      rw [c0, c1, c2, c3] at h_13
      linear_combination -h_13
    have h2 : M3 2 3 = 0 := by
      have h_23 : (M3ᵀ * minkowskiMetric * M3) 3 2 = minkowskiMetric 3 2 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_23
      have c0 : M3 0 2 = 0 := by exact h_M3_col2 0
      have c1 : M3 1 2 = 0 := by exact h_M3_col2 1
      have c2 : M3 2 2 = 1 := by exact h_M3_col2 2
      have c3 : M3 3 2 = 0 := by exact h_M3_col2 3
      rw [c0, c1, c2, c3] at h_23
      linear_combination -h_23
    rw [h0, h1, h2] at hM33
    linear_combination -hM33

  have h_M3_det : M3.det = 1 := by
    have h_G1_det : G1.det = 1 := IsGivens_det hG1
    have h_G2_det : G2.det = 1 := IsGivens_det hG2
    have h_G3_det : G3.det = 1 := IsGivens_det hG3
    calc M3.det = G3.det * (G2.det * (G1.det * M.det)) := by simp [M3, M2, M1, Matrix.det_mul]
      _ = 1 * (1 * (1 * 1)) := by rw [h_G1_det, h_G2_det, h_G3_det, hDet]
      _ = 1 := by ring

  have h_M3_col3_3_val : M3 3 3 = 1 := by
    have h_diag : M3 = Matrix.diagonal ![1, 1, 1, M3 3 3] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, *] <;> (
        try exact h_M3_col0 i
        try exact h_M3_col1 i
        try exact h_M3_col2 i)
      · have h_03 : (M3ᵀ * minkowskiMetric * M3) 3 0 = minkowskiMetric 3 0 := by rw [h_M3_metric]
        simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_03
        have c0 : M3 0 0 = 1 := by exact h_M3_col0 0
        have c1 : M3 1 0 = 0 := by exact h_M3_col0 1
        have c2 : M3 2 0 = 0 := by exact h_M3_col0 2
        have c3 : M3 3 0 = 0 := by exact h_M3_col0 3
        rw [c0, c1, c2, c3] at h_03
        linear_combination h_03
      · have h_13 : (M3ᵀ * minkowskiMetric * M3) 3 1 = minkowskiMetric 3 1 := by rw [h_M3_metric]
        simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_13
        have c0 : M3 0 1 = 0 := by exact h_M3_col1 0
        have c1 : M3 1 1 = 1 := by exact h_M3_col1 1
        have c2 : M3 2 1 = 0 := by exact h_M3_col1 2
        have c3 : M3 3 1 = 0 := by exact h_M3_col1 3
        rw [c0, c1, c2, c3] at h_13
        linear_combination -h_13
      · have h_23 : (M3ᵀ * minkowskiMetric * M3) 3 2 = minkowskiMetric 3 2 := by rw [h_M3_metric]
        simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_23
        have c0 : M3 0 2 = 0 := by exact h_M3_col2 0
        have c1 : M3 1 2 = 0 := by exact h_M3_col2 1
        have c2 : M3 2 2 = 1 := by exact h_M3_col2 2
        have c3 : M3 3 2 = 0 := by exact h_M3_col2 3
        simp [c0, c1, c2, c3] at h_23
        ring_nf at h_23
        exact h_23
    have h_det : M3.det = M3 3 3 := by
      rw [h_diag, det_diagonal, Fin.prod_univ_four]
      simp <;> try ring
    rw [←h_det, h_M3_det]

  have h_M3_is_1 : M3 = 1 := by
    ext i j
    have c0 := h_M3_col0 i
    have c1 := h_M3_col1 i
    have c2 := h_M3_col2 i
    fin_cases i <;> fin_cases j <;> simp [*] <;> try exact c0 <;> try exact c1 <;> try exact c2
    · have h_03 : (M3ᵀ * minkowskiMetric * M3) 3 0 = minkowskiMetric 3 0 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_03
      have cc0 : M3 0 0 = 1 := by exact h_M3_col0 0
      have cc1 : M3 1 0 = 0 := by exact h_M3_col0 1
      have cc2 : M3 2 0 = 0 := by exact h_M3_col0 2
      have cc3 : M3 3 0 = 0 := by exact h_M3_col0 3
      simp [cc0, cc1, cc2, cc3] at h_03
      ring_nf at h_03
      exact h_03
    · have h_13 : (M3ᵀ * minkowskiMetric * M3) 3 1 = minkowskiMetric 3 1 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_13
      have cc0 : M3 0 1 = 0 := by exact h_M3_col1 0
      have cc1 : M3 1 1 = 1 := by exact h_M3_col1 1
      have cc2 : M3 2 1 = 0 := by exact h_M3_col1 2
      have cc3 : M3 3 1 = 0 := by exact h_M3_col1 3
      simp [cc0, cc1, cc2, cc3] at h_13
      ring_nf at h_13
      exact h_13
    · have h_23 : (M3ᵀ * minkowskiMetric * M3) 3 2 = minkowskiMetric 3 2 := by rw [h_M3_metric]
      simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four] at h_23
      have cc0 : M3 0 2 = 0 := by exact h_M3_col2 0
      have cc1 : M3 1 2 = 0 := by exact h_M3_col2 1
      have cc2 : M3 2 2 = 1 := by exact h_M3_col2 2
      have cc3 : M3 3 2 = 0 := by exact h_M3_col2 3
      simp [cc0, cc1, cc2, cc3] at h_23
      ring_nf at h_23
      exact h_23

  let G_all := G3 * (G2 * G1)
  have h_G_all : IsGivens G_all := IsGivens.mul hG3 (IsGivens.mul hG2 hG1)
  have h_G_all_M : G_all * M = 1 := by
    calc G_all * M = G3 * (G2 * G1) * M := rfl
      _ = G3 * (G2 * (G1 * M)) := by rw [Matrix.mul_assoc G3 (G2 * G1) M, Matrix.mul_assoc G2 G1 M]
      _ = M3 := rfl
      _ = 1 := h_M3_is_1

  rcases IsGivens_inv h_G_all with ⟨G_inv, hG_inv, h_inv1, h_inv2⟩
  use G_inv
  refine ⟨hG_inv, ?_⟩
  calc M = 1 * M := by rw [Matrix.one_mul]
    _ = (G_inv * G_all) * M := by rw [←h_inv1]
    _ = G_inv * (G_all * M) := by rw [Matrix.mul_assoc]
    _ = G_inv * 1 := by rw [h_G_all_M]
    _ = G_inv := by rw [Matrix.mul_one]

end Geometry
