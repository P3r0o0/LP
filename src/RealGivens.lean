import Mathlib.Analysis.Real.Sqrt
import Minkowski

open Matrix Set Real Geometry

lemma vec4_0 (v0 v1 v2 v3 : ℝ) : ![v0, v1, v2, v3] 0 = v0 := rfl
lemma vec4_1 (v0 v1 v2 v3 : ℝ) : ![v0, v1, v2, v3] 1 = v1 := rfl
lemma vec4_2 (v0 v1 v2 v3 : ℝ) : ![v0, v1, v2, v3] 2 = v2 := rfl
lemma vec4_3 (v0 v1 v2 v3 : ℝ) : ![v0, v1, v2, v3] 3 = v3 := rfl

lemma sq_add_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have h1 : 0 ≤ x ^ 2 := sq_nonneg x
  have h2 : 0 ≤ y ^ 2 := sq_nonneg y
  have h3 : x ^ 2 = 0 := by linarith
  have h4 : y ^ 2 = 0 := by linarith
  exact ⟨sq_eq_zero_iff.mp h3, sq_eq_zero_iff.mp h4⟩

namespace Geometry.RealGivens

noncomputable def givens_xy (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![
  1, 0, 0, 0;
  0, c, -s, 0;
  0, s, c, 0;
  0, 0, 0, 1
]

lemma givens_xy_is_lorentz (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
  (givens_xy c s)ᵀ * minkowskiMetricReal * (givens_xy c s) = minkowskiMetricReal := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_xy, minkowskiMetricReal, Fin.sum_univ_four]
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_zx (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![
  1, 0, 0, 0;
  0, c, 0, s;
  0, 0, 1, 0;
  0, -s, 0, c
]

lemma givens_zx_is_lorentz (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
  (givens_zx c s)ᵀ * minkowskiMetricReal * (givens_zx c s) = minkowskiMetricReal := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_zx, minkowskiMetricReal, Fin.sum_univ_four]
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

noncomputable def givens_t_x (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![
  c, -s, 0, 0;
  -s, c, 0, 0;
  0, 0, 1, 0;
  0, 0, 0, 1
]

lemma givens_t_x_is_lorentz (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) :
  (givens_t_x c s)ᵀ * minkowskiMetricReal * (givens_t_x c s) = minkowskiMetricReal := by
  ext i j; fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, givens_t_x, minkowskiMetricReal, Fin.sum_univ_four]
    try linear_combination h
    try linear_combination -h
    try ring_nf
  )

lemma givens_reduce_step_real (v1 v2 : ℝ) (h : v1 ^ 2 + v2 ^ 2 ≠ 0) :
  ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * v1 + c * v2 = 0 ∧ (c * v1 - s * v2) ^ 2 = v1 ^ 2 + v2 ^ 2 := by
  let R := Real.sqrt (v1 ^ 2 + v2 ^ 2)
  have hR2 : R ^ 2 = v1 ^ 2 + v2 ^ 2 := by apply Real.sq_sqrt; positivity
  have hR_ne_0 : R ≠ 0 := by intro H; rw [H, zero_pow (by decide)] at hR2; exact h hR2.symm
  use (v1 / R), (-v2 / R)
  refine ⟨?_, ?_, ?_⟩
  · calc (v1 / R) ^ 2 + (-v2 / R) ^ 2 = (v1 ^ 2 + v2 ^ 2) / R ^ 2 := by ring
      _ = R ^ 2 / R ^ 2 := by rw [hR2]
      _ = 1 := div_self (by positivity)
  · ring
  · calc (v1 / R * v1 - (-v2 / R) * v2) ^ 2 = ((v1 ^ 2 + v2 ^ 2) / R) ^ 2 := by ring
      _ = (R ^ 2 / R) ^ 2 := by rw [hR2]
      _ = R ^ 2 := by
        have : R ^ 2 / R = R := by
          calc R ^ 2 / R = R * R / R := by ring
            _ = R := mul_div_cancel_right₀ R hR_ne_0
        rw [this]
      _ = v1 ^ 2 + v2 ^ 2 := hR2

lemma givens_xy_mulVec (c s : ℝ) (v : Fin 4 → ℝ) :
  Matrix.mulVec (givens_xy c s) v = ![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] := by
  ext i; dsimp [givens_xy, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_zx_mulVec (c s : ℝ) (v : Fin 4 → ℝ) :
  Matrix.mulVec (givens_zx c s) v = ![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] := by
  ext i; dsimp [givens_zx, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

lemma givens_t_x_mulVec (c s : ℝ) (v : Fin 4 → ℝ) :
  Matrix.mulVec (givens_t_x c s) v = ![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] := by
  ext i; dsimp [givens_t_x, mulVec, dotProduct]; fin_cases i <;> { simp [Fin.sum_univ_four]; try ring_nf }

inductive IsRealGivens : Matrix (Fin 4) (Fin 4) ℝ → Prop
| xy (c s : ℝ) (h : c^2 + s^2 = 1) : IsRealGivens (givens_xy c s)
| zx (c s : ℝ) (h : c^2 + s^2 = 1) : IsRealGivens (givens_zx c s)
| tx (c s : ℝ) (h : c^2 - s^2 = 1) (hpos : c > 0) : IsRealGivens (givens_t_x c s)
| one : IsRealGivens 1
| mul {A B} (hA : IsRealGivens A) (hB : IsRealGivens B) : IsRealGivens (A * B)

lemma IsRealGivens_lorentz {G : Matrix (Fin 4) (Fin 4) ℝ} (h : IsRealGivens G) : Gᵀ * minkowskiMetricReal * G = minkowskiMetricReal := by
  induction h with
  | xy c s hc => exact givens_xy_is_lorentz c s hc
  | zx c s hc => exact givens_zx_is_lorentz c s hc
  | tx c s hc => exact givens_t_x_is_lorentz c s hc
  | one => simp
  | @mul A B hA hB ihA ihB =>
    calc (A * B)ᵀ * minkowskiMetricReal * (A * B)
      _ = Bᵀ * (Aᵀ * minkowskiMetricReal * A) * B := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Bᵀ * minkowskiMetricReal * B := by rw [ihA]
      _ = minkowskiMetricReal := ihB

lemma IsRealGivens_preserves_mass_shell {G} (hG : IsRealGivens G) (v : Fin 4 → ℝ) :
  (Matrix.mulVec G v) 0 ^ 2 - ((Matrix.mulVec G v) 1 ^ 2 + (Matrix.mulVec G v) 2 ^ 2 + (Matrix.mulVec G v) 3 ^ 2) =
  v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
  induction hG generalizing v with
  | xy c s h =>
    rw [givens_xy_mulVec]
    calc ![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] 0 ^ 2 - (![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] 1 ^ 2 + ![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] 2 ^ 2 + ![v 0, c * v 1 - s * v 2, s * v 1 + c * v 2, v 3] 3 ^ 2)
      = v 0 ^ 2 - ((c * v 1 - s * v 2) ^ 2 + (s * v 1 + c * v 2) ^ 2 + v 3 ^ 2) := by simp [vec4_2, vec4_3]
      _ = v 0 ^ 2 - ((c^2 + s^2) * (v 1 ^ 2 + v 2 ^ 2) + v 3 ^ 2) := by ring
      _ = v 0 ^ 2 - (1 * (v 1 ^ 2 + v 2 ^ 2) + v 3 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | zx c s h =>
    rw [givens_zx_mulVec]
    calc ![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] 0 ^ 2 - (![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] 1 ^ 2 + ![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] 2 ^ 2 + ![v 0, c * v 1 + s * v 3, v 2, -s * v 1 + c * v 3] 3 ^ 2)
      = v 0 ^ 2 - ((c * v 1 + s * v 3) ^ 2 + v 2 ^ 2 + (-s * v 1 + c * v 3) ^ 2) := by simp [vec4_2, vec4_3]
      _ = v 0 ^ 2 - ((c^2 + s^2) * (v 1 ^ 2 + v 3 ^ 2) + v 2 ^ 2) := by ring
      _ = v 0 ^ 2 - (1 * (v 1 ^ 2 + v 3 ^ 2) + v 2 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | tx c s h =>
    rw [givens_t_x_mulVec]
    calc ![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] 0 ^ 2 - (![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] 1 ^ 2 + ![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] 2 ^ 2 + ![c * v 0 - s * v 1, -s * v 0 + c * v 1, v 2, v 3] 3 ^ 2)
      = (c * v 0 - s * v 1) ^ 2 - ((-s * v 0 + c * v 1) ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by simp [vec4_2, vec4_3]
      _ = (c^2 - s^2) * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by ring
      _ = 1 * (v 0 ^ 2 - v 1 ^ 2) - (v 2 ^ 2 + v 3 ^ 2) := by rw [h]
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  | one =>
    rw [Matrix.one_mulVec]
  | @mul A B hA hB ihA ihB =>
    calc (Matrix.mulVec (A * B) v) 0 ^ 2 - ((Matrix.mulVec (A * B) v) 1 ^ 2 + (Matrix.mulVec (A * B) v) 2 ^ 2 + (Matrix.mulVec (A * B) v) 3 ^ 2)
      = (Matrix.mulVec A (Matrix.mulVec B v)) 0 ^ 2 - ((Matrix.mulVec A (Matrix.mulVec B v)) 1 ^ 2 + (Matrix.mulVec A (Matrix.mulVec B v)) 2 ^ 2 + (Matrix.mulVec A (Matrix.mulVec B v)) 3 ^ 2) := by rw [Matrix.mulVec_mulVec]
      _ = (Matrix.mulVec B v) 0 ^ 2 - ((Matrix.mulVec B v) 1 ^ 2 + (Matrix.mulVec B v) 2 ^ 2 + (Matrix.mulVec B v) 3 ^ 2) := ihA (Matrix.mulVec B v)
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := ihB v

lemma reduce_v2_to_0 (v0 v1 v2 v3 : ℝ) :
  ∃ c s : ℝ, c^2 + s^2 = 1 ∧ s * v1 + c * v2 = 0 ∧ (c * v1 - s * v2)^2 = v1^2 + v2^2 := by
  by_cases h : v1 ^ 2 + v2 ^ 2 = 0
  · use 1, 0
    have ⟨hv1, hv2⟩ := sq_add_sq_eq_zero h
    simp [hv1, hv2]
  · exact givens_reduce_step_real v1 v2 h

lemma reduce_v3_to_0 (v0 v1 v3 : ℝ) :
  ∃ c s : ℝ, c^2 + s^2 = 1 ∧ -s * v1 + c * v3 = 0 ∧ (c * v1 + s * v3)^2 = v1^2 + v3^2 := by
  by_cases h : v1 ^ 2 + v3 ^ 2 = 0
  · use 1, 0
    have ⟨hv1, hv3⟩ := sq_add_sq_eq_zero h
    simp [hv1, hv3]
  · obtain ⟨c, s, hc, hs, hsq⟩ := givens_reduce_step_real v1 v3 h
    use c, -s
    refine ⟨?_, ?_, ?_⟩
    · calc c ^ 2 + (-s) ^ 2 = c ^ 2 + s ^ 2 := by ring
        _ = 1 := hc
    · calc -(-s) * v1 + c * v3 = s * v1 + c * v3 := by ring
        _ = 0 := hs
    · calc (c * v1 + (-s) * v3) ^ 2 = (c * v1 - s * v3) ^ 2 := by ring
        _ = v1 ^ 2 + v3 ^ 2 := hsq

lemma reduce_v1_to_0 (v0 v1 : ℝ) (h1 : v0 ^ 2 - v1 ^ 2 = 1) (h2 : v0 > 0) :
  ∃ c s : ℝ, c^2 - s^2 = 1 ∧ -s * v0 + c * v1 = 0 ∧ c * v0 - s * v1 = 1 ∧ c > 0 := by
  use v0, v1
  refine ⟨h1, ?_, ?_, h2⟩
  · ring
  · calc v0 * v0 - v1 * v1 = v0 ^ 2 - v1 ^ 2 := by ring
      _ = 1 := h1

lemma reduce_to_e0 (v : Fin 4 → ℝ) (h1 : v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) = 1) (h2 : v 0 > 0) :
  ∃ G : Matrix (Fin 4) (Fin 4) ℝ, IsRealGivens G ∧
    Matrix.mulVec G v = ![1, 0, 0, 0] := by
  obtain ⟨c1, s1, hc1, hs1, hsq1⟩ := reduce_v2_to_0 (v 0) (v 1) (v 2) (v 3)
  let v' := Matrix.mulVec (givens_xy c1 s1) v
  have hv'_0 : v' 0 = v 0 := by dsimp [v']; rw [givens_xy_mulVec, vec4_0]
  have hv'_1 : v' 1 = c1 * v 1 - s1 * v 2 := by dsimp [v']; rw [givens_xy_mulVec, vec4_1]
  have hv'_2 : v' 2 = 0 := by
    dsimp [v']
    rw [givens_xy_mulVec, vec4_2]
    exact hs1
  have hv'_3 : v' 3 = v 3 := by dsimp [v']; rw [givens_xy_mulVec, vec4_3]

  obtain ⟨c2, s2, hc2, hs2, hsq2⟩ := reduce_v3_to_0 (v' 0) (v' 1) (v' 3)
  let v'' := Matrix.mulVec (givens_zx c2 s2) v'
  have hv''_0 : v'' 0 = v 0 := by
    dsimp [v'']
    rw [givens_zx_mulVec, vec4_0]
    exact hv'_0
  have hv''_1 : v'' 1 = c2 * v' 1 + s2 * v' 3 := by dsimp [v'']; rw [givens_zx_mulVec, vec4_1]
  have hv''_2 : v'' 2 = 0 := by
    dsimp [v'']
    rw [givens_zx_mulVec, vec4_2]
    exact hv'_2
  have hv''_3 : v'' 3 = 0 := by
    dsimp [v'']
    rw [givens_zx_mulVec, vec4_3]
    exact hs2

  have h_mass : v'' 0 ^ 2 - v'' 1 ^ 2 = 1 := by
    calc v'' 0 ^ 2 - v'' 1 ^ 2 = v'' 0 ^ 2 - (v'' 1 ^ 2 + v'' 2 ^ 2 + v'' 3 ^ 2) := by rw [hv''_2, hv''_3]; ring
      _ = v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2) := IsRealGivens_preserves_mass_shell (IsRealGivens.zx c2 s2 hc2) v'
      _ = v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := IsRealGivens_preserves_mass_shell (IsRealGivens.xy c1 s1 hc1) v
      _ = 1 := h1

  have hv''_0_pos : v'' 0 > 0 := by rw [hv''_0]; exact h2

  obtain ⟨c3, s3, hc3, hs3, hsq3, hc3_pos⟩ := reduce_v1_to_0 (v'' 0) (v'' 1) h_mass hv''_0_pos
  let v''' := Matrix.mulVec (givens_t_x c3 s3) v''
  have hv'''_0 : v''' 0 = 1 := by
    dsimp [v''']
    rw [givens_t_x_mulVec, vec4_0]
    exact hsq3
  have hv'''_1 : v''' 1 = 0 := by
    dsimp [v''']
    rw [givens_t_x_mulVec, vec4_1]
    exact hs3
  have hv'''_2 : v''' 2 = 0 := by
    dsimp [v''']
    rw [givens_t_x_mulVec, vec4_2]
    exact hv''_2
  have hv'''_3 : v''' 3 = 0 := by
    dsimp [v''']
    rw [givens_t_x_mulVec, vec4_3]
    exact hv''_3

  use (givens_t_x c3 s3) * (givens_zx c2 s2) * (givens_xy c1 s1)
  refine ⟨?_, ?_⟩
  · apply IsRealGivens.mul
    · apply IsRealGivens.mul
      · exact IsRealGivens.tx c3 s3 hc3 hc3_pos
      · exact IsRealGivens.zx c2 s2 hc2
    · exact IsRealGivens.xy c1 s1 hc1
  · have h_mul : Matrix.mulVec ((givens_t_x c3 s3) * (givens_zx c2 s2) * (givens_xy c1 s1)) v = v''' := by
      dsimp [v''', v'', v']
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h_mul]
    ext i
    fin_cases i
    · exact hv'''_0
    · exact hv'''_1
    · exact hv'''_2
    · exact hv'''_3


lemma reduce_v1_to_pos_1 (v1 : ℝ) (h : v1 ^ 2 = 1) :
  ∃ c s : ℝ, c^2 + s^2 = 1 ∧ (c * v1 = 1) ∧ (s = 0) := by
  use v1, 0
  refine ⟨?_, ?_, rfl⟩
  · calc v1 ^ 2 + 0 ^ 2 = v1 ^ 2 := by ring
      _ = 1 := h
  · calc v1 * v1 = v1 ^ 2 := by ring
      _ = 1 := h

lemma reduce_to_e1 (v : Fin 4 → ℝ) (h0 : v 0 = 0) (h_mass : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1) :
  ∃ G : Matrix (Fin 4) (Fin 4) ℝ, IsRealGivens G ∧
    Matrix.mulVec G v = ![0, 1, 0, 0] := by
  
  obtain ⟨c1, s1, hc1, hs1, hsq1⟩ := reduce_v3_to_0 (v 0) (v 1) (v 3)
  let v' := Matrix.mulVec (givens_zx c1 s1) v
  have hv'_0 : v' 0 = 0 := by dsimp [v']; rw [givens_zx_mulVec, vec4_0, h0]
  have hv'_1 : v' 1 = c1 * v 1 + s1 * v 3 := by dsimp [v']; rw [givens_zx_mulVec, vec4_1]
  have hv'_2 : v' 2 = v 2 := by dsimp [v']; rw [givens_zx_mulVec, vec4_2]
  have hv'_3 : v' 3 = 0 := by
    dsimp [v']
    rw [givens_zx_mulVec, vec4_3]
    exact hs1

  have h_mass2 : v' 1 ^ 2 + v' 2 ^ 2 = 1 := by
    calc v' 1 ^ 2 + v' 2 ^ 2 = v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2 := by rw [hv'_3]; ring
      _ = -(v' 0 ^ 2 - (v' 1 ^ 2 + v' 2 ^ 2 + v' 3 ^ 2)) := by rw [hv'_0]; ring
      _ = -(v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2)) := by
        have := IsRealGivens_preserves_mass_shell (IsRealGivens.zx c1 s1 hc1) v
        rw [this]
      _ = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by rw [h0]; ring
      _ = 1 := h_mass

  
  obtain ⟨c2, s2, hc2, hs2, hsq2⟩ := reduce_v2_to_0 (v' 0) (v' 1) (v' 2) (v' 3)
  let v'' := Matrix.mulVec (givens_xy c2 s2) v'
  have hv''_0 : v'' 0 = 0 := by dsimp [v'']; rw [givens_xy_mulVec, vec4_0, hv'_0]
  have hv''_1 : v'' 1 = c2 * v' 1 - s2 * v' 2 := by dsimp [v'']; rw [givens_xy_mulVec, vec4_1]
  have hv''_2 : v'' 2 = 0 := by
    dsimp [v'']
    rw [givens_xy_mulVec, vec4_2]
    exact hs2
  have hv''_3 : v'' 3 = 0 := by dsimp [v'']; rw [givens_xy_mulVec, vec4_3, hv'_3]

  have h_mass3 : v'' 1 ^ 2 = 1 := by
    calc v'' 1 ^ 2 = (c2 * v' 1 - s2 * v' 2) ^ 2 := by rw [hv''_1]
      _ = v' 1 ^ 2 + v' 2 ^ 2 := hsq2
      _ = 1 := h_mass2

  
  obtain ⟨c3, s3, hc3, hpos3, hs_zero⟩ := reduce_v1_to_pos_1 (v'' 1) h_mass3
  let v''' := Matrix.mulVec (givens_xy c3 s3) v''
  have hv'''_0 : v''' 0 = 0 := by dsimp [v''']; rw [givens_xy_mulVec, vec4_0, hv''_0]
  have hv'''_1 : v''' 1 = 1 := by
    dsimp [v''']
    rw [givens_xy_mulVec, vec4_1, hs_zero, hv''_2]
    calc c3 * v'' 1 - 0 * 0 = c3 * v'' 1 := by ring
      _ = 1 := hpos3
  have hv'''_2 : v''' 2 = 0 := by
    dsimp [v''']
    rw [givens_xy_mulVec, vec4_2, hs_zero, hv''_2]
    ring
  have hv'''_3 : v''' 3 = 0 := by dsimp [v''']; rw [givens_xy_mulVec, vec4_3, hv''_3]

  use (givens_xy c3 s3) * (givens_xy c2 s2) * (givens_zx c1 s1)
  refine ⟨?_, ?_⟩
  · apply IsRealGivens.mul
    · apply IsRealGivens.mul
      · exact IsRealGivens.xy c3 s3 hc3
      · exact IsRealGivens.xy c2 s2 hc2
    · exact IsRealGivens.zx c1 s1 hc1
  · have h_mul : Matrix.mulVec ((givens_xy c3 s3) * (givens_xy c2 s2) * (givens_zx c1 s1)) v = v''' := by
      dsimp [v''', v'', v']
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h_mul]
    ext i
    fin_cases i
    · exact hv'''_0
    · exact hv'''_1
    · exact hv'''_2
    · exact hv'''_3

lemma reduce_to_e2 (v : Fin 4 → ℝ) (h0 : v 0 = 0) (h1 : v 1 = 0) (h_mass : v 2 ^ 2 + v 3 ^ 2 = 1) :
  ∃ G : Matrix (Fin 4) (Fin 4) ℝ, IsRealGivens G ∧
    Matrix.mulVec G v = ![0, 0, 1, 0] := by
  let G1 := givens_xy 0 (-1)
  have hc1 : (0:ℝ)^2 + (-1:ℝ)^2 = 1 := by ring
  let v' := Matrix.mulVec G1 v
  have hv'_0 : v' 0 = 0 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_0, h0]
  have hv'_1 : v' 1 = v 2 := by
    dsimp [v', G1]
    rw [givens_xy_mulVec, vec4_1, h1]
    ring
  have hv'_2 : v' 2 = 0 := by
    dsimp [v', G1]
    rw [givens_xy_mulVec, vec4_2, h1]
    ring
  have hv'_3 : v' 3 = v 3 := by dsimp [v', G1]; rw [givens_xy_mulVec, vec4_3]

  have h_mass2 : v' 1 ^ 2 + v' 3 ^ 2 = 1 := by
    calc v' 1 ^ 2 + v' 3 ^ 2 = v 2 ^ 2 + v 3 ^ 2 := by rw [hv'_1, hv'_3]
      _ = 1 := h_mass

  obtain ⟨c2, s2, hc2, hs2, hsq2⟩ := reduce_v3_to_0 (v' 0) (v' 1) (v' 3)
  let v'' := Matrix.mulVec (givens_zx c2 s2) v'
  have hv''_0 : v'' 0 = 0 := by dsimp [v'']; rw [givens_zx_mulVec, vec4_0, hv'_0]
  have hv''_1 : v'' 1 = c2 * v' 1 + s2 * v' 3 := by dsimp [v'']; rw [givens_zx_mulVec, vec4_1]
  have hv''_2 : v'' 2 = 0 := by dsimp [v'']; rw [givens_zx_mulVec, vec4_2, hv'_2]
  have hv''_3 : v'' 3 = 0 := by dsimp [v'']; rw [givens_zx_mulVec, vec4_3]; exact hs2

  have h_mass3 : v'' 1 ^ 2 = 1 := by
    calc v'' 1 ^ 2 = (c2 * v' 1 + s2 * v' 3) ^ 2 := by rw [hv''_1]
      _ = v' 1 ^ 2 + v' 3 ^ 2 := hsq2
      _ = 1 := h_mass2

  obtain ⟨c3, s3, hc3, hpos3, hs_zero⟩ := reduce_v1_to_pos_1 (v'' 1) h_mass3
  let v''' := Matrix.mulVec (givens_zx c3 s3) v''
  have hv'''_0 : v''' 0 = 0 := by dsimp [v''']; rw [givens_zx_mulVec, vec4_0, hv''_0]
  have hv'''_1 : v''' 1 = 1 := by
    dsimp [v''']
    rw [givens_zx_mulVec, vec4_1, hs_zero, hv''_3]
    calc c3 * v'' 1 + 0 * 0 = c3 * v'' 1 := by ring
      _ = 1 := hpos3
  have hv'''_2 : v''' 2 = 0 := by dsimp [v''']; rw [givens_zx_mulVec, vec4_2, hv''_2]
  have hv'''_3 : v''' 3 = 0 := by
    dsimp [v''']
    rw [givens_zx_mulVec, vec4_3, hs_zero, hv''_3]
    ring

  let G4 := givens_xy 0 1
  have hc4 : (0:ℝ)^2 + (1:ℝ)^2 = 1 := by ring
  let v'''' := Matrix.mulVec G4 v'''
  have hv''''_0 : v'''' 0 = 0 := by dsimp [v'''', G4]; rw [givens_xy_mulVec, vec4_0, hv'''_0]
  have hv''''_1 : v'''' 1 = 0 := by
    dsimp [v'''', G4]
    rw [givens_xy_mulVec, vec4_1, hv'''_2]
    ring
  have hv''''_2 : v'''' 2 = 1 := by
    dsimp [v'''', G4]
    rw [givens_xy_mulVec, vec4_2, hv'''_1, hv'''_2]
    ring
  have hv''''_3 : v'''' 3 = 0 := by dsimp [v'''', G4]; rw [givens_xy_mulVec, vec4_3, hv'''_3]

  use G4 * (givens_zx c3 s3) * (givens_zx c2 s2) * G1
  refine ⟨?_, ?_⟩
  · apply IsRealGivens.mul
    · apply IsRealGivens.mul
      · apply IsRealGivens.mul
        · exact IsRealGivens.xy 0 1 hc4
        · exact IsRealGivens.zx c3 s3 hc3
      · exact IsRealGivens.zx c2 s2 hc2
    · exact IsRealGivens.xy 0 (-1) hc1
  · have h_mul : Matrix.mulVec (G4 * (givens_zx c3 s3) * (givens_zx c2 s2) * G1) v = v'''' := by
      dsimp [v'''', v''', v'', v']
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h_mul]
    ext i
    fin_cases i
    · exact hv''''_0
    · exact hv''''_1
    · exact hv''''_2
    · exact hv''''_3

end Geometry.RealGivens

lemma sin_arccos_of_pos {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (hs : 0 ≤ s) : sin (arccos c) = s := by
  have h1 : c^2 ≤ 1 := by
    calc c^2 ≤ c^2 + s^2 := by
           have hs2 : 0 ≤ s^2 := sq_nonneg s
           exact le_add_of_nonneg_right hs2
         _ = 1 := h
  have hc1 : -1 ≤ c := by nlinarith
  have hc2 : c ≤ 1 := by nlinarith
  have h_trig : sin (arccos c) ^ 2 + cos (arccos c) ^ 2 = 1 := sin_sq_add_cos_sq _
  have hc : cos (arccos c) = c := cos_arccos hc1 hc2
  rw [hc] at h_trig
  have h_sq : sin (arccos c) ^ 2 = s ^ 2 := by linarith [h_trig, h]
  have h_mul : (sin (arccos c) - s) * (sin (arccos c) + s) = 0 := by
    calc (sin (arccos c) - s) * (sin (arccos c) + s) = sin (arccos c) ^ 2 - s ^ 2 := by ring
      _ = 0 := by linarith
  cases mul_eq_zero.mp h_mul with
  | inl h_eq => exact sub_eq_zero.mp h_eq
  | inr h_eq =>
    have h_sin_nonneg : 0 ≤ sin (arccos c) := sin_nonneg_of_mem_Icc ⟨arccos_nonneg c, arccos_le_pi c⟩
    have h_eq2 := eq_neg_of_add_eq_zero_left h_eq
    have hs_neg : s ≤ 0 := by linarith
    have hs_zero : s = 0 := le_antisymm hs_neg hs
    rw [hs_zero] at h_eq2 ⊢
    linarith

lemma sin_arccos_of_neg {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (hs : ¬ 0 ≤ s) : sin (arccos c) = -s := by
  have h1 : c^2 ≤ 1 := by
    calc c^2 ≤ c^2 + s^2 := by
           have hs2 : 0 ≤ s^2 := sq_nonneg s
           exact le_add_of_nonneg_right hs2
         _ = 1 := h
  have hc1 : -1 ≤ c := by nlinarith
  have hc2 : c ≤ 1 := by nlinarith
  have h_trig : sin (arccos c) ^ 2 + cos (arccos c) ^ 2 = 1 := sin_sq_add_cos_sq _
  have hc : cos (arccos c) = c := cos_arccos hc1 hc2
  rw [hc] at h_trig
  have h_sq : sin (arccos c) ^ 2 = s ^ 2 := by linarith [h_trig, h]
  have h_mul : (sin (arccos c) - s) * (sin (arccos c) + s) = 0 := by
    calc (sin (arccos c) - s) * (sin (arccos c) + s) = sin (arccos c) ^ 2 - s ^ 2 := by ring
      _ = 0 := by linarith
  cases mul_eq_zero.mp h_mul with
  | inl h_eq =>
    have h_sin_nonneg : 0 ≤ sin (arccos c) := sin_nonneg_of_mem_Icc ⟨arccos_nonneg c, arccos_le_pi c⟩
    have hs_pos : 0 ≤ s := by linarith
    contradiction
  | inr h_eq =>
    linarith

noncomputable def circle_path (c s : ℝ) : ℝ → ℝ × ℝ :=
  let θ := if s ≥ 0 then Real.arccos c else - Real.arccos c
  fun t => (Real.cos ((1-t) * θ), Real.sin ((1-t) * θ))

lemma circle_path_0 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : circle_path c s 0 = (c, s) := by
  dsimp [circle_path]
  have h_sub : (1 - (0 : ℝ)) = 1 := by ring
  rw [h_sub, one_mul]
  have h1 : c^2 ≤ 1 := by
    calc c^2 ≤ c^2 + s^2 := by
           have hs2 : 0 ≤ s^2 := sq_nonneg s
           exact le_add_of_nonneg_right hs2
         _ = 1 := h
  have hc1 : -1 ≤ c := by nlinarith
  have hc2 : c ≤ 1 := by nlinarith
  split_ifs with hs
  · ext
    · exact cos_arccos hc1 hc2
    · exact sin_arccos_of_pos h hs
  · ext
    · rw [cos_neg, cos_arccos hc1 hc2]
    · rw [sin_neg, sin_arccos_of_neg h hs]
      ring

lemma circle_path_1 (c s : ℝ) : circle_path c s 1 = (1, 0) := by
  dsimp [circle_path]
  have h_sub : (1 - (1 : ℝ)) = 0 := by ring
  rw [h_sub, zero_mul, cos_zero, sin_zero]

lemma circle_path_sq (c s : ℝ) (t : ℝ) : (circle_path c s t).1^2 + (circle_path c s t).2^2 = 1 := by
  dsimp [circle_path]
  exact cos_sq_add_sin_sq _

noncomputable def tx_path (s : ℝ) : ℝ → ℝ × ℝ :=
  fun t => (Real.sqrt (1 + ((1-t) * s)^2), (1-t) * s)

lemma tx_path_sq (s : ℝ) (t : ℝ) : (tx_path s t).1^2 - (tx_path s t).2^2 = 1 := by
  dsimp [tx_path]
  have h_sq : Real.sqrt (1 + ((1 - t) * s) ^ 2) ^ 2 = 1 + ((1 - t) * s) ^ 2 := by
    apply Real.sq_sqrt
    positivity
  rw [h_sq]
  ring

lemma tx_path_c_pos (s : ℝ) (t : ℝ) : (tx_path s t).1 > 0 := by
  dsimp [tx_path]
  apply Real.sqrt_pos.mpr
  positivity

lemma tx_path_0 (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (hpos : c > 0) : tx_path s 0 = (c, s) := by
  dsimp [tx_path]
  have h_sub : (1 - (0 : ℝ)) = 1 := by ring
  rw [h_sub, one_mul]
  ext
  · have hc_sq : c^2 = 1 + s^2 := by linarith
    have hc_eq : Real.sqrt (c^2) = Real.sqrt (1 + s^2) := by rw [hc_sq]
    have hc_sqrt : Real.sqrt (c^2) = c := Real.sqrt_sq (by linarith)
    rw [hc_sqrt] at hc_eq
    exact hc_eq.symm
  · rfl

lemma tx_path_1 (s : ℝ) : tx_path s 1 = (1, 0) := by
  dsimp [tx_path]
  have h_sub : (1 - (1 : ℝ)) = 0 := by ring
  rw [h_sub, zero_mul]
  ext
  · simp
  · rfl
