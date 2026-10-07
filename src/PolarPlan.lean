import Mathlib
import Spinor
import Minkowski
import MatrixAnalysis
import MatrixExpS
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Exponential

open Complex Matrix Geometry Geometry.SpinorTopology Geometry.MatrixAnalysis
open scoped Matrix ComplexOrder

lemma isHerm_two_by_two (a d : ℝ) (c : ℂ) :
    (!![(a : ℂ), c; star c, (d : ℂ)]).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma complex_alg_id (a d : ℝ) (c v0 v1 : ℂ) :
    a * (a * normSq v0 + d * normSq v1 + 2 * (star v0 * c * v1).re) =
    normSq (a * v0 + c * v1) + (a * d - normSq c) * normSq v1 := by
  simp [normSq, add_mul, mul_add, mul_comm, mul_left_comm]
  ring

lemma posDef_two_by_two (a d : ℝ) (c : ℂ) (ha : 0 < a) (hdet : 0 < a * d - normSq c) :
    (!![(a : ℂ), c; star c, (d : ℂ)]).PosDef := by
  constructor
  · exact isHerm_two_by_two a d c
  · intro v hv
    have h_sum1 : v.sum (fun i xi => v.sum fun j xj => star xi * !![(a : ℂ), c; star c, (d : ℂ)] i j * xj) =
      ∑ i : Fin 2, ∑ j : Fin 2, star (v i) * !![(a : ℂ), c; star c, (d : ℂ)] i j * (v j) := by
      rw [Finsupp.sum_fintype]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finsupp.sum_fintype]
        · intro j; simp
      · intro i; simp
    rw [h_sum1]
    have h_expand : (∑ i : Fin 2, ∑ j : Fin 2, star (v i) * !![(a : ℂ), c; star c, (d : ℂ)] i j * (v j)) =
      ((a * normSq (v 0) + d * normSq (v 1) + 2 * (star (v 0) * c * v 1).re : ℝ) : ℂ) := by
      simp [Fin.sum_univ_two, normSq_eq_conj_mul_self]
      apply Complex.ext
      · simp; ring
      · simp; ring
    rw [h_expand]
    have h_lt : (0 : ℂ) < ((a * normSq (v 0) + d * normSq (v 1) + 2 * (star (v 0) * c * v 1).re : ℝ) : ℂ) ↔
                (0 : ℝ) < a * normSq (v 0) + d * normSq (v 1) + 2 * (star (v 0) * c * v 1).re := by
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, rfl⟩
    rw [h_lt]
    have h_mul_a : 0 < a * (a * normSq (v 0) + d * normSq (v 1) + 2 * (star (v 0) * c * v 1).re) ↔
                   0 < a * normSq (v 0) + d * normSq (v 1) + 2 * (star (v 0) * c * v 1).re := by
      exact mul_pos_iff_of_pos_left ha
    rw [← h_mul_a]
    rw [complex_alg_id]
    have h_nonneg1 : 0 ≤ normSq (a * v 0 + c * v 1) := normSq_nonneg _
    have h_nonneg2 : 0 ≤ (a * d - normSq c) * normSq (v 1) := mul_nonneg (le_of_lt hdet) (normSq_nonneg _)
    have h_sum_pos : 0 ≤ normSq (a * v 0 + c * v 1) + (a * d - normSq c) * normSq (v 1) := add_nonneg h_nonneg1 h_nonneg2
    by_contra h_not_pos
    have h_zero : normSq (a * v 0 + c * v 1) + (a * d - normSq c) * normSq (v 1) = 0 := le_antisymm (not_lt.mp h_not_pos) h_sum_pos
    have h_v1_zero : normSq (v 1) = 0 := by
      have h_nonneg3 : 0 ≤ normSq (a * v 0 + c * v 1) := normSq_nonneg _
      have h_zero2 : (a * d - normSq c) * normSq (v 1) ≤ 0 := by linarith
      have h_nonneg4 : 0 ≤ (a * d - normSq c) * normSq (v 1) := mul_nonneg (le_of_lt hdet) (normSq_nonneg _)
      exact (mul_eq_zero.mp (le_antisymm h_zero2 h_nonneg4)).resolve_left (ne_of_gt hdet)
    have h_v1 : v 1 = 0 := normSq_eq_zero.mp h_v1_zero
    have h_v0_zero : normSq (a * v 0 + c * v 1) = 0 := by
      have h_nonneg3 : 0 ≤ (a * d - normSq c) * normSq (v 1) := mul_nonneg (le_of_lt hdet) (normSq_nonneg _)
      have h_zero2 : normSq (a * v 0 + c * v 1) ≤ 0 := by linarith
      exact le_antisymm h_zero2 h_nonneg1
    have h_v0_eq : a * v 0 + c * v 1 = 0 := normSq_eq_zero.mp h_v0_zero
    rw [h_v1, mul_zero, add_zero] at h_v0_eq
    have h_v0 : v 0 = 0 := by
      have h_a_ne : (a : ℂ) ≠ 0 := by simp [ne_of_gt ha]
      exact mul_eq_zero.mp h_v0_eq |>.resolve_left h_a_ne
    have hv_zero : v = 0 := by
      ext i
      fin_cases i
      · exact h_v0
      · exact h_v1
    exact hv hv_zero

lemma posDef_vec_to_spinor (x : Fin 4 → ℝ) (hx : x ∈ forward_light_cone) :
    (vec_to_spinor (fun i => (x i : ℂ))).PosDef := by
  have h_t : 0 < x 0 := by
    rcases hx with ⟨h_pos, _⟩
    exact h_pos
  have h_normSq_I : normSq ((x 1 : ℂ) - (x 2 : ℂ) * I) = (x 1)^2 + (x 2)^2 := by
    simp [normSq]
    ring
  have h_norm : 0 < (x 0)^2 - (x 1)^2 - (x 2)^2 - (x 3)^2 := by
    rcases hx with ⟨_, h_norm_ineq⟩
    rw [minkowskiInner_explicit] at h_norm_ineq
    have h_sq1 : x 1 * x 1 = (x 1)^2 := by ring
    have h_sq2 : x 2 * x 2 = (x 2)^2 := by ring
    have h_sq3 : x 3 * x 3 = (x 3)^2 := by ring
    have h_sq0 : x 0 * x 0 = (x 0)^2 := by ring
    linarith
  have h_a : 0 < x 0 + x 3 := by
    have h1 : (x 3)^2 ≤ (x 1)^2 + (x 2)^2 + (x 3)^2 := by
      have h_sq1 : 0 ≤ (x 1)^2 := sq_nonneg (x 1)
      have h_sq2 : 0 ≤ (x 2)^2 := sq_nonneg (x 2)
      linarith
    have h2 : (x 3)^2 < (x 0)^2 := by linarith
    have h3 : - (x 0) < x 3 ∧ x 3 < x 0 := by
      have h_abs : |x 3| < |x 0| := by
        rw [← sq_lt_sq]
        exact h2
      have h_x0_abs : |x 0| = x 0 := abs_of_pos h_t
      rw [h_x0_abs] at h_abs
      rw [abs_lt] at h_abs
      exact h_abs
    linarith
  have h_det : 0 < (x 0 + x 3) * (x 0 - x 3) - normSq ((x 1 : ℂ) - (x 2 : ℂ) * I) := by
    rw [h_normSq_I]
    have h_diff : (x 0 + x 3) * (x 0 - x 3) = (x 0)^2 - (x 3)^2 := by ring
    rw [h_diff]
    linarith
  have h_matrix : vec_to_spinor (fun i => (x i : ℂ)) = !![((x 0 + x 3 : ℝ) : ℂ), (x 1 : ℂ) - (x 2 : ℂ) * I; star ((x 1 : ℂ) - (x 2 : ℂ) * I), ((x 0 - x 3 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [vec_to_spinor]
    · simp [vec_to_spinor]; ring
    · simp [vec_to_spinor]
    · simp [vec_to_spinor]; ring
  rw [h_matrix]
  exact posDef_two_by_two (x 0 + x 3) (x 0 - x 3) ((x 1 : ℂ) - (x 2 : ℂ) * I) h_a h_det




noncomputable def P_diag (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp t : ℂ), 0; 0, (Real.exp (-t) : ℂ)]

lemma P_diag_inv (t : ℝ) : (P_diag t)⁻¹ = !![(Real.exp (-t) : ℂ), 0; 0, (Real.exp t : ℂ)] := by
  have h_det : (P_diag t).det ≠ 0 := by
    have h_det_calc : (P_diag t).det = cexp t * cexp (-t) := by
      simp [P_diag, Matrix.det_fin_two]
    rw [h_det_calc]
    have h0 : (t : ℂ) + (-t : ℂ) = 0 := by ring
    rw [← Complex.exp_add, h0, Complex.exp_zero]
    exact one_ne_zero
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j
  · simp [P_diag, Matrix.mul_apply, Fin.sum_univ_two]
    have h0 : (t : ℂ) + (-t : ℂ) = 0 := by ring
    rw [← Complex.exp_add, h0, Complex.exp_zero]
  · simp [P_diag, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [P_diag, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [P_diag, Matrix.mul_apply, Fin.sum_univ_two]
    have h0 : (-t : ℂ) + (t : ℂ) = 0 := by ring
    rw [← Complex.exp_add, h0, Complex.exp_zero]

noncomputable def V_s_diag (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-I / 2 : ℂ) • (P_diag (s * t) * U * (P_diag (s * t))⁻¹ - (P_diag (s * t))⁻¹ * U * P_diag (s * t)) +
  (1/2 : ℂ) • (P_diag (s * t) * V * (P_diag (s * t))⁻¹ + (P_diag (s * t))⁻¹ * V * P_diag (s * t))

lemma V_s_diag_zero (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    V_s_diag t U V 0 = V := by
  dsimp [V_s_diag]
  have h0 : 0 * t = 0 := MulZeroClass.zero_mul t
  rw [h0]
  have h_P0 : P_diag 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals {
      simp [P_diag]
    }
  rw [h_P0]
  have h_P0_inv : (1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = 1 := by
    apply Matrix.inv_eq_right_inv
    exact Matrix.mul_one 1
  rw [h_P0_inv]
  simp
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma V_s_diag_00 (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    (V_s_diag t U V s) 0 0 = V 0 0 := by
  have hP00 : P_diag (s * t) 0 0 = (Real.exp (s * t) : ℂ) := rfl
  have hP01 : P_diag (s * t) 0 1 = 0 := rfl
  have hP10 : P_diag (s * t) 1 0 = 0 := rfl
  have hP11 : P_diag (s * t) 1 1 = (Real.exp (-(s * t)) : ℂ) := rfl
  have hI00 : (P_diag (s * t))⁻¹ 0 0 = (Real.exp (-(s * t)) : ℂ) := by rw [P_diag_inv]; rfl
  have hI01 : (P_diag (s * t))⁻¹ 0 1 = 0 := by rw [P_diag_inv]; rfl
  have hI10 : (P_diag (s * t))⁻¹ 1 0 = 0 := by rw [P_diag_inv]; rfl
  have hI11 : (P_diag (s * t))⁻¹ 1 1 = (Real.exp (s * t) : ℂ) := by rw [P_diag_inv]; rfl

  have hr : (Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hr' : Real.exp (s * t) * Real.exp (-(s * t)) = 1 := by
      rw [← Real.exp_add]
      have h0 : s * t + -(s * t) = 0 := by ring
      rw [h0, Real.exp_zero]
    rw [hr', Complex.ofReal_one]

  have hr2 : (Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hr' : Real.exp (-(s * t)) * Real.exp (s * t) = 1 := by
      rw [← Real.exp_add]
      have h0 : -(s * t) + s * t = 0 := by ring
      rw [h0, Real.exp_zero]
    rw [hr', Complex.ofReal_one]

  have h_PUP : (P_diag (s * t) * U * (P_diag (s * t))⁻¹) 0 0 = U 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP00, hP01, hI00, hI10, mul_zero, zero_mul, add_zero]
    calc
      (Real.exp (s * t) : ℂ) * U 0 0 * (Real.exp (-(s * t)) : ℂ)
        = U 0 0 * ((Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = U 0 0 * 1 := by rw [hr]
      _ = U 0 0 := mul_one (U 0 0)

  have h_IUP : ((P_diag (s * t))⁻¹ * U * P_diag (s * t)) 0 0 = U 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI00, hI01, hP00, hP10, mul_zero, zero_mul, add_zero]
    calc
      (Real.exp (-(s * t)) : ℂ) * U 0 0 * (Real.exp (s * t) : ℂ)
        = U 0 0 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = U 0 0 * 1 := by rw [hr2]
      _ = U 0 0 := mul_one (U 0 0)

  have h_PVP : (P_diag (s * t) * V * (P_diag (s * t))⁻¹) 0 0 = V 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP00, hP01, hI00, hI10, mul_zero, zero_mul, add_zero]
    calc
      (Real.exp (s * t) : ℂ) * V 0 0 * (Real.exp (-(s * t)) : ℂ)
        = V 0 0 * ((Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = V 0 0 * 1 := by rw [hr]
      _ = V 0 0 := mul_one (V 0 0)

  have h_IVP : ((P_diag (s * t))⁻¹ * V * P_diag (s * t)) 0 0 = V 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI00, hI01, hP00, hP10, mul_zero, zero_mul, add_zero]
    calc
      (Real.exp (-(s * t)) : ℂ) * V 0 0 * (Real.exp (s * t) : ℂ)
        = V 0 0 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = V 0 0 * 1 := by rw [hr2]
      _ = V 0 0 := mul_one (V 0 0)

  dsimp [V_s_diag]
  simp only [h_PUP, h_IUP, h_PVP, h_IVP]
  ring

lemma V_s_diag_11 (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    (V_s_diag t U V s) 1 1 = V 1 1 := by
  have hP00 : P_diag (s * t) 0 0 = (Real.exp (s * t) : ℂ) := rfl
  have hP01 : P_diag (s * t) 0 1 = 0 := rfl
  have hP10 : P_diag (s * t) 1 0 = 0 := rfl
  have hP11 : P_diag (s * t) 1 1 = (Real.exp (-(s * t)) : ℂ) := rfl
  have hI00 : (P_diag (s * t))⁻¹ 0 0 = (Real.exp (-(s * t)) : ℂ) := by rw [P_diag_inv]; rfl
  have hI01 : (P_diag (s * t))⁻¹ 0 1 = 0 := by rw [P_diag_inv]; rfl
  have hI10 : (P_diag (s * t))⁻¹ 1 0 = 0 := by rw [P_diag_inv]; rfl
  have hI11 : (P_diag (s * t))⁻¹ 1 1 = (Real.exp (s * t) : ℂ) := by rw [P_diag_inv]; rfl

  have hr : (Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hr' : Real.exp (s * t) * Real.exp (-(s * t)) = 1 := by
      rw [← Real.exp_add]
      have h0 : s * t + -(s * t) = 0 := by ring
      rw [h0, Real.exp_zero]
    rw [hr', Complex.ofReal_one]

  have hr2 : (Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hr' : Real.exp (-(s * t)) * Real.exp (s * t) = 1 := by
      rw [← Real.exp_add]
      have h0 : -(s * t) + s * t = 0 := by ring
      rw [h0, Real.exp_zero]
    rw [hr', Complex.ofReal_one]

  have h_PUP : (P_diag (s * t) * U * (P_diag (s * t))⁻¹) 1 1 = U 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP11, hP10, hI11, hI01, mul_zero, zero_mul, zero_add]
    calc
      _ = U 1 1 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = U 1 1 * 1 := by rw [hr2]
      _ = U 1 1 := mul_one (U 1 1)

  have h_IUP : ((P_diag (s * t))⁻¹ * U * P_diag (s * t)) 1 1 = U 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI11, hI10, hP11, hP01, mul_zero, zero_mul, zero_add]
    calc
      _ = U 1 1 * ((Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = U 1 1 * 1 := by rw [hr]
      _ = U 1 1 := mul_one (U 1 1)

  have h_PVP : (P_diag (s * t) * V * (P_diag (s * t))⁻¹) 1 1 = V 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP11, hP10, hI11, hI01, mul_zero, zero_mul, zero_add]
    calc
      _ = V 1 1 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = V 1 1 * 1 := by rw [hr2]
      _ = V 1 1 := mul_one (V 1 1)

  have h_IVP : ((P_diag (s * t))⁻¹ * V * P_diag (s * t)) 1 1 = V 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI11, hI10, hP11, hP01, mul_zero, zero_mul, zero_add]
    calc
      _ = V 1 1 * ((Real.exp (s * t) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = V 1 1 * 1 := by rw [hr]
      _ = V 1 1 := mul_one (V 1 1)

  dsimp [V_s_diag]
  simp [h_PUP, h_IUP, h_PVP, h_IVP]
  ring

lemma V_s_diag_01 (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    (V_s_diag t U V s) 0 1 =
      ((Real.exp (2 * (s * t)) : ℂ)) * (-I / 2 * U 0 1 + 1 / 2 * V 0 1) +
      ((Real.exp (-(2 * (s * t))) : ℂ)) * (I / 2 * U 0 1 + 1 / 2 * V 0 1) := by
  have hP00 : P_diag (s * t) 0 0 = (Real.exp (s * t) : ℂ) := rfl
  have hP01 : P_diag (s * t) 0 1 = 0 := rfl
  have hP10 : P_diag (s * t) 1 0 = 0 := rfl
  have hP11 : P_diag (s * t) 1 1 = (Real.exp (-(s * t)) : ℂ) := rfl
  have hI00 : (P_diag (s * t))⁻¹ 0 0 = (Real.exp (-(s * t)) : ℂ) := by rw [P_diag_inv]; rfl
  have hI01 : (P_diag (s * t))⁻¹ 0 1 = 0 := by rw [P_diag_inv]; rfl
  have hI10 : (P_diag (s * t))⁻¹ 1 0 = 0 := by rw [P_diag_inv]; rfl
  have hI11 : (P_diag (s * t))⁻¹ 1 1 = (Real.exp (s * t) : ℂ) := by rw [P_diag_inv]; rfl

  have h_exp_2 : (Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ) = (Real.exp (2 * (s * t)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have h : s * t + s * t = 2 * (s * t) := by ring
    rw [h]

  have h_exp_neg2 : (Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ) = (Real.exp (-(2 * (s * t))) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have h : -(s * t) + -(s * t) = -(2 * (s * t)) := by ring
    rw [h]

  have h_PUP : (P_diag (s * t) * U * (P_diag (s * t))⁻¹) 0 1 = (Real.exp (2 * (s * t)) : ℂ) * U 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP00, hP01, hI01, hI11, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = U 0 1 * ((Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = U 0 1 * (Real.exp (2 * (s * t)) : ℂ) := by rw [h_exp_2]
      _ = (Real.exp (2 * (s * t)) : ℂ) * U 0 1 := by ring

  have h_IUP : ((P_diag (s * t))⁻¹ * U * P_diag (s * t)) 0 1 = (Real.exp (-(2 * (s * t))) : ℂ) * U 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI00, hI01, hP01, hP11, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = U 0 1 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = U 0 1 * (Real.exp (-(2 * (s * t))) : ℂ) := by rw [h_exp_neg2]
      _ = (Real.exp (-(2 * (s * t))) : ℂ) * U 0 1 := by ring

  have h_PVP : (P_diag (s * t) * V * (P_diag (s * t))⁻¹) 0 1 = (Real.exp (2 * (s * t)) : ℂ) * V 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP00, hP01, hI01, hI11, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = V 0 1 * ((Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = V 0 1 * (Real.exp (2 * (s * t)) : ℂ) := by rw [h_exp_2]
      _ = (Real.exp (2 * (s * t)) : ℂ) * V 0 1 := by ring

  have h_IVP : ((P_diag (s * t))⁻¹ * V * P_diag (s * t)) 0 1 = (Real.exp (-(2 * (s * t))) : ℂ) * V 0 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI00, hI01, hP01, hP11, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = V 0 1 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = V 0 1 * (Real.exp (-(2 * (s * t))) : ℂ) := by rw [h_exp_neg2]
      _ = (Real.exp (-(2 * (s * t))) : ℂ) * V 0 1 := by ring

  dsimp [V_s_diag]
  simp only [h_PUP, h_IUP, h_PVP, h_IVP]
  ring

lemma V_s_diag_10 (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    (V_s_diag t U V s) 1 0 =
      ((Real.exp (-(2 * (s * t))) : ℂ)) * (-I / 2 * U 1 0 + 1 / 2 * V 1 0) +
      ((Real.exp (2 * (s * t)) : ℂ)) * (I / 2 * U 1 0 + 1 / 2 * V 1 0) := by
  have hP00 : P_diag (s * t) 0 0 = (Real.exp (s * t) : ℂ) := rfl
  have hP01 : P_diag (s * t) 0 1 = 0 := rfl
  have hP10 : P_diag (s * t) 1 0 = 0 := rfl
  have hP11 : P_diag (s * t) 1 1 = (Real.exp (-(s * t)) : ℂ) := rfl
  have hI00 : (P_diag (s * t))⁻¹ 0 0 = (Real.exp (-(s * t)) : ℂ) := by rw [P_diag_inv]; rfl
  have hI01 : (P_diag (s * t))⁻¹ 0 1 = 0 := by rw [P_diag_inv]; rfl
  have hI10 : (P_diag (s * t))⁻¹ 1 0 = 0 := by rw [P_diag_inv]; rfl
  have hI11 : (P_diag (s * t))⁻¹ 1 1 = (Real.exp (s * t) : ℂ) := by rw [P_diag_inv]; rfl

  have h_exp_2 : (Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ) = (Real.exp (2 * (s * t)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have h : s * t + s * t = 2 * (s * t) := by ring
    rw [h]

  have h_exp_neg2 : (Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ) = (Real.exp (-(2 * (s * t))) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have h : -(s * t) + -(s * t) = -(2 * (s * t)) := by ring
    rw [h]

  have h_PUP : (P_diag (s * t) * U * (P_diag (s * t))⁻¹) 1 0 = (Real.exp (-(2 * (s * t))) : ℂ) * U 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP10, hP11, hI00, hI10, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = U 1 0 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = U 1 0 * (Real.exp (-(2 * (s * t))) : ℂ) := by rw [h_exp_neg2]
      _ = (Real.exp (-(2 * (s * t))) : ℂ) * U 1 0 := by ring

  have h_IUP : ((P_diag (s * t))⁻¹ * U * P_diag (s * t)) 1 0 = (Real.exp (2 * (s * t)) : ℂ) * U 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI10, hI11, hP00, hP10, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = U 1 0 * ((Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = U 1 0 * (Real.exp (2 * (s * t)) : ℂ) := by rw [h_exp_2]
      _ = (Real.exp (2 * (s * t)) : ℂ) * U 1 0 := by ring

  have h_PVP : (P_diag (s * t) * V * (P_diag (s * t))⁻¹) 1 0 = (Real.exp (-(2 * (s * t))) : ℂ) * V 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP10, hP11, hI00, hI10, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = V 1 0 * ((Real.exp (-(s * t)) : ℂ) * (Real.exp (-(s * t)) : ℂ)) := by ring
      _ = V 1 0 * (Real.exp (-(2 * (s * t))) : ℂ) := by rw [h_exp_neg2]
      _ = (Real.exp (-(2 * (s * t))) : ℂ) * V 1 0 := by ring

  have h_IVP : ((P_diag (s * t))⁻¹ * V * P_diag (s * t)) 1 0 = (Real.exp (2 * (s * t)) : ℂ) * V 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hI10, hI11, hP00, hP10, mul_zero, zero_mul, add_zero, zero_add]
    calc
      _ = V 1 0 * ((Real.exp (s * t) : ℂ) * (Real.exp (s * t) : ℂ)) := by ring
      _ = V 1 0 * (Real.exp (2 * (s * t)) : ℂ) := by rw [h_exp_2]
      _ = (Real.exp (2 * (s * t)) : ℂ) * V 1 0 := by ring

  dsimp [V_s_diag]
  simp only [h_PUP, h_IUP, h_PVP, h_IVP]
  ring

lemma star_ofReal (x : ℝ) : star (x : ℂ) = (x : ℂ) := RCLike.conj_ofReal x

lemma V_s_diag_herm (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU_herm : U.IsHermitian) (hV_herm : V.IsHermitian) (s : ℝ) :
    (V_s_diag t U V s).IsHermitian := by
  dsimp [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j
  · change star ((V_s_diag t U V s) 0 0) = (V_s_diag t U V s) 0 0
    have h1 := V_s_diag_00 t U V s
    have h2 : star (V 0 0) = V 0 0 := by
      have := congr_fun (congr_fun hV_herm 0) 0
      exact this
    rw [h1, h2]
  · change star ((V_s_diag t U V s) 1 0) = (V_s_diag t U V s) 0 1
    have h1 := V_s_diag_01 t U V s
    have h2 := V_s_diag_10 t U V s
    rw [h1, h2]
    have hU_01 : star (U 0 1) = U 1 0 := congr_fun (congr_fun hU_herm 1) 0
    have hV_01 : star (V 0 1) = V 1 0 := congr_fun (congr_fun hV_herm 1) 0
    have hU_10 : star (U 1 0) = U 0 1 := congr_fun (congr_fun hU_herm 0) 1
    have hV_10 : star (V 1 0) = V 0 1 := congr_fun (congr_fun hV_herm 0) 1
    have h_star_I : star (I / 2 : ℂ) = -I / 2 := by simp
    have h_star_neg_I : star (-I / 2 : ℂ) = I / 2 := by simp
    have h_star_half : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [star_add, star_mul, hU_10, hV_10, h_star_I, h_star_neg_I, h_star_half, star_ofReal]
    ring
  · change star ((V_s_diag t U V s) 0 1) = (V_s_diag t U V s) 1 0
    have h1 := V_s_diag_10 t U V s
    have h2 := V_s_diag_01 t U V s
    rw [h1, h2]
    have hU_01 : star (U 0 1) = U 1 0 := congr_fun (congr_fun hU_herm 1) 0
    have hV_01 : star (V 0 1) = V 1 0 := congr_fun (congr_fun hV_herm 1) 0
    have hU_10 : star (U 1 0) = U 0 1 := congr_fun (congr_fun hU_herm 0) 1
    have hV_10 : star (V 1 0) = V 0 1 := congr_fun (congr_fun hV_herm 0) 1
    have h_star_I : star (I / 2 : ℂ) = -I / 2 := by simp
    have h_star_neg_I : star (-I / 2 : ℂ) = I / 2 := by simp
    have h_star_half : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [star_add, star_mul, hU_01, hV_01, h_star_I, h_star_neg_I, h_star_half, star_ofReal]
    ring
  · change star ((V_s_diag t U V s) 1 1) = (V_s_diag t U V s) 1 1
    have h1 := V_s_diag_11 t U V s
    have h2 : star (V 1 1) = V 1 1 := by
      have := congr_fun (congr_fun hV_herm 1) 1
      exact this
    rw [h1, h2]


lemma pos_re_of_pos {z : ℂ} (h : 0 < z) : 0 < z.re := by
  have h1 : 0 ≤ z := le_of_lt h
  have h2 : 0 ≠ z := ne_of_lt h
  rw [Complex.le_def] at h1
  rcases h1 with ⟨h_re, h_im⟩
  simp only [zero_re, zero_im] at h_re h_im
  have h_ne_zero : z.re ≠ 0 := by
    intro hc
    apply h2
    apply Complex.ext
    · simp only [zero_re]
      exact hc.symm
    · simp only [zero_im]
      exact h_im
  exact lt_of_le_of_ne h_re h_ne_zero.symm

lemma hermitian_diag_isReal {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.IsHermitian) (i : Fin 2) :
    M i i = ((M i i).re : ℂ) := by
  have h_eq : Mᴴ = M := hM
  have h : star (M i i) = M i i := by
    calc star (M i i) = Mᴴ i i := rfl
      _ = M i i := by rw [h_eq]
  apply Complex.ext
  · rfl
  · have h_im : -(M i i).im = (M i i).im := by
      have h2 := congr_arg Complex.im h
      exact h2
    have h_im2 : (M i i).im = 0 := by linarith
    simp [h_im2]

lemma pos_of_re_pos_and_im_zero (z : ℂ) (h1 : 0 < z.re) (h2 : z.im = 0) : 0 < z := by
  exact ⟨h1, h2.symm⟩

lemma expand_dotProduct_2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) =
    star (x 0) * M 0 0 * x 0 + star (x 0) * M 0 1 * x 1 +
    star (x 1) * M 1 0 * x 0 + star (x 1) * M 1 1 * x 1 := by
  dsimp [dotProduct, mulVec, vecMul]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  ring


lemma quadratic_form_re_poly (a d : ℝ) (b : ℂ) (u v : ℂ) :
    a * ((a : ℂ) * u * star u + b * star u * v + star b * u * star v + (d : ℂ) * v * star v).re =
    normSq ((a : ℂ) * u + b * v) + (a * d - normSq b) * normSq v := by
  simp [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im]
  ring


lemma posdef_2x2_iff (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) :
    M.PosDef ↔ 0 < (M 0 0).re ∧ 0 < (M 0 0 * M 1 1 - (M 0 1 * M 1 0)).re := by
  constructor
  · intro h
    have h1 : 0 < (M 0 0).re := by
      have := h.diag_pos (i := 0)
      exact pos_re_of_pos this
    have h2 : 0 < M.det.re := by
      have := h.det_pos
      exact pos_re_of_pos this
    have h3 : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
      simp [Matrix.det_fin_two]
    rw [h3] at h2
    exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    
    apply posDef_iff_dotProduct_mulVec.mpr
    refine ⟨hM, ?_⟩
    intro x hx
    have h_dot := expand_dotProduct_2x2 M x
    have hM00 : M 0 0 = ((M 0 0).re : ℂ) := hermitian_diag_isReal hM 0
    have hM11 : M 1 1 = ((M 1 1).re : ℂ) := hermitian_diag_isReal hM 1
    have hM10 : M 1 0 = star (M 0 1) := by
      have h_eq : Mᴴ = M := hM
      calc M 1 0 = Mᴴ 1 0 := by rw [h_eq]
        _ = star (M 0 1) := rfl
    have h_dot2 : star x ⬝ᵥ (M *ᵥ x) =
        ((M 0 0).re : ℂ) * x 0 * star (x 0) + M 0 1 * star (x 0) * x 1 +
        star (M 0 1) * x 0 * star (x 1) + ((M 1 1).re : ℂ) * x 1 * star (x 1) := by
      rw [h_dot, hM00, hM11, hM10]
      generalize hr00 : ((M 0 0).re : ℂ) = r00
      generalize hr11 : ((M 1 1).re : ℂ) = r11
      ring
    have h_re : (M 0 0).re * (star x ⬝ᵥ (M *ᵥ x)).re =
        normSq (((M 0 0).re : ℂ) * x 0 + M 0 1 * x 1) +
        ((M 0 0).re * (M 1 1).re - normSq (M 0 1)) * normSq (x 1) := by
      have h_dot3 : ((M 0 0).re : ℂ) * (star x ⬝ᵥ (M *ᵥ x)) =
          ((M 0 0).re : ℂ) * (((M 0 0).re : ℂ) * x 0 * star (x 0) + M 0 1 * star (x 0) * x 1 +
          star (M 0 1) * x 0 * star (x 1) + ((M 1 1).re : ℂ) * x 1 * star (x 1)) := by
        rw [h_dot2]
      have h_re_eq : (((M 0 0).re : ℂ) * (star x ⬝ᵥ (M *ᵥ x))).re =
          (((M 0 0).re : ℂ) * (((M 0 0).re : ℂ) * x 0 * star (x 0) + M 0 1 * star (x 0) * x 1 +
          star (M 0 1) * x 0 * star (x 1) + ((M 1 1).re : ℂ) * x 1 * star (x 1))).re := by
        rw [h_dot3]
      have h_re_LHS : (((M 0 0).re : ℂ) * (star x ⬝ᵥ (M *ᵥ x))).re = (M 0 0).re * (star x ⬝ᵥ (M *ᵥ x)).re := by
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      have h_re_RHS : (((M 0 0).re : ℂ) * (((M 0 0).re : ℂ) * x 0 * star (x 0) + M 0 1 * star (x 0) * x 1 + star (M 0 1) * x 0 * star (x 1) + ((M 1 1).re : ℂ) * x 1 * star (x 1))).re = (M 0 0).re * (((M 0 0).re : ℂ) * x 0 * star (x 0) + M 0 1 * star (x 0) * x 1 + star (M 0 1) * x 0 * star (x 1) + ((M 1 1).re : ℂ) * x 1 * star (x 1)).re := by
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      rw [h_re_LHS, h_re_RHS] at h_re_eq
      rw [h_re_eq]
      exact quadratic_form_re_poly ((M 0 0).re) ((M 1 1).re) (M 0 1) (x 0) (x 1)

    have h_im : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
      rw [h_dot2]
      simp only [add_im, mul_im, ofReal_re, ofReal_im, star_def, conj_re, conj_im, zero_mul, add_zero, sub_zero, mul_re]
      ring

    have h_det : (M 0 0 * M 1 1 - M 0 1 * M 1 0).re = (M 0 0).re * (M 1 1).re - normSq (M 0 1) := by
      rw [hM00, hM11, hM10]
      simp only [normSq_apply, sub_re, mul_re, ofReal_re, ofReal_im, star_def, conj_re, conj_im, sub_zero, zero_mul]
      ring
    rw [h_det] at h2

    have h_RHS_pos : 0 < normSq (((M 0 0).re : ℂ) * x 0 + M 0 1 * x 1) + ((M 0 0).re * (M 1 1).re - normSq (M 0 1)) * normSq (x 1) := by
      by_cases hx1 : x 1 = 0
      · have hx0 : x 0 ≠ 0 := by
          intro h0
          apply hx
          funext i
          match i with
          | 0 => exact h0
          | 1 => exact hx1
        rw [hx1]
        simp only [mul_zero, add_zero, normSq_zero, mul_zero]
        have hn : 0 < normSq (x 0) := normSq_pos.mpr hx0
        have ha : 0 < (M 0 0).re ^ 2 := sq_pos_of_pos h1
        have eq1 : normSq (((M 0 0).re : ℂ) * x 0) = (M 0 0).re ^ 2 * normSq (x 0) := by
          calc normSq (((M 0 0).re : ℂ) * x 0) = normSq ((M 0 0).re : ℂ) * normSq (x 0) := normSq_mul _ _
            _ = (M 0 0).re ^ 2 * normSq (x 0) := by
              have h_sq : normSq ((M 0 0).re : ℂ) = (M 0 0).re ^ 2 := by simp [normSq_ofReal, sq]
              rw [h_sq]
        rw [eq1]
        exact mul_pos ha hn
      · have hn : 0 < normSq (x 1) := normSq_pos.mpr hx1
        have hp2 : 0 < ((M 0 0).re * (M 1 1).re - normSq (M 0 1)) * normSq (x 1) := mul_pos h2 hn
        have hp1 : 0 ≤ normSq (((M 0 0).re : ℂ) * x 0 + M 0 1 * x 1) := normSq_nonneg _
        exact add_pos_of_nonneg_of_pos hp1 hp2

    have h_LHS_pos : 0 < (M 0 0).re * (star x ⬝ᵥ (M *ᵥ x)).re := by
      rw [h_re]
      exact h_RHS_pos

    have h_re_pos : 0 < (star x ⬝ᵥ (M *ᵥ x)).re := pos_of_mul_pos_right h_LHS_pos (le_of_lt h1)

    exact pos_of_re_pos_and_im_zero _ h_re_pos h_im


lemma convex_exp_mul (c : ℝ) : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => Real.exp (c * s)) := by
  have hc : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h1 : ConvexOn ℝ Set.univ (fun s => Real.exp (c * s)) := by
    constructor
    · exact convex_univ
    · intro x _ y _ a b ha hb hab
      have h_exp := hc.2 (Set.mem_univ (c * x)) (Set.mem_univ (c * y)) ha hb hab
      change Real.exp (c * (a * x + b * y)) ≤ a * Real.exp (c * x) + b * Real.exp (c * y)
      have h_eq : c * (a * x + b * y) = a * (c * x) + b * (c * y) := by ring
      rw [h_eq]
      exact h_exp
  exact h1.subset (Set.subset_univ _) (convex_Icc (0 : ℝ) 1)

lemma convexOn_exp_comb (A B : ℂ) (k : ℝ) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun (s : ℝ) => Complex.normSq (A * (Real.exp (2 * s * k) : ℂ) + B * (Real.exp (-2 * s * k) : ℂ))) := by
  have h_eq : (fun (s : ℝ) => Complex.normSq (A * (Real.exp (2 * s * k) : ℂ) + B * (Real.exp (-2 * s * k) : ℂ))) =
      fun s => Complex.normSq A * Real.exp (4 * k * s) + Complex.normSq B * Real.exp (-4 * k * s) + 2 * (A * star B).re := by
    ext s
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, star_def, Complex.conj_re, Complex.conj_im, sub_zero, mul_zero, zero_add]
    have e1 : Real.exp (2 * s * k) * Real.exp (2 * s * k) = Real.exp (4 * k * s) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-2 * s * k) * Real.exp (-2 * s * k) = Real.exp (-4 * k * s) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have e3 : Real.exp (2 * s * k) * Real.exp (-2 * s * k) = 1 := by
      rw [←Real.exp_add]
      have : 2 * s * k + -2 * s * k = 0 := by ring
      rw [this, Real.exp_zero]
    calc (A.re * Real.exp (2 * s * k) + B.re * Real.exp (-2 * s * k)) * (A.re * Real.exp (2 * s * k) + B.re * Real.exp (-2 * s * k)) +
         (A.im * Real.exp (2 * s * k) + B.im * Real.exp (-2 * s * k)) * (A.im * Real.exp (2 * s * k) + B.im * Real.exp (-2 * s * k))
       = (A.re * A.re + A.im * A.im) * (Real.exp (2 * s * k) * Real.exp (2 * s * k)) +
         (B.re * B.re + B.im * B.im) * (Real.exp (-2 * s * k) * Real.exp (-2 * s * k)) +
         2 * (A.re * B.re + A.im * B.im) * (Real.exp (2 * s * k) * Real.exp (-2 * s * k)) := by ring
     _ = (A.re * A.re + A.im * A.im) * Real.exp (4 * k * s) +
         (B.re * B.re + B.im * B.im) * Real.exp (-4 * k * s) +
         2 * (A.re * B.re + A.im * B.im) * 1 := by rw [e1, e2, e3]
     _ = (A.re * A.re + A.im * A.im) * Real.exp (4 * k * s) +
         (B.re * B.re + B.im * B.im) * Real.exp (-4 * k * s) +
         2 * (A.re * B.re - A.im * -B.im) := by ring
  rw [h_eq]

  have hc1 : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => Complex.normSq A * Real.exp (4 * k * s)) :=
    ConvexOn.smul (Complex.normSq_nonneg A) (convex_exp_mul (4 * k))
  have hc2 : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => Complex.normSq B * Real.exp (-4 * k * s)) :=
    ConvexOn.smul (Complex.normSq_nonneg B) (convex_exp_mul (-4 * k))
  have hc3 : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => 2 * (A * star B).re) :=
    convexOn_const _ (convex_Icc (0 : ℝ) 1)

  have hc12 := ConvexOn.add hc1 hc2
  exact ConvexOn.add hc12 hc3


lemma concaveOn_min_endpoints {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, min (f 0) (f 1) ≤ f s := by
  intro s hs
  have h_s_eq : s = (1 - s) * 0 + s * 1 := by ring
  have h_0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h_1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h_sum : 1 - s + s = 1 := by ring
  have h_pos1 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have h_pos2 : 0 ≤ s := hs.1
  have h_conc := hf.2 h_0 h_1 h_pos1 h_pos2 h_sum
  have h_min0 : min (f 0) (f 1) ≤ f 0 := min_le_left _ _
  have h_min1 : min (f 0) (f 1) ≤ f 1 := min_le_right _ _
  calc min (f 0) (f 1) = (1 - s) * min (f 0) (f 1) + s * min (f 0) (f 1) := by ring
    _ ≤ (1 - s) * f 0 + s * f 1 := by gcongr
    _ ≤ f ((1 - s) * 0 + s * 1) := h_conc
    _ = f s := by rw [←h_s_eq]

lemma V_s_diag_posdef (t : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU_herm : U.IsHermitian) (hV_herm : V.IsHermitian)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hV0 : (V_s_diag t U V 0).PosDef)
    (hV1 : (V_s_diag t U V 1).PosDef) :
    (V_s_diag t U V s).PosDef := by
  have hM_herm : (V_s_diag t U V s).IsHermitian := V_s_diag_herm t U V hU_herm hV_herm s
  rw [posdef_2x2_iff _ hM_herm]

  have hM0_herm : (V_s_diag t U V 0).IsHermitian := V_s_diag_herm t U V hU_herm hV_herm 0
  have hM1_herm : (V_s_diag t U V 1).IsHermitian := V_s_diag_herm t U V hU_herm hV_herm 1

  have h0_cond := (posdef_2x2_iff _ hM0_herm).mp hV0
  have h1_cond := (posdef_2x2_iff _ hM1_herm).mp hV1

  have h00 : (V_s_diag t U V s 0 0).re = (V 0 0).re := by rw [V_s_diag_00]
  have h11 : (V_s_diag t U V s 1 1).re = (V 1 1).re := by rw [V_s_diag_11]

  have h_pos1 : 0 < (V_s_diag t U V s 0 0).re := by
    rw [h00]
    have h00_0 : (V_s_diag t U V 0 0 0).re = (V 0 0).re := by rw [V_s_diag_00]
    rw [←h00_0]
    exact h0_cond.1

  have h_det_eq : ∀ (x : ℝ), (V_s_diag t U V x 0 0 * V_s_diag t U V x 1 1 - V_s_diag t U V x 0 1 * V_s_diag t U V x 1 0).re =
    (V_s_diag t U V x 0 0).re * (V_s_diag t U V x 1 1).re - Complex.normSq (V_s_diag t U V x 0 1) := by
    intro x
    have h_herm := V_s_diag_herm t U V hU_herm hV_herm x
    have hM00 : V_s_diag t U V x 0 0 = (V_s_diag t U V x 0 0).re := by
      have h00 : star (V_s_diag t U V x 0 0) = V_s_diag t U V x 0 0 := congrFun (congrFun h_herm 0) 0
      apply Complex.ext
      · rfl
      · have him : -(V_s_diag t U V x 0 0).im = (V_s_diag t U V x 0 0).im := congrArg Complex.im h00
        have him0 : (V_s_diag t U V x 0 0).im = 0 := by linarith
        simp [him0]
    have hM11 : V_s_diag t U V x 1 1 = (V_s_diag t U V x 1 1).re := by
      have h11 : star (V_s_diag t U V x 1 1) = V_s_diag t U V x 1 1 := congrFun (congrFun h_herm 1) 1
      apply Complex.ext
      · rfl
      · have him : -(V_s_diag t U V x 1 1).im = (V_s_diag t U V x 1 1).im := congrArg Complex.im h11
        have him0 : (V_s_diag t U V x 1 1).im = 0 := by linarith
        simp [him0]
    have hM10 : V_s_diag t U V x 1 0 = star (V_s_diag t U V x 0 1) := by
      have h10 : star (V_s_diag t U V x 0 1) = V_s_diag t U V x 1 0 := congrFun (congrFun h_herm 1) 0
      exact h10.symm
    rw [hM00, hM11, hM10]
    simp only [normSq_apply, sub_re, mul_re, ofReal_re, ofReal_im, star_def, conj_re, conj_im, sub_zero, zero_mul]
    ring

  have h_pos2 : 0 < (V_s_diag t U V s 0 0 * V_s_diag t U V s 1 1 - V_s_diag t U V s 0 1 * V_s_diag t U V s 1 0).re := by
    rw [h_det_eq s]
    rw [h00, h11]
    let f := fun (x : ℝ) => (V 0 0).re * (V 1 1).re - Complex.normSq (V_s_diag t U V x 0 1)
    have h_f_eq : f = fun x => (V 0 0).re * (V 1 1).re - Complex.normSq ((-I / 2 * U 0 1 + 1 / 2 * V 0 1) * (Real.exp (2 * x * t) : ℂ) + (I / 2 * U 0 1 + 1 / 2 * V 0 1) * (Real.exp (-2 * x * t) : ℂ)) := by
      ext x
      dsimp [f]
      congr 1
      have h_v := V_s_diag_01 t U V x
      rw [h_v]
      congr 1
      ring
    have Hc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f := by
      rw [h_f_eq]
      have hc_const : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun (x : ℝ) => (V 0 0).re * (V 1 1).re) := concaveOn_const _ (convex_Icc (0 : ℝ) 1)
      have hc_sub := convexOn_exp_comb (-I / 2 * U 0 1 + 1 / 2 * V 0 1) (I / 2 * U 0 1 + 1 / 2 * V 0 1) t
      exact ConcaveOn.sub hc_const hc_sub

    have h_min := concaveOn_min_endpoints Hc s ⟨hs0, hs1⟩
    have hf0 : 0 < f 0 := by
      have h00_0 : (V_s_diag t U V 0 0 0).re = (V 0 0).re := by rw [V_s_diag_00]
      have h11_0 : (V_s_diag t U V 0 1 1).re = (V 1 1).re := by rw [V_s_diag_11]
      have h0_cond_2 := h0_cond.2
      rw [h_det_eq 0] at h0_cond_2
      rw [h00_0, h11_0] at h0_cond_2
      exact h0_cond_2
    have hf1 : 0 < f 1 := by
      have h00_1 : (V_s_diag t U V 1 0 0).re = (V 0 0).re := by rw [V_s_diag_00]
      have h11_1 : (V_s_diag t U V 1 1 1).re = (V 1 1).re := by rw [V_s_diag_11]
      have h1_cond_2 := h1_cond.2
      rw [h_det_eq 1] at h1_cond_2
      rw [h00_1, h11_1] at h1_cond_2
      exact h1_cond_2

    have h_min_pos : 0 < min (f 0) (f 1) := lt_min hf0 hf1
    exact lt_of_lt_of_le h_min_pos h_min
  exact ⟨h_pos1, h_pos2⟩

lemma vec_to_spinor_eq_matrix (x : Fin 4 → ℝ) :
    vec_to_spinor (fun i => (x i : ℂ)) = !![((x 0 + x 3 : ℝ) : ℂ), (x 1 : ℂ) - (x 2 : ℂ) * I; star ((x 1 : ℂ) - (x 2 : ℂ) * I), ((x 0 - x 3 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [vec_to_spinor]
  · simp [vec_to_spinor]; ring
  · simp [vec_to_spinor]
  · simp [vec_to_spinor]; ring

lemma posDef_vec_to_spinor_iff (x : Fin 4 → ℝ) :
    (vec_to_spinor (fun i => (x i : ℂ))).PosDef ↔ x ∈ forward_light_cone := by
  constructor
  · intro h
    have h_herm : (vec_to_spinor (fun i => (x i : ℂ))).IsHermitian := by
      rw [vec_to_spinor_eq_matrix]
      exact isHerm_two_by_two (x 0 + x 3) (x 0 - x 3) ((x 1 : ℂ) - (x 2 : ℂ) * I)
    have h_iff := posdef_2x2_iff (vec_to_spinor (fun i => (x i : ℂ))) h_herm
    have h_pos := h_iff.mp h
    have h_pos1 := h_pos.1
    have h_pos2 := h_pos.2
    have h_eq : vec_to_spinor (fun i => (x i : ℂ)) = !![((x 0 + x 3 : ℝ) : ℂ), (x 1 : ℂ) - (x 2 : ℂ) * I; star ((x 1 : ℂ) - (x 2 : ℂ) * I), ((x 0 - x 3 : ℝ) : ℂ)] := vec_to_spinor_eq_matrix x
    have h00 : (vec_to_spinor (fun i => (x i : ℂ))) 0 0 = ((x 0 + x 3 : ℝ) : ℂ) := by rw [h_eq]; rfl
    have h11 : (vec_to_spinor (fun i => (x i : ℂ))) 1 1 = ((x 0 - x 3 : ℝ) : ℂ) := by rw [h_eq]; rfl
    have h01 : (vec_to_spinor (fun i => (x i : ℂ))) 0 1 = (x 1 : ℂ) - (x 2 : ℂ) * I := by rw [h_eq]; rfl
    have h10 : (vec_to_spinor (fun i => (x i : ℂ))) 1 0 = star ((x 1 : ℂ) - (x 2 : ℂ) * I) := by rw [h_eq]; rfl

    rw [h00] at h_pos1
    have h_re1 : (((x 0 + x 3 : ℝ) : ℂ)).re = x 0 + x 3 := by simp
    rw [h_re1] at h_pos1

    rw [h00, h11, h01, h10] at h_pos2
    have h_det_re : ((((x 0 + x 3 : ℝ) : ℂ)) * (((x 0 - x 3 : ℝ) : ℂ)) - ((x 1 : ℂ) - (x 2 : ℂ) * I) * star ((x 1 : ℂ) - (x 2 : ℂ) * I)).re = x 0 ^ 2 - x 3 ^ 2 - (x 1 ^ 2 + x 2 ^ 2) := by
      simp [sub_re, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im]
      ring
    rw [h_det_re] at h_pos2

    have h_pos_sq : 0 < x 0 ^ 2 - (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by linarith
    have h_x0_pos : 0 < x 0 := by
      have h_sq_ineq : x 3 ^ 2 < x 0 ^ 2 := by
        have h_sum_sq : 0 ≤ x 1 ^ 2 + x 2 ^ 2 := by positivity
        linarith
      have h_abs_ineq : |x 3| < |x 0| := by
        rw [← sq_lt_sq]
        exact h_sq_ineq
      by_contra hc
      have hc2 : x 0 ≤ 0 := not_lt.mp hc
      have hc3 : |x 0| = -x 0 := abs_of_nonpos hc2
      rw [hc3] at h_abs_ineq
      have h_abs3 : -x 3 ≤ |x 3| := neg_le_abs (x 3)
      have h_abs3_pos : x 3 ≤ |x 3| := le_abs_self (x 3)
      have h_bound : x 3 < -x 0 := lt_of_le_of_lt h_abs3_pos h_abs_ineq
      have hc4 : x 0 + x 3 < 0 := by linarith
      linarith

    have h_inner : minkowskiInner x x > 0 := by
      rw [minkowskiInner_explicit]
      have eq1 : x 1 * x 1 = x 1 ^ 2 := by ring
      have eq2 : x 2 * x 2 = x 2 ^ 2 := by ring
      have eq3 : x 3 * x 3 = x 3 ^ 2 := by ring
      have eq0 : x 0 * x 0 = x 0 ^ 2 := by ring
      rw [eq1, eq2, eq3, eq0]
      linarith

    exact ⟨h_x0_pos, h_inner⟩
  · exact posDef_vec_to_spinor x


noncomputable def tube_F_diag (c : ℝ) (hc : 0 < c) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  V_s_diag (Real.log c) X Y s


lemma tube_F_diag_posdef (c : ℝ) (hc : 0 < c) (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.IsHermitian) (hY : Y.PosDef)
    (hF1 : (tube_F_diag c hc X Y 1).PosDef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (tube_F_diag c hc X Y s).PosDef := by
  dsimp [tube_F_diag] at *
  have hF0 : (V_s_diag (Real.log c) X Y 0).PosDef := by
    rw [V_s_diag_zero]
    exact hY
  exact V_s_diag_posdef (Real.log c) X Y hX hY.1 s hs0 hs1 hF0 hF1


lemma dot_mulVec_assoc (M P : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    star x ⬝ᵥ ((P * M * Pᴴ) *ᵥ x) = star (Pᴴ *ᵥ x) ⬝ᵥ (M *ᵥ (Pᴴ *ᵥ x)) := by
  have hm1 : ((P * M * Pᴴ) *ᵥ x) = (P * (M * Pᴴ)) *ᵥ x := by rw [Matrix.mul_assoc]
  rw [hm1]
  rw [← Matrix.mulVec_mulVec x P (M * Pᴴ)]
  rw [← Matrix.mulVec_mulVec x M Pᴴ]
  have h1 : star x ⬝ᵥ P *ᵥ (M *ᵥ (Pᴴ *ᵥ x)) = (star x ᵥ* P) ⬝ᵥ (M *ᵥ (Pᴴ *ᵥ x)) := Matrix.dotProduct_mulVec (star x) P (M *ᵥ (Pᴴ *ᵥ x))
  rw [h1]
  have h_star : star x ᵥ* P = star (Pᴴ *ᵥ x) := by
    have h := (Matrix.star_mulVec Pᴴ x).symm
    rw [conjTranspose_conjTranspose] at h
    exact h
  rw [h_star]

lemma conjTranspose_mul_triple (M P : Matrix (Fin 2) (Fin 2) ℂ) :
    (P * M * Pᴴ)ᴴ = P * Mᴴ * Pᴴ := by
  have h1 : (P * M * Pᴴ)ᴴ = Pᴴᴴ * (P * M)ᴴ := conjTranspose_mul (P * M) Pᴴ
  have h2 : (P * M)ᴴ = Mᴴ * Pᴴ := conjTranspose_mul P M
  have h3 : Pᴴᴴ = P := conjTranspose_conjTranspose P
  rw [h1, h2, h3, Matrix.mul_assoc]

lemma posdef_congruence (M P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.det ≠ 0)
    (hM : M.PosDef) : (P * M * Pᴴ).PosDef := by
  have h_herm : (P * M * Pᴴ).IsHermitian := by
    dsimp [Matrix.IsHermitian]
    rw [conjTranspose_mul_triple]
    have h1 : Mᴴ = M := hM.1
    rw [h1]
  apply posDef_iff_dotProduct_mulVec.mpr
  constructor
  · exact h_herm
  · intro x hx
    rw [dot_mulVec_assoc M P x]
    have hM_dot := posDef_iff_dotProduct_mulVec.mp hM
    apply hM_dot.2
    intro h_zero
    have h_det : IsUnit Pᴴ.det := by
      rw [det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hP)
    have h_inv : (Pᴴ)⁻¹ *ᵥ (Pᴴ *ᵥ x) = (Pᴴ)⁻¹ *ᵥ 0 := by rw [h_zero]
    rw [Matrix.mulVec_zero] at h_inv
    have h_inv2 : (Pᴴ)⁻¹ *ᵥ (Pᴴ *ᵥ x) = ((Pᴴ)⁻¹ * Pᴴ) *ᵥ x := by rw [← Matrix.mulVec_mulVec x (Pᴴ)⁻¹ Pᴴ]
    rw [h_inv2] at h_inv
    have h_inv3 : (Pᴴ)⁻¹ * Pᴴ = 1 := nonsing_inv_mul _ h_det
    rw [h_inv3, one_mulVec] at h_inv
    exact hx h_inv

noncomputable def tube_F_diag_c (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let u := (Complex.log c).re
  let v := (Complex.log c).im
  !![ (Real.cos (2 * s * v) : ℂ) * Y 0 0 + (Real.sin (2 * s * v) : ℂ) * X 0 0,
      (Real.cosh (2 * s * u) : ℂ) * Y 0 1 - I * (Real.sinh (2 * s * u) : ℂ) * X 0 1;
      (Real.cosh (2 * s * u) : ℂ) * Y 1 0 + I * (Real.sinh (2 * s * u) : ℂ) * X 1 0,
      (Real.cos (2 * s * v) : ℂ) * Y 1 1 - (Real.sin (2 * s * v) : ℂ) * X 1 1 ]

noncomputable def tube_F_jordan_c (b : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ Y 0 0 - 2 * s * (star b * X 0 1).im - s^2 * ‖b‖^2 * Y 1 1, Y 0 1 - I * (s * b) * X 1 1;
      Y 1 0 + I * (s * star b) * X 1 1, Y 1 1 ]

lemma isHermitian_of_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h00 : (starRingEnd ℂ) (A 0 0) = A 0 0)
    (h11 : (starRingEnd ℂ) (A 1 1) = A 1 1)
    (h01 : (starRingEnd ℂ) (A 0 1) = A 1 0) :
    A.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j
  · change star (A 0 0) = A 0 0
    exact h00
  · change star (A 1 0) = A 0 1
    have h : star (star (A 0 1)) = star (A 1 0) := congrArg star h01
    simp only [star_star] at h
    exact h.symm
  · change star (A 0 1) = A 1 0
    exact h01
  · change star (A 1 1) = A 1 1
    exact h11

lemma herm_diag_im_zero (Y : Matrix (Fin 2) (Fin 2) ℂ) (hy : Yᴴ = Y) (i : Fin 2) :
    (Y i i).im = 0 := by
  have h : star (Y i i) = Y i i := congr_fun (congr_fun hy i) i
  have h2 := (Complex.ext_iff.mp h).2
  simp only [Complex.star_def, Complex.conj_im] at h2
  linarith

lemma sin_concave_aux (θ s : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * Real.sin θ ≤ Real.sin (s * θ) := by
  have h := (strictConcaveOn_sin_Icc.concaveOn).2 (x := θ) (y := 0) ⟨hθ0, hθ⟩
    ⟨le_refl _, Real.pi_pos.le⟩ hs0 (sub_nonneg.mpr hs1) (by ring)
  simpa [smul_eq_mul] using h

lemma sinusoid_interp (A B θ s : ℝ) :
    Real.sin θ * (A * Real.cos (s * θ) + B * Real.sin (s * θ)) =
      Real.sin ((1 - s) * θ) * A + Real.sin (s * θ) * (A * Real.cos θ + B * Real.sin θ) := by
  have h : (1 - s) * θ = θ - s * θ := by ring
  rw [h, Real.sin_sub]
  ring

lemma sinusoid_concave_pos (A B θ s : ℝ) (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi) (hA : 0 < A)
    (h1 : 0 < A * Real.cos θ + B * Real.sin θ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * A + s * (A * Real.cos θ + B * Real.sin θ) ≤
      A * Real.cos (s * θ) + B * Real.sin (s * θ) := by
  have hne : θ ≠ Real.pi := by
    rintro rfl
    simp at h1
    linarith
  have hlt : θ < Real.pi := lt_of_le_of_ne hθ hne
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hlt
  have e1 := sin_concave_aux θ (1 - s) hθ0.le hθ (by linarith) (by linarith)
  have e2 := sin_concave_aux θ s hθ0.le hθ hs0 hs1
  have hid := sinusoid_interp A B θ s
  have key : Real.sin θ * ((1 - s) * A + s * (A * Real.cos θ + B * Real.sin θ)) ≤
      Real.sin θ * (A * Real.cos (s * θ) + B * Real.sin (s * θ)) := by
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_right e1 hA.le, mul_le_mul_of_nonneg_right e2 h1.le]
  exact le_of_mul_le_mul_left key hsin

lemma sinusoid_concave (A B θ s : ℝ) (hθ : |θ| ≤ Real.pi) (hA : 0 < A)
    (h1 : 0 < A * Real.cos θ + B * Real.sin θ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * A + s * (A * Real.cos θ + B * Real.sin θ) ≤
      A * Real.cos (s * θ) + B * Real.sin (s * θ) := by
  rcases lt_trichotomy θ 0 with h | h | h
  · have := sinusoid_concave_pos A (-B) (-θ) s (by linarith) (by rw [abs_le] at hθ; linarith) hA
      (by simpa using h1) hs0 hs1
    have e1 : Real.cos (s * -θ) = Real.cos (s * θ) := by rw [mul_neg, Real.cos_neg]
    have e2 : Real.sin (s * -θ) = - Real.sin (s * θ) := by rw [mul_neg, Real.sin_neg]
    simp only [Real.cos_neg, Real.sin_neg, e1, e2] at this
    linarith
  · subst h
    have : (1 - s) * A + s * A = A := by ring
    simp
    linarith
  · exact sinusoid_concave_pos A B θ s h (by rw [abs_le] at hθ; linarith) hA h1 hs0 hs1

lemma sinh_convex_aux (τ s : ℝ) (hτ : 0 ≤ τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sinh (s * τ) ≤ s * Real.sinh τ := by
  have hc : ConvexOn ℝ (Set.Ici (0:ℝ)) Real.sinh := by
    apply convexOn_of_deriv2_nonneg (convex_Ici 0)
    · exact Real.continuous_sinh.continuousOn
    · exact Real.differentiable_sinh.differentiableOn
    · have : deriv Real.sinh = Real.cosh := Real.deriv_sinh
      rw [this]
      exact Real.differentiable_cosh.differentiableOn
    · intro x hx
      have h1 : deriv Real.sinh = Real.cosh := Real.deriv_sinh
      have h2 : deriv Real.cosh = Real.sinh := Real.deriv_cosh
      show 0 ≤ deriv (deriv Real.sinh) x
      rw [h1, h2]
      have hx' : 0 < x := by simpa using hx
      exact (Real.sinh_pos_iff.mpr hx').le
  have h := hc.2 (x := τ) (y := 0) (by simpa using hτ) (by simp) hs0 (sub_nonneg.mpr hs1) (by ring)
  have h' : Real.sinh (s * τ) ≤ s * Real.sinh τ := by
    simpa [smul_eq_mul] using h
  exact h'


lemma cosh_sinh_interp (τ s : ℝ) (y x : ℂ) :
    (Real.sinh τ : ℂ) * ((Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x) =
      (Real.sinh ((1 - s) * τ) : ℂ) * y +
      (Real.sinh (s * τ) : ℂ) * ((Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x) := by
  have h : (1 - s) * τ = τ - s * τ := by ring
  have e : Real.sinh ((1 - s) * τ) = Real.sinh τ * Real.cosh (s * τ) - Real.cosh τ * Real.sinh (s * τ) := by
    rw [h, Real.sinh_sub]
  have e' : (Real.sinh ((1 - s) * τ) : ℂ) = (Real.sinh τ : ℂ) * (Real.cosh (s * τ) : ℂ) - (Real.cosh τ : ℂ) * (Real.sinh (s * τ) : ℂ) := by
    exact_mod_cast e
  rw [e']
  ring

lemma cosh_sinh_norm_le_pos (τ s : ℝ) (hτ : 0 ≤ τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (y x : ℂ) :
    ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ ≤
      (1 - s) * ‖y‖ + s * ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖ := by
  rcases eq_or_lt_of_le hτ with h | h
  · subst h
    simp
    nlinarith [norm_nonneg y]
  · have hsh : 0 < Real.sinh τ := Real.sinh_pos_iff.mpr h
    have hid := cosh_sinh_interp τ s y x
    have e1 : Real.sinh ((1 - s) * τ) ≤ (1 - s) * Real.sinh τ :=
      sinh_convex_aux τ (1 - s) hτ (by linarith) (by linarith)
    have e1' : 0 ≤ Real.sinh ((1 - s) * τ) := Real.sinh_nonneg_iff.mpr (by nlinarith)
    have e2 : Real.sinh (s * τ) ≤ s * Real.sinh τ := sinh_convex_aux τ s hτ hs0 hs1
    have e2' : 0 ≤ Real.sinh (s * τ) := Real.sinh_nonneg_iff.mpr (by nlinarith)
    have hn : Real.sinh τ * ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ ≤
        Real.sinh ((1 - s) * τ) * ‖y‖ + Real.sinh (s * τ) * ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖ := by
      have := congrArg norm hid
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsh] at this
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg e1', abs_of_nonneg e2']
    have hn2 : Real.sinh τ * ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ ≤
        Real.sinh τ * ((1 - s) * ‖y‖ + s * ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖) := by
      refine hn.trans ?_
      nlinarith [mul_le_mul_of_nonneg_right e1 (norm_nonneg y),
        mul_le_mul_of_nonneg_right e2 (norm_nonneg ((Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x))]
    exact le_of_mul_le_mul_left hn2 hsh

lemma cosh_sinh_norm_le (τ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (y x : ℂ) :
    ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ ≤
      (1 - s) * ‖y‖ + s * ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖ := by
  rcases le_total 0 τ with h | h
  · exact cosh_sinh_norm_le_pos τ s h hs0 hs1 y x
  · have := cosh_sinh_norm_le_pos (-τ) s (by linarith) hs0 hs1 y (-x)
    have e1 : s * -τ = -(s * τ) := by ring
    simp only [e1, Real.cosh_neg, Real.sinh_neg, Complex.ofReal_neg] at this
    simpa using this

lemma det_interp (a0 d0 a1 d1 a d β0 β1 β s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha0 : 0 < a0) (hd0 : 0 < d0) (ha1 : 0 < a1) (hd1 : 0 < d1)
    (ha : (1 - s) * a0 + s * a1 ≤ a) (hd : (1 - s) * d0 + s * d1 ≤ d)
    (hβ : β ≤ (1 - s) * β0 + s * β1) (hβ0 : 0 ≤ β0) (hβ1 : 0 ≤ β1) (hβn : 0 ≤ β)
    (hdet0 : β0 ^ 2 < a0 * d0) (hdet1 : β1 ^ 2 < a1 * d1) :
    β ^ 2 < a * d := by
  have hp : 0 ≤ 1 - s := by linarith
  have hA : 0 < (1 - s) * a0 + s * a1 := by
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using ha0
    · nlinarith [mul_nonneg hp ha0.le, mul_pos h ha1]
  have hD : 0 < (1 - s) * d0 + s * d1 := by
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using hd0
    · nlinarith [mul_nonneg hp hd0.le, mul_pos h hd1]
  have h1 : ((1 - s) * a0 + s * a1) * ((1 - s) * d0 + s * d1) ≤ a * d :=
    mul_le_mul ha hd hD.le (hA.le.trans ha)
  set m0 := Real.sqrt (a0 * d0) with hm0
  set m1 := Real.sqrt (a1 * d1) with hm1
  have hm0sq : m0 ^ 2 = a0 * d0 := Real.sq_sqrt (by positivity)
  have hm1sq : m1 ^ 2 = a1 * d1 := Real.sq_sqrt (by positivity)
  have hm0p : 0 ≤ m0 := Real.sqrt_nonneg _
  have hm1p : 0 ≤ m1 := Real.sqrt_nonneg _
  have hb0 : β0 < m0 := by nlinarith
  have hb1 : β1 < m1 := by nlinarith
  have hamgm : 2 * m0 * m1 ≤ a0 * d1 + a1 * d0 := by
    have hsq : (2 * m0 * m1) ^ 2 ≤ (a0 * d1 + a1 * d0) ^ 2 := by
      have : (2 * m0 * m1) ^ 2 = 4 * (a0 * d0) * (a1 * d1) := by
        have : (2 * m0 * m1) ^ 2 = 4 * m0 ^ 2 * m1 ^ 2 := by ring
        rw [this, hm0sq, hm1sq]
      rw [this]
      nlinarith [sq_nonneg (a0 * d1 - a1 * d0)]
    by_contra hcon
    push_neg at hcon
    have hpos : 0 ≤ a0 * d1 + a1 * d0 := by positivity
    have := pow_lt_pow_left₀ hcon hpos (two_ne_zero)
    linarith
  have h2 : ((1 - s) * m0 + s * m1) ^ 2 ≤ ((1 - s) * a0 + s * a1) * ((1 - s) * d0 + s * d1) := by
    have key : ((1 - s) * a0 + s * a1) * ((1 - s) * d0 + s * d1) - ((1 - s) * m0 + s * m1) ^ 2 =
        s * (1 - s) * (a0 * d1 + a1 * d0 - 2 * m0 * m1) := by
      linear_combination (-(1 - s) ^ 2) * hm0sq + (-(s ^ 2)) * hm1sq
    have : 0 ≤ s * (1 - s) * (a0 * d1 + a1 * d0 - 2 * m0 * m1) :=
      mul_nonneg (mul_nonneg hs0 hp) (by linarith)
    linarith
  have h3 : (1 - s) * β0 + s * β1 < (1 - s) * m0 + s * m1 := by
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using hb0
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hb0.le), mul_pos h (sub_pos.mpr hb1)]
  have h4 : β ^ 2 < ((1 - s) * m0 + s * m1) ^ 2 := by
    have : β < (1 - s) * m0 + s * m1 := lt_of_le_of_lt hβ h3
    nlinarith
  linarith


lemma diag_posdef_core (θ τ s : ℝ) (hθ : |θ| ≤ Real.pi) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (Y0 Y1 X0 X1 : ℝ) (y x : ℂ)
    (hY0 : 0 < Y0) (hYd : ‖y‖ ^ 2 < Y0 * Y1)
    (hA1 : 0 < Y0 * Real.cos θ + X0 * Real.sin θ)
    (hdet1 : ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖ ^ 2 <
      (Y0 * Real.cos θ + X0 * Real.sin θ) * (Y1 * Real.cos θ + (-X1) * Real.sin θ)) :
    0 < Y0 * Real.cos (s * θ) + X0 * Real.sin (s * θ) ∧
    ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ ^ 2 <
      (Y0 * Real.cos (s * θ) + X0 * Real.sin (s * θ)) *
        (Y1 * Real.cos (s * θ) + (-X1) * Real.sin (s * θ)) := by
  have hY1 : 0 < Y1 := by
    have : 0 ≤ ‖y‖ ^ 2 := by positivity
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hD1 : 0 < Y1 * Real.cos θ + (-X1) * Real.sin θ := by
    have : 0 ≤ ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖ ^ 2 := by positivity
    by_contra hneg
    push_neg at hneg
    nlinarith
  have ha := sinusoid_concave Y0 X0 θ s hθ hY0 hA1 hs0 hs1
  have hd := sinusoid_concave Y1 (-X1) θ s hθ hY1 hD1 hs0 hs1
  have hb := cosh_sinh_norm_le τ s hs0 hs1 y x
  have hp : 0 ≤ 1 - s := by linarith
  have hapos : 0 < (1 - s) * Y0 + s * (Y0 * Real.cos θ + X0 * Real.sin θ) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using hY0
    · nlinarith [mul_nonneg hp hY0.le, mul_pos h hA1]
  refine ⟨lt_of_lt_of_le hapos ha, ?_⟩
  have key := det_interp Y0 Y1 (Y0 * Real.cos θ + X0 * Real.sin θ) (Y1 * Real.cos θ + (-X1) * Real.sin θ)
    (Y0 * Real.cos (s * θ) + X0 * Real.sin (s * θ)) (Y1 * Real.cos (s * θ) + (-X1) * Real.sin (s * θ))
    ‖y‖ ‖(Real.cosh τ : ℂ) * y - I * (Real.sinh τ : ℂ) * x‖
    ‖(Real.cosh (s * τ) : ℂ) * y - I * (Real.sinh (s * τ) : ℂ) * x‖ s hs0 hs1
    hY0 hY1 hA1 hD1 ha hd hb (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hYd hdet1
  exact key


lemma herm_det_re_Y (Y : Matrix (Fin 2) (Fin 2) ℂ) (hy : Yᴴ = Y)
    (h_det : 0 < (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0).re) :
    0 < (Y 0 0).re * (Y 1 1).re - Complex.normSq (Y 0 1) := by
  have h_Y10 : Y 1 0 = star (Y 0 1) := Eq.symm (congr_fun (congr_fun hy 1) 0)
  have h0 := herm_diag_im_zero Y hy 0
  have h1 := herm_diag_im_zero Y hy 1
  rw [h_Y10, Complex.sub_re, Complex.mul_re, h0, h1] at h_det
  have hb : (Y 0 1 * star (Y 0 1)).re = Complex.normSq (Y 0 1) := by
    rw [show Y 0 1 * star (Y 0 1) = (Complex.normSq (Y 0 1) : ℂ) from Complex.mul_conj _]
    exact Complex.ofReal_re _
  rw [hb] at h_det
  linarith

lemma tube_F_diag_c_re00 (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) (hY : Yᴴ = Y) (s : ℝ) :
    tube_F_diag_c c X Y s 0 0 = (((Y 0 0).re * Real.cos (s * (2 * (Complex.log c).im)) +
      (X 0 0).re * Real.sin (s * (2 * (Complex.log c).im)) : ℝ) : ℂ) := by
  have hx := herm_diag_im_zero X hX 0
  have hy := herm_diag_im_zero Y hY 0
  have e : 2 * s * (Complex.log c).im = s * (2 * (Complex.log c).im) := by ring
  change (Real.cos (2 * s * (Complex.log c).im) : ℂ) * Y 0 0 +
    (Real.sin (2 * s * (Complex.log c).im) : ℂ) * X 0 0 = _
  rw [e]
  generalize Real.cos (s * (2 * (Complex.log c).im)) = A
  generalize Real.sin (s * (2 * (Complex.log c).im)) = B
  apply Complex.ext <;> simp [hx, hy] <;> try ring

lemma tube_F_diag_c_re11 (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) (hY : Yᴴ = Y) (s : ℝ) :
    tube_F_diag_c c X Y s 1 1 = (((Y 1 1).re * Real.cos (s * (2 * (Complex.log c).im)) +
      (-(X 1 1).re) * Real.sin (s * (2 * (Complex.log c).im)) : ℝ) : ℂ) := by
  have hx := herm_diag_im_zero X hX 1
  have hy := herm_diag_im_zero Y hY 1
  have e : 2 * s * (Complex.log c).im = s * (2 * (Complex.log c).im) := by ring
  change (Real.cos (2 * s * (Complex.log c).im) : ℂ) * Y 1 1 -
    (Real.sin (2 * s * (Complex.log c).im) : ℂ) * X 1 1 = _
  rw [e]
  generalize Real.cos (s * (2 * (Complex.log c).im)) = A
  generalize Real.sin (s * (2 * (Complex.log c).im)) = B
  apply Complex.ext <;> simp [hx, hy] <;> try ring

lemma tube_F_diag_c_01 (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    tube_F_diag_c c X Y s 0 1 = (Real.cosh (s * (2 * (Complex.log c).re)) : ℂ) * Y 0 1 -
      I * (Real.sinh (s * (2 * (Complex.log c).re)) : ℂ) * X 0 1 := by
  have e : 2 * s * (Complex.log c).re = s * (2 * (Complex.log c).re) := by ring
  change (Real.cosh (2 * s * (Complex.log c).re) : ℂ) * Y 0 1 -
    I * (Real.sinh (2 * s * (Complex.log c).re) : ℂ) * X 0 1 = _
  rw [e]

lemma tube_F_diag_c_10 (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) (hY : Yᴴ = Y) (s : ℝ) :
    tube_F_diag_c c X Y s 1 0 = star (tube_F_diag_c c X Y s 0 1) := by
  have hx : X 1 0 = star (X 0 1) := Eq.symm (congr_fun (congr_fun hX 1) 0)
  have hy : Y 1 0 = star (Y 0 1) := Eq.symm (congr_fun (congr_fun hY 1) 0)
  have e : 2 * s * (Complex.log c).re = s * (2 * (Complex.log c).re) := by ring
  rw [tube_F_diag_c_01]
  change (Real.cosh (2 * s * (Complex.log c).re) : ℂ) * Y 1 0 +
    I * (Real.sinh (2 * s * (Complex.log c).re) : ℂ) * X 1 0 = _
  rw [e, hx, hy]
  generalize Real.cosh (s * (2 * (Complex.log c).re)) = A
  generalize Real.sinh (s * (2 * (Complex.log c).re)) = B
  simp
  try ring

lemma tube_F_diag_c_herm (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) (hY : Yᴴ = Y) (s : ℝ) :
    (tube_F_diag_c c X Y s).IsHermitian := by
  apply isHermitian_of_fin_two
  · rw [tube_F_diag_c_re00 c X Y hX hY]; exact Complex.conj_ofReal _
  · rw [tube_F_diag_c_re11 c X Y hX hY]; exact Complex.conj_ofReal _
  · rw [tube_F_diag_c_10 c X Y hX hY]; rfl

lemma tube_F_diag_c_det_re (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) (hY : Yᴴ = Y) (s : ℝ) :
    (tube_F_diag_c c X Y s 0 0 * tube_F_diag_c c X Y s 1 1 -
      tube_F_diag_c c X Y s 0 1 * tube_F_diag_c c X Y s 1 0).re =
    ((Y 0 0).re * Real.cos (s * (2 * (Complex.log c).im)) + (X 0 0).re * Real.sin (s * (2 * (Complex.log c).im))) *
    ((Y 1 1).re * Real.cos (s * (2 * (Complex.log c).im)) + (-(X 1 1).re) * Real.sin (s * (2 * (Complex.log c).im))) -
    ‖(Real.cosh (s * (2 * (Complex.log c).re)) : ℂ) * Y 0 1 -
      I * (Real.sinh (s * (2 * (Complex.log c).re)) : ℂ) * X 0 1‖ ^ 2 := by
  have h : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  rw [tube_F_diag_c_10 c X Y hX hY, Complex.sub_re, h, tube_F_diag_c_01,
    tube_F_diag_c_re00 c X Y hX hY, tube_F_diag_c_re11 c X Y hX hY]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma tube_F_diag_c_posdef (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.IsHermitian) (hY : Y.PosDef)
    (hF1 : (tube_F_diag_c c X Y 1).PosDef)
    (hv : |(Complex.log c).im| ≤ Real.pi / 2)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (tube_F_diag_c c X Y s).PosDef := by
  have hy_herm : Yᴴ = Y := hY.1
  have hx_herm : Xᴴ = X := hX
  rw [posdef_2x2_iff _ (tube_F_diag_c_herm c X Y hx_herm hy_herm s)]
  have hθ : |2 * (Complex.log c).im| ≤ Real.pi := by
    rw [abs_mul]; simp only [abs_two]; linarith
  obtain ⟨hY0, hYdet⟩ := (posdef_2x2_iff Y hy_herm).mp hY
  have hYd := herm_det_re_Y Y hy_herm hYdet
  have hYd' : ‖Y 0 1‖ ^ 2 < (Y 0 0).re * (Y 1 1).re := by
    rw [← Complex.normSq_eq_norm_sq]; linarith
  obtain ⟨hF1a, hF1det⟩ := (posdef_2x2_iff _ hF1.1).mp hF1
  rw [tube_F_diag_c_det_re c X Y hx_herm hy_herm 1] at hF1det
  rw [tube_F_diag_c_re00 c X Y hx_herm hy_herm, Complex.ofReal_re, one_mul] at hF1a
  simp only [one_mul] at hF1det
  have hcore := diag_posdef_core (2 * (Complex.log c).im) (2 * (Complex.log c).re) s hθ hs0 hs1
    (Y 0 0).re (Y 1 1).re (X 0 0).re (X 1 1).re (Y 0 1) (X 0 1) hY0 hYd' hF1a (by linarith)
  constructor
  · rw [tube_F_diag_c_re00 c X Y hx_herm hy_herm, Complex.ofReal_re]
    exact hcore.1
  · rw [tube_F_diag_c_det_re c X Y hx_herm hy_herm s]
    linarith [hcore.2]

lemma concave_pos_of_le_zero (C0 C1 C2 s : ℝ) (hC2 : C2 ≤ 0)
    (h0 : 0 < C0) (h1 : 0 < C0 + C1 + C2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < C0 + C1 * s + C2 * s^2 := by
  have h_eq : C0 + C1 * s + C2 * s^2 = (1 - s) * C0 + s * (C0 + C1 + C2) + C2 * (s^2 - s) := by ring
  rw [h_eq]
  have h_s_sq : s^2 - s ≤ 0 := by
    calc s^2 - s = s * (s - 1) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (by linarith)
  have h_C2_mul : 0 ≤ C2 * (s^2 - s) := mul_nonneg_of_nonpos_of_nonpos hC2 h_s_sq
  have h_C0_mul : 0 ≤ (1 - s) * C0 := mul_nonneg (by linarith) (le_of_lt h0)
  have h_s_mul : 0 ≤ s * (C0 + C1 + C2) := mul_nonneg hs0 (le_of_lt h1)
  have h_pos : 0 < (1 - s) * C0 + s * (C0 + C1 + C2) := by
    rcases eq_or_lt_of_le hs1 with hs1_eq | hs1_lt
    · rw [hs1_eq]; linarith
    · have h_pos_left : 0 < (1 - s) * C0 := mul_pos (by linarith) h0
      linarith
  linarith

lemma jordan_c_conj_entry00 (b x01 y00 y11 : ℂ) (s : ℝ)
    (h00 : (starRingEnd ℂ) y00 = y00) (h11 : (starRingEnd ℂ) y11 = y11) :
    (starRingEnd ℂ) (y00 - 2 * s * (star b * x01).im - s^2 * ‖b‖^2 * y11) =
      y00 - 2 * s * (star b * x01).im - s^2 * ‖b‖^2 * y11 := by
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, h00, h11, h2]

lemma jordan_c_conj_entry01 (b y01 y10 x11 : ℂ) (s : ℝ)
    (h01 : (starRingEnd ℂ) y01 = y10) (hx : (starRingEnd ℂ) x11 = x11) :
    (starRingEnd ℂ) (y01 - I * (s * b) * x11) = y10 + I * (s * star b) * x11 := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, h01, hx, Complex.star_def, Complex.conj_I]
  ring

lemma tube_F_jordan_c_isHermitian (b : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (tube_F_jordan_c b X Y s).IsHermitian := by
  have hy_herm : Yᴴ = Y := hY
  have hx_herm : Xᴴ = X := hX
  have hy00 : (starRingEnd ℂ) (Y 0 0) = Y 0 0 := by exact congr_fun (congr_fun hy_herm 0) 0
  have hy11 : (starRingEnd ℂ) (Y 1 1) = Y 1 1 := by exact congr_fun (congr_fun hy_herm 1) 1
  have hy01 : (starRingEnd ℂ) (Y 0 1) = Y 1 0 := by exact congr_fun (congr_fun hy_herm 1) 0
  have hx11 : (starRingEnd ℂ) (X 1 1) = X 1 1 := by exact congr_fun (congr_fun hx_herm 1) 1
  apply isHermitian_of_fin_two
  · exact jordan_c_conj_entry00 b (X 0 1) (Y 0 0) (Y 1 1) s hy00 hy11
  · exact hy11
  · exact jordan_c_conj_entry01 b (Y 0 1) (Y 1 0) (X 1 1) s hy01 hx11

lemma jordan_c_det_alg (p q ξ s : ℝ) (y b : ℂ) :
    (((p:ℂ) * q - (y - I * (s * b) * ξ) * (star y + I * (s * star b) * ξ))).re =
      p * q - Complex.normSq y - s^2 * ‖b‖^2 * ξ^2 + 2 * s * ξ * (y * star b).im := by
  have : ‖b‖^2 = Complex.normSq b := by rw [Complex.normSq_eq_norm_sq]
  rw [this]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

lemma jordan_c_det_entries (b x01 y01 : ℂ) (p q ξ s : ℝ) :
    ((((p:ℂ) - 2 * s * (star b * x01).im - s^2 * ‖b‖^2 * q) * q -
      (y01 - I * (s * b) * ξ) * (star y01 + I * (s * star b) * ξ))).re =
    (p * q - Complex.normSq y01) +
      (-2 * q * (star b * x01).im + 2 * ξ * (y01 * star b).im) * s +
      (-(‖b‖^2 * (q^2 + ξ^2))) * s^2 := by
  have h := jordan_c_det_alg (p - 2 * s * (star b * x01).im - s^2 * ‖b‖^2 * q) q ξ s y01 b
  push_cast at h
  rw [h]
  ring

lemma tube_F_jordan_c_det_eq_poly (b : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ((tube_F_jordan_c b X Y s 0 0) * (tube_F_jordan_c b X Y s 1 1) -
      (tube_F_jordan_c b X Y s 0 1) * (tube_F_jordan_c b X Y s 1 0)).re =
    ((Y 0 0).re * (Y 1 1).re - Complex.normSq (Y 0 1)) +
      (-2 * (Y 1 1).re * (star b * X 0 1).im + 2 * (X 1 1).re * (Y 0 1 * star b).im) * s +
      (-(‖b‖^2 * ((Y 1 1).re^2 + (X 1 1).re^2))) * s^2 := by
  have hy_herm : Yᴴ = Y := hY
  have hx_herm : Xᴴ = X := hX
  have hy00 : (starRingEnd ℂ) (Y 0 0) = Y 0 0 := by exact congr_fun (congr_fun hy_herm 0) 0
  have hy11 : (starRingEnd ℂ) (Y 1 1) = Y 1 1 := by exact congr_fun (congr_fun hy_herm 1) 1
  have hy01 : (starRingEnd ℂ) (Y 0 1) = Y 1 0 := by exact congr_fun (congr_fun hy_herm 1) 0
  have hx11 : (starRingEnd ℂ) (X 1 1) = X 1 1 := by exact congr_fun (congr_fun hx_herm 1) 1
  have e00 : Y 0 0 = ((Y 0 0).re : ℂ) := (Complex.conj_eq_iff_re.mp hy00).symm
  have e11 : Y 1 1 = ((Y 1 1).re : ℂ) := (Complex.conj_eq_iff_re.mp hy11).symm
  have ex : X 1 1 = ((X 1 1).re : ℂ) := (Complex.conj_eq_iff_re.mp hx11).symm
  have e10 : Y 1 0 = star (Y 0 1) := by rw [← hy01]; rfl
  have key := jordan_c_det_entries b (X 0 1) (Y 0 1) (Y 0 0).re (Y 1 1).re (X 1 1).re s
  rw [← e00, ← e11, ← ex, ← e10] at key
  simpa [tube_F_jordan_c] using key

lemma im_zero_of_conj_eq (z : ℂ) (h : (starRingEnd ℂ) z = z) : z.im = 0 := by
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im] at h2
  linarith

lemma norm_sq_cast_eq_mul_star (a : ℂ) : ((‖a‖ : ℝ) : ℂ) ^ 2 = a * star a := by
  have h := Complex.mul_conj a
  rw [Complex.normSq_eq_norm_sq] at h
  push_cast at h
  rw [Complex.star_def]
  exact h.symm

lemma jordan_c_Y11_re_pos (Y : Matrix (Fin 2) (Fin 2) ℂ) (hY : Y.PosDef) :
    0 < (Y 1 1).re := by
  have hy_herm : Yᴴ = Y := hY.1
  have h_iff := (posdef_2x2_iff Y hy_herm).mp hY
  have h_det := herm_det_re_Y Y hy_herm h_iff.2
  have h_nn : 0 ≤ (normSq (Y 0 1) : ℝ) := normSq_nonneg _
  have h_mul : 0 < (Y 0 0).re * (Y 1 1).re := by linarith
  exact pos_of_mul_pos_right h_mul (le_of_lt h_iff.1)

lemma pos_re00_of_det_pos (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : Fᴴ = F)
    (h11 : 0 < (F 1 1).re) (hdet : 0 < (F 0 0 * F 1 1 - F 0 1 * F 1 0).re) :
    0 < (F 0 0).re := by
  have h := herm_det_re_Y F hF hdet
  have h_nn : 0 ≤ (normSq (F 0 1) : ℝ) := normSq_nonneg _
  have h_mul : 0 < (F 1 1).re * (F 0 0).re := by
    rw [mul_comm]; linarith
  exact pos_of_mul_pos_right h_mul (le_of_lt h11)

lemma jordan_c_det_poly_pos (b : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.IsHermitian) (hY : Y.PosDef)
    (hF1 : (tube_F_jordan_c b X Y 1).PosDef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (tube_F_jordan_c b X Y s 0 0 * tube_F_jordan_c b X Y s 1 1 -
      tube_F_jordan_c b X Y s 0 1 * tube_F_jordan_c b X Y s 1 0).re := by
  have hy_herm : Yᴴ = Y := hY.1
  have h_herm_1 : (tube_F_jordan_c b X Y 1).IsHermitian :=
    tube_F_jordan_c_isHermitian b X Y 1 hX hy_herm
  have h0 := herm_det_re_Y Y hy_herm ((posdef_2x2_iff Y hy_herm).mp hY).2
  have h_det_1 := ((posdef_2x2_iff _ h_herm_1).mp hF1).2
  rw [tube_F_jordan_c_det_eq_poly b X Y 1 hX hy_herm] at h_det_1
  rw [tube_F_jordan_c_det_eq_poly b X Y s hX hy_herm]
  have hC2 : -(‖b‖^2 * ((Y 1 1).re^2 + (X 1 1).re^2)) ≤ 0 :=
    neg_nonpos.mpr (by positivity)
  exact concave_pos_of_le_zero _ _ _ s hC2 h0 (by linarith) hs0 hs1

lemma tube_F_jordan_c_posdef (b : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.IsHermitian) (hY : Y.PosDef)
    (hF1 : (tube_F_jordan_c b X Y 1).PosDef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (tube_F_jordan_c b X Y s).PosDef := by
  have hy_herm : Yᴴ = Y := hY.1
  have h_herm_s : (tube_F_jordan_c b X Y s).IsHermitian :=
    tube_F_jordan_c_isHermitian b X Y s hX hy_herm
  have h_det_s := jordan_c_det_poly_pos b X Y hX hY hF1 s hs0 hs1
  apply (posdef_2x2_iff _ h_herm_s).mpr
  constructor
  · exact pos_re00_of_det_pos _ h_herm_s (jordan_c_Y11_re_pos Y hY) h_det_s
  · exact h_det_s


lemma posdef_congruence_inv (M P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.det ≠ 0)
    (hM : (P * M * Pᴴ).PosDef) : M.PosDef := by
  have h_det : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have h_det_conj : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hP)
  have h_herm : M.IsHermitian := by
    dsimp [Matrix.IsHermitian]
    have h4 : P * M * Pᴴ = (P * M * Pᴴ)ᴴ := hM.1.symm
    rw [conjTranspose_mul_triple M P] at h4
    have h5 : P⁻¹ * (P * M * Pᴴ) = P⁻¹ * (P * Mᴴ * Pᴴ) := by rw [h4]
    have hm1 : P * M * Pᴴ = P * (M * Pᴴ) := Matrix.mul_assoc P M Pᴴ
    have hm2 : P * Mᴴ * Pᴴ = P * (Mᴴ * Pᴴ) := Matrix.mul_assoc P Mᴴ Pᴴ
    rw [hm1, hm2] at h5
    rw [← Matrix.mul_assoc P⁻¹ P (M * Pᴴ), ← Matrix.mul_assoc P⁻¹ P (Mᴴ * Pᴴ)] at h5
    rw [nonsing_inv_mul _ h_det, Matrix.one_mul, Matrix.one_mul] at h5
    have h6 : (M * Pᴴ) * (Pᴴ)⁻¹ = (Mᴴ * Pᴴ) * (Pᴴ)⁻¹ := by rw [h5]
    rw [Matrix.mul_assoc M Pᴴ (Pᴴ)⁻¹, Matrix.mul_assoc Mᴴ Pᴴ (Pᴴ)⁻¹] at h6
    rw [mul_nonsing_inv _ h_det_conj, Matrix.mul_one, Matrix.mul_one] at h6
    exact h6.symm

  apply posDef_iff_dotProduct_mulVec.mpr
  constructor
  · exact h_herm
  · intro x hx
    have hM_dot := posDef_iff_dotProduct_mulVec.mp hM
    let y := (Pᴴ)⁻¹ *ᵥ x
    have hy : y ≠ 0 := by
      intro h_zero
      have hx_zero : Pᴴ *ᵥ y = Pᴴ *ᵥ 0 := by rw [h_zero]
      rw [Matrix.mulVec_zero] at hx_zero
      have hx_zero2 : Pᴴ *ᵥ y = (Pᴴ * (Pᴴ)⁻¹) *ᵥ x := by
        dsimp [y]
        rw [← Matrix.mulVec_mulVec x Pᴴ (Pᴴ)⁻¹]
      rw [mul_nonsing_inv _ h_det_conj, one_mulVec] at hx_zero2
      rw [hx_zero2] at hx_zero
      exact hx hx_zero
    have h2 : star y ⬝ᵥ ((P * M * Pᴴ) *ᵥ y) > 0 := hM_dot.2 hy
    rw [dot_mulVec_assoc M P y] at h2
    have hyx : Pᴴ *ᵥ y = x := by
      dsimp [y]
      rw [Matrix.mulVec_mulVec x Pᴴ (Pᴴ)⁻¹, mul_nonsing_inv _ h_det_conj, one_mulVec]
    rw [hyx] at h2
    exact h2






def RealLorentzLieAlgebra : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := { M | Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0 }
  add_mem' {A B} hA hB := by
    change (A + B)ᵀ * minkowskiMetricReal + minkowskiMetricReal * (A + B) = 0
    rw [transpose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 : Aᵀ * minkowskiMetricReal + minkowskiMetricReal * A = 0 := hA
    have h2 : Bᵀ * minkowskiMetricReal + minkowskiMetricReal * B = 0 := hB
    rw [add_add_add_comm, h1, h2, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * minkowskiMetricReal + minkowskiMetricReal * 0 = 0
    simp
  smul_mem' c A hA := by
    change (c • A)ᵀ * minkowskiMetricReal + minkowskiMetricReal * (c • A) = 0
    rw [transpose_smul, smul_mul_assoc, mul_smul_comm, ←smul_add]
    have h1 : Aᵀ * minkowskiMetricReal + minkowskiMetricReal * A = 0 := hA
    rw [h1, smul_zero]


def real_matrix_to_complex (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  M.map (fun x => (x : ℂ))

@[simp] lemma rmc_mul (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    real_matrix_to_complex (A * B) = real_matrix_to_complex A * real_matrix_to_complex B := by
  ext i j; simp [real_matrix_to_complex, Matrix.mul_apply]

@[simp] lemma rmc_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    real_matrix_to_complex (A + B) = real_matrix_to_complex A + real_matrix_to_complex B := by
  ext i j; simp [real_matrix_to_complex]

@[simp] lemma rmc_transpose (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (real_matrix_to_complex A)ᵀ = real_matrix_to_complex Aᵀ := by
  ext i j; simp [real_matrix_to_complex]

@[simp] lemma rmc_zero : real_matrix_to_complex 0 = 0 := by
  ext i j; simp [real_matrix_to_complex]

@[simp] lemma rmc_metric : real_matrix_to_complex minkowskiMetricReal = minkowskiMetric := by
  ext i j
  simp [real_matrix_to_complex, minkowskiMetric, minkowskiMetricReal]
  fin_cases i <;> fin_cases j <;> norm_num


noncomputable def lorentz_exp (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  NormedSpace.exp M

lemma commute_I_neg_I (M : Matrix (Fin 4) (Fin 4) ℂ) : Commute (I • M) ((-I) • M) := by
  dsimp [Commute, SemiconjBy]
  rw [smul_mul_smul, smul_mul_smul, mul_neg, neg_mul]

lemma lorentz_exp_add_cancel (M : Matrix (Fin 4) (Fin 4) ℂ) :
    lorentz_exp (I • M) * lorentz_exp ((-I) • M) = 1 := by
  dsimp [lorentz_exp]
  rw [← Matrix.exp_add_of_commute _ _ (commute_I_neg_I M)]
  have h_add : I • M + (-I) • M = 0 := by
    rw [← add_smul, add_neg_cancel, zero_smul]
  rw [h_add, NormedSpace.exp_zero]

lemma lorentz_exp_add_cancel_rev (M : Matrix (Fin 4) (Fin 4) ℂ) :
    lorentz_exp ((-I) • M) * lorentz_exp (I • M) = 1 := by
  dsimp [lorentz_exp]
  rw [← Matrix.exp_add_of_commute _ _ (commute_I_neg_I M).symm]
  have h_add : (-I) • M + I • M = 0 := by
    rw [← add_smul, neg_add_cancel, zero_smul]
  rw [h_add, NormedSpace.exp_zero]

lemma isUnit_metric : IsUnit minkowskiMetric := by
  have h_mul : minkowskiMetric * minkowskiMetric = 1 := by
    ext i j
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> norm_num
  exact ⟨⟨minkowskiMetric, minkowskiMetric, h_mul, h_mul⟩, rfl⟩

lemma metric_inv_eq : minkowskiMetric⁻¹ = minkowskiMetric := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num

lemma exp_iM_prop1 (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0) :
    (lorentz_exp (I • real_matrix_to_complex M))ᵀ * minkowskiMetric * lorentz_exp (I • real_matrix_to_complex M) = minkowskiMetric := by
  have hM_c : (real_matrix_to_complex M)ᵀ * minkowskiMetric + minkowskiMetric * real_matrix_to_complex M = 0 := by
    have h1 : real_matrix_to_complex (Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M) = 0 := by rw [hM, rmc_zero]
    simp at h1
    exact h1
  have h_transpose : (I • real_matrix_to_complex M)ᵀ = I • (real_matrix_to_complex M)ᵀ := by
    ext i j; simp [real_matrix_to_complex]
  dsimp [lorentz_exp]
  rw [← Matrix.exp_transpose, h_transpose]
  have h_sub : (real_matrix_to_complex M)ᵀ = - minkowskiMetric * real_matrix_to_complex M * minkowskiMetric := by
    have h_metric_sq : minkowskiMetric * minkowskiMetric = 1 := by
      ext i j; simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]; fin_cases i <;> fin_cases j <;> norm_num
    calc (real_matrix_to_complex M)ᵀ = (real_matrix_to_complex M)ᵀ * 1 := by rw [Matrix.mul_one]
      _ = (real_matrix_to_complex M)ᵀ * (minkowskiMetric * minkowskiMetric) := by rw [h_metric_sq]
      _ = ((real_matrix_to_complex M)ᵀ * minkowskiMetric) * minkowskiMetric := by rw [← Matrix.mul_assoc]
      _ = (- (minkowskiMetric * real_matrix_to_complex M)) * minkowskiMetric := by rw [eq_neg_of_add_eq_zero_left hM_c]
      _ = - minkowskiMetric * real_matrix_to_complex M * minkowskiMetric := by simp [neg_mul, Matrix.mul_assoc]
  have h_smul : I • (real_matrix_to_complex M)ᵀ = minkowskiMetric * ((-I) • real_matrix_to_complex M) * minkowskiMetric⁻¹ := by
    rw [h_sub, metric_inv_eq]
    ext i j; simp [Matrix.mul_apply, Matrix.smul_apply, minkowskiMetric]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four]
  rw [h_smul]
  rw [Matrix.exp_conj _ _ isUnit_metric]
  have h_mul : minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M) * minkowskiMetric⁻¹ * minkowskiMetric * NormedSpace.exp (I • real_matrix_to_complex M) = minkowskiMetric := by
    rw [metric_inv_eq]
    have h_metric_sq : minkowskiMetric * minkowskiMetric = 1 := by
      ext i j; simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]; fin_cases i <;> fin_cases j <;> norm_num
    calc minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M) * minkowskiMetric * minkowskiMetric * NormedSpace.exp (I • real_matrix_to_complex M)
      _ = minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M) * (minkowskiMetric * minkowskiMetric) * NormedSpace.exp (I • real_matrix_to_complex M) := by rw [Matrix.mul_assoc (minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M)) minkowskiMetric minkowskiMetric]
      _ = minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M) * 1 * NormedSpace.exp (I • real_matrix_to_complex M) := by rw [h_metric_sq]
      _ = minkowskiMetric * NormedSpace.exp ((-I) • real_matrix_to_complex M) * NormedSpace.exp (I • real_matrix_to_complex M) := by rw [Matrix.mul_one]
      _ = minkowskiMetric * (NormedSpace.exp ((-I) • real_matrix_to_complex M) * NormedSpace.exp (I • real_matrix_to_complex M)) := by rw [Matrix.mul_assoc]
      _ = minkowskiMetric * 1 := by
        have h_cancel := lorentz_exp_add_cancel_rev (real_matrix_to_complex M)
        dsimp [lorentz_exp] at h_cancel
        rw [h_cancel]
      _ = minkowskiMetric := Matrix.mul_one _
  exact h_mul

lemma det_sq_eq_one_test (Y : Matrix (Fin 4) (Fin 4) ℂ) (hY : Yᵀ * minkowskiMetric * Y = minkowskiMetric) :
    Y.det ^ 2 = 1 := by
  have h_det : (Yᵀ * minkowskiMetric * Y).det = minkowskiMetric.det := by rw [hY]
  rw [det_mul, det_mul, det_transpose] at h_det
  have h_metric_det : minkowskiMetric.det = -1 := by
    dsimp [minkowskiMetric]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [h_metric_det] at h_det
  calc Y.det ^ 2 = - (Y.det * -1 * Y.det) := by ring
    _ = - (-1) := by rw [h_det]
    _ = 1 := by ring

lemma exp_iM_det_eq_one (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0) :
    (lorentz_exp (I • real_matrix_to_complex M)).det = 1 := by
  have hM_half : ((2 : ℝ)⁻¹ • M)ᵀ * minkowskiMetricReal + minkowskiMetricReal * ((2 : ℝ)⁻¹ • M) = 0 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hM, smul_zero]
  have hY := exp_iM_prop1 ((2 : ℝ)⁻¹ • M) hM_half
  have h_rewrite : I • real_matrix_to_complex ((2 : ℝ)⁻¹ • M) = (2 : ℂ)⁻¹ • I • real_matrix_to_complex M := by
    ext i j; simp [real_matrix_to_complex]; ring
  rw [h_rewrite] at hY
  have h_comm : Commute ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M) ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M) := rfl
  have h_add : (2 : ℂ)⁻¹ • I • real_matrix_to_complex M + (2 : ℂ)⁻¹ • I • real_matrix_to_complex M = I • real_matrix_to_complex M := by
    rw [← add_smul]
    have h2 : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by norm_num
    rw [h2, one_smul]
  have hX : lorentz_exp (I • real_matrix_to_complex M) = lorentz_exp ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M) * lorentz_exp ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M) := by
    dsimp [lorentz_exp]
    rw [← Matrix.exp_add_of_commute _ _ h_comm, h_add]
  rw [hX, det_mul]
  have h1 := det_sq_eq_one_test _ hY
  calc (lorentz_exp ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M)).det * (lorentz_exp ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M)).det
      = (lorentz_exp ((2 : ℂ)⁻¹ • I • real_matrix_to_complex M)).det ^ 2 := by ring
    _ = 1 := h1


noncomputable def exp_iM (M : RealLorentzLieAlgebra) : SpecialSpecialComplexLorentzGroup :=
  ⟨⟨lorentz_exp (I • real_matrix_to_complex M.val),
    lorentz_exp ((-I) • real_matrix_to_complex M.val),
    lorentz_exp_add_cancel (real_matrix_to_complex M.val),
    lorentz_exp_add_cancel_rev (real_matrix_to_complex M.val)⟩,
   by
     constructor
     · exact exp_iM_prop1 M.val M.property
     · exact exp_iM_det_eq_one M.val M.property⟩
lemma h00 (a b c d : ℂ) : !![a, b; c, d] 0 0 = a := rfl
lemma h01 (a b c d : ℂ) : !![a, b; c, d] 0 1 = b := rfl
lemma h10 (a b c d : ℂ) : !![a, b; c, d] 1 0 = c := rfl
lemma h11 (a b c d : ℂ) : !![a, b; c, d] 1 1 = d := rfl

lemma sl2c_jordan_case1 (x y z w : ℂ) (h_det : x * w - y * z = 1)
  (delta : ℂ) (h_delta : delta ^ 2 = (x + w) ^ 2 - 4)
  (lam1 lam2 : ℂ) (h_lam1 : lam1 = (x + w + delta) / 2) (h_lam2 : lam2 = (x + w - delta) / 2) :
  !![x, y; z, w] * !![lam1 - w, lam2 - w; z, z] = !![lam1 - w, lam2 - w; z, z] * !![lam1, 0; 0, lam2] := by
  have e1 : 2 * lam1 = x + w + delta := by
    calc 2 * lam1 = 2 * ((x + w + delta) / 2) := by rw [h_lam1]
      _ = x + w + delta := by ring
  have e2 : 2 * lam2 = x + w - delta := by
    calc 2 * lam2 = 2 * ((x + w - delta) / 2) := by rw [h_lam2]
      _ = x + w - delta := by ring
  have e_sum : lam1 + lam2 = x + w := by
    calc lam1 + lam2 = (x + w + delta) / 2 + (x + w - delta) / 2 := by rw [h_lam1, h_lam2]
      _ = x + w := by ring
  have e_prod : lam1 * lam2 = 1 := by
    calc lam1 * lam2 = (x + w + delta) * (x + w - delta) / 4 := by rw [h_lam1, h_lam2]; ring
      _ = ((x + w)^2 - delta^2) / 4 := by ring
      _ = ((x + w)^2 - ((x + w)^2 - 4)) / 4 := by rw [h_delta]
      _ = 1 := by ring
  have h00 (a b c d : ℂ) : !![a, b; c, d] 0 0 = a := rfl
  have h01 (a b c d : ℂ) : !![a, b; c, d] 0 1 = b := rfl
  have h10 (a b c d : ℂ) : !![a, b; c, d] 1 0 = c := rfl
  have h11 (a b c d : ℂ) : !![a, b; c, d] 1 1 = d := rfl
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * (lam1 - w) + y * z = x * lam1 - x * w + y * z := by ring
      _ = x * lam1 - (x * w - y * z) := by ring
      _ = x * lam1 - 1 := by rw [h_det]
      _ = x * lam1 - lam1 * lam2 := by rw [e_prod]
      _ = lam1 * (x - lam2) := by ring
      _ = lam1 * (x - ((x + w) - lam1)) := by rw [← e_sum]; ring
      _ = lam1 * (lam1 - w) := by ring
      _ = (lam1 - w) * lam1 + (lam2 - w) * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * (lam2 - w) + y * z = x * lam2 - x * w + y * z := by ring
      _ = x * lam2 - (x * w - y * z) := by ring
      _ = x * lam2 - 1 := by rw [h_det]
      _ = x * lam2 - lam1 * lam2 := by rw [e_prod]
      _ = lam2 * (x - lam1) := by ring
      _ = lam2 * (x - ((x + w) - lam2)) := by rw [← e_sum]; ring
      _ = lam2 * (lam2 - w) := by ring
      _ = (lam1 - w) * 0 + (lam2 - w) * lam2 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc z * (lam1 - w) + w * z = z * lam1 - z * w + w * z := by ring
      _ = z * lam1 + z * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc z * (lam2 - w) + w * z = z * lam2 - z * w + w * z := by ring
      _ = z * 0 + z * lam2 := by ring

lemma sl2c_jordan_case2 (x y w : ℂ) (h_det : x * w = 1) :
  !![x, y; 0, w] * !![1, y; 0, w - x] = !![1, y; 0, w - x] * !![x, 0; 0, w] := by
  have h00 (a b c d : ℂ) : !![a, b; c, d] 0 0 = a := rfl
  have h01 (a b c d : ℂ) : !![a, b; c, d] 0 1 = b := rfl
  have h10 (a b c d : ℂ) : !![a, b; c, d] 1 0 = c := rfl
  have h11 (a b c d : ℂ) : !![a, b; c, d] 1 1 = d := rfl
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * 1 + y * 0 = x := by ring
      _ = 1 * x + y * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * y + y * (w - x) = y * w := by ring
      _ = 1 * 0 + y * w := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc 0 * 1 + w * 0 = 0 := by ring
      _ = 0 * x + (w - x) * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc 0 * y + w * (w - x) = (w - x) * w := by ring
      _ = 0 * 0 + (w - x) * w := by ring

lemma sl2c_jordan_case3 (x y z w c : ℂ) (h_det : x * w - y * z = 1)
  (h_delta : (x + w) ^ 2 = 4) (h_c : 2 * c = x + w) :
  !![x, y; z, w] * !![c - w, 1; z, 0] = !![c - w, 1; z, 0] * !![c, 1; 0, c] := by
  have h_c2 : c ^ 2 = 1 := by
    calc c ^ 2 = (2 * c) ^ 2 / 4 := by ring
      _ = (x + w) ^ 2 / 4 := by rw [h_c]
      _ = 4 / 4 := by rw [h_delta]
      _ = 1 := by ring
  have h_w : w = 2 * c - x := by
    calc w = (x + w) - x := by ring
      _ = 2 * c - x := by rw [← h_c]
  have h00 (a b c d : ℂ) : !![a, b; c, d] 0 0 = a := rfl
  have h01 (a b c d : ℂ) : !![a, b; c, d] 0 1 = b := rfl
  have h10 (a b c d : ℂ) : !![a, b; c, d] 1 0 = c := rfl
  have h11 (a b c d : ℂ) : !![a, b; c, d] 1 1 = d := rfl
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * (c - w) + y * z = x * c - x * w + y * z := by ring
      _ = x * c - (x * w - y * z) := by ring
      _ = x * c - 1 := by rw [h_det]
      _ = x * c - c ^ 2 := by rw [h_c2]
      _ = c * (x - c) := by ring
      _ = c * (x - (2 * c - c)) := by ring
      _ = c * (x - (x + w - c)) := by rw [← h_c]
      _ = c * (c - w) := by ring
      _ = (c - w) * c + 1 * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc x * 1 + y * 0 = x := by ring
      _ = (x + w) - w := by ring
      _ = 2 * c - w := by rw [← h_c]
      _ = (c - w) * 1 + 1 * c := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc z * (c - w) + w * z = z * c - z * w + w * z := by ring
      _ = z * c + 0 * 0 := by ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc z * 1 + w * 0 = z := by ring
      _ = z * 1 + 0 * c := by ring

lemma P_c_trick (P V D : Matrix (Fin 2) (Fin 2) ℂ) (h : P * V = V * D) (c : ℂ) :
  P * (c • V) = (c • V) * D := by
  calc P * (c • V) = c • (P * V) := by exact Matrix.mul_smul P c V
    _ = c • (V * D) := by rw [h]
    _ = (c • V) * D := by exact Eq.symm (Matrix.smul_mul c V D)

lemma P_c_inv_trick (P P_c D : Matrix (Fin 2) (Fin 2) ℂ) (h : P * P_c = P_c * D) (h_inv : P_c * P_c⁻¹ = 1) :
  P = P_c * D * P_c⁻¹ := by
  calc P = P * 1 := by rw [Matrix.mul_one]
    _ = P * (P_c * P_c⁻¹) := by rw [← h_inv]
    _ = (P * P_c) * P_c⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P_c * D) * P_c⁻¹ := by rw [h]
    _ = P_c * D * P_c⁻¹ := by rw [Matrix.mul_assoc]

lemma sl2c_jordan_decomp_proof_case1 (x y z w : ℂ) (h_det : x * w - y * z = 1) (hz : z ≠ 0) (h_tr : (x + w) ^ 2 ≠ 4) :
    ∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0),
      !![x, y; z, w] = P_c.val * (diag_matrix c hc).val * P_c.val⁻¹ := by
  obtain ⟨delta, h_delta2⟩ : ∃ delta : ℂ, delta ^ 2 = (x + w) ^ 2 - 4 := IsAlgClosed.exists_pow_nat_eq ((x + w) ^ 2 - 4) (by decide : 0 < 2)
  have h_delta_ne_0 : delta ≠ 0 := by
    intro h
    have h1 : delta ^ 2 = 0 := by
      calc delta ^ 2 = 0 ^ 2 := by rw [h]
        _ = 0 := by ring
    rw [h1] at h_delta2
    have h2 : (x + w) ^ 2 = 4 := by
      calc (x + w) ^ 2 = (x + w) ^ 2 - 4 + 4 := by ring
        _ = 0 + 4 := by rw [← h_delta2]
        _ = 4 := by ring
    exact h_tr h2
  let lam1 := (x + w + delta) / 2
  let lam2 := (x + w - delta) / 2
  have h_comm : !![x, y; z, w] * !![lam1 - w, lam2 - w; z, z] = !![lam1 - w, lam2 - w; z, z] * !![lam1, 0; 0, lam2] := sl2c_jordan_case1 x y z w h_det delta h_delta2 lam1 lam2 rfl rfl
  let V : Matrix (Fin 2) (Fin 2) ℂ := !![lam1 - w, lam2 - w; z, z]
  have h_det_V : V.det = z * delta := by
    calc V.det = (lam1 - w) * z - (lam2 - w) * z := by simp [V, Matrix.det_fin_two]
      _ = z * (lam1 - lam2) := by ring
      _ = z * (((x + w + delta) / 2) - ((x + w - delta) / 2)) := rfl
      _ = z * delta := by ring
  have h_det_V_ne_0 : V.det ≠ 0 := by
    rw [h_det_V]
    intro h
    cases mul_eq_zero.mp h with
    | inl h2 => exact hz h2
    | inr h3 => exact h_delta_ne_0 h3
  obtain ⟨sq, h_sq2⟩ : ∃ sq : ℂ, sq ^ 2 = V.det ⁻¹ := IsAlgClosed.exists_pow_nat_eq (V.det ⁻¹) (by decide : 0 < 2)
  let P_c_val := sq • V
  have h_det_Pc : P_c_val.det = 1 := by
    calc P_c_val.det = sq ^ 2 * V.det := by
          have hd2 : (sq • V).det = sq ^ (Fintype.card (Fin 2)) * V.det := Matrix.det_smul V sq
          have hcard : Fintype.card (Fin 2) = 2 := rfl
          rwa [hcard] at hd2
      _ = V.det ⁻¹ * V.det := by rw [h_sq2]
      _ = 1 := by exact inv_mul_cancel₀ h_det_V_ne_0
  let P_c : SpecialLinearGroup (Fin 2) ℂ := ⟨P_c_val, h_det_Pc⟩
  let c := lam1
  have hc : c ≠ 0 := by
    intro h
    have h2 : x + w + delta = 0 := by
      calc x + w + delta = ((x + w + delta) / 2) * 2 := by ring
        _ = c * 2 := rfl
        _ = 0 * 2 := by rw [h]
        _ = 0 := by ring
    have h3 : delta = -(x + w) := by
      calc delta = x + w + delta - (x + w) := by ring
        _ = 0 - (x + w) := by rw [h2]
        _ = -(x + w) := by ring
    have h4 : delta ^ 2 = (x + w) ^ 2 := by
      calc delta ^ 2 = (-(x + w)) ^ 2 := by rw [h3]
        _ = (x + w) ^ 2 := by ring
    have h5 : (x + w) ^ 2 = (x + w) ^ 2 - 4 := by
      calc (x + w) ^ 2 = delta ^ 2 := by rw [h4]
        _ = (x + w) ^ 2 - 4 := h_delta2
    have h6 : (x + w) ^ 2 - (x + w) ^ 2 = (x + w) ^ 2 - 4 - (x + w) ^ 2 := congrArg (fun u => u - (x + w) ^ 2) h5
    have h7 : (0 : ℂ) = -4 := by
      calc (0 : ℂ) = (x + w) ^ 2 - (x + w) ^ 2 := by ring
        _ = (x + w) ^ 2 - 4 - (x + w) ^ 2 := h6
        _ = -4 := by ring
    exact absurd h7 (by norm_num)
  use P_c, c, hc
  have hc_inv : c⁻¹ = lam2 := by
    have hc2 : c * lam2 = 1 := by
      calc c * lam2 = ((x + w + delta) / 2) * ((x + w - delta) / 2) := rfl
        _ = ((x + w) ^ 2 - delta ^ 2) / 4 := by ring
        _ = ((x + w) ^ 2 - ((x + w) ^ 2 - 4)) / 4 := by rw [h_delta2]
        _ = 4 / 4 := by ring
        _ = 1 := by norm_num
    calc c⁻¹ = c⁻¹ * 1 := by ring
      _ = c⁻¹ * (c * lam2) := by rw [← hc2]
      _ = (c⁻¹ * c) * lam2 := by rw [mul_assoc]
      _ = 1 * lam2 := by rw [inv_mul_cancel₀ hc]
      _ = lam2 := by ring
  have h_diag_eq : (diag_matrix c hc).val = !![lam1, 0; 0, lam2] := by
    have h_diag : (diag_matrix c hc).val = !![c, 0; 0, c⁻¹] := rfl
    calc (diag_matrix c hc).val = !![c, 0; 0, c⁻¹] := h_diag
      _ = !![lam1, 0; 0, lam2] := by rw [hc_inv]
  have h_comm_smul : !![x, y; z, w] * P_c_val = P_c_val * !![lam1, 0; 0, lam2] := P_c_trick !![x, y; z, w] V !![lam1, 0; 0, lam2] h_comm sq
  rw [h_diag_eq]
  have h_inv : P_c_val * P_c_val⁻¹ = 1 := by
    have hd_ne : P_c_val.det ≠ 0 := by rw [h_det_Pc]; exact one_ne_zero
    have hd_unit : IsUnit P_c_val.det := isUnit_iff_ne_zero.mpr hd_ne
    exact Matrix.mul_nonsing_inv P_c_val hd_unit
  exact P_c_inv_trick !![x, y; z, w] P_c_val !![lam1, 0; 0, lam2] h_comm_smul h_inv

lemma sl2c_jordan_decomp_proof_case2 (x y w : ℂ) (h_det : x * w = 1) (h_eq : x ≠ w) :
    ∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0),
      !![x, y; 0, w] = P_c.val * (diag_matrix c hc).val * P_c.val⁻¹ := by
  let V : Matrix (Fin 2) (Fin 2) ℂ := !![1, y; 0, w - x]
  have h_comm : !![x, y; 0, w] * V = V * !![x, 0; 0, w] := sl2c_jordan_case2 x y w h_det
  obtain ⟨sq, h_sq2⟩ : ∃ sq : ℂ, sq ^ 2 = (w - x) ⁻¹ := IsAlgClosed.exists_pow_nat_eq ((w - x) ⁻¹) (by decide : 0 < 2)
  let P_c_val := sq • V
  have h_det_V : V.det = w - x := by
    simp [V, Matrix.det_fin_two]
  have h_det_Pc : P_c_val.det = 1 := by
    calc P_c_val.det = sq ^ 2 * V.det := by
          have hd : P_c_val.det = sq ^ 2 * V.det := by
            have hd2 : (sq • V).det = sq ^ (Fintype.card (Fin 2)) * V.det := Matrix.det_smul V sq
            have hcard : Fintype.card (Fin 2) = 2 := rfl
            rwa [hcard] at hd2
          exact hd
      _ = (w - x) ⁻¹ * (w - x) := by rw [h_sq2, h_det_V]
      _ = 1 := by exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm h_eq))
  let P_c : SpecialLinearGroup (Fin 2) ℂ := ⟨P_c_val, h_det_Pc⟩
  use P_c, x
  have hx_ne_0 : x ≠ 0 := by
    intro h
    rw [h, zero_mul] at h_det
    exact zero_ne_one h_det
  use hx_ne_0
  have h_diag : (diag_matrix x hx_ne_0).val = !![x, 0; 0, x⁻¹] := rfl
  have h_w_inv : w = x⁻¹ := by
    calc w = 1 * w := by ring
      _ = (x⁻¹ * x) * w := by rw [inv_mul_cancel₀ hx_ne_0]
      _ = x⁻¹ * (x * w) := by ring
      _ = x⁻¹ * 1 := by rw [h_det]
      _ = x⁻¹ := by ring
  have h_diag_eq : (diag_matrix x hx_ne_0).val = !![x, 0; 0, w] := by
    rw [h_diag, h_w_inv]
  have h_comm_smul : !![x, y; 0, w] * P_c_val = P_c_val * !![x, 0; 0, w] := P_c_trick !![x, y; 0, w] V !![x, 0; 0, w] h_comm sq
  rw [h_diag_eq]
  have h_inv : P_c_val * P_c_val⁻¹ = 1 := by
    have hd_ne : P_c_val.det ≠ 0 := by rw [h_det_Pc]; exact one_ne_zero
    have hd_unit : IsUnit P_c_val.det := isUnit_iff_ne_zero.mpr hd_ne
    exact Matrix.mul_nonsing_inv P_c_val hd_unit
  exact P_c_inv_trick !![x, y; 0, w] P_c_val !![x, 0; 0, w] h_comm_smul h_inv

lemma sl2c_jordan_decomp_proof_case3 (x y z w : ℂ) (h_det : x * w - y * z = 1) (hz : z ≠ 0) (h_tr : (x + w) ^ 2 = 4) :
    ∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (s_a : ℂ) (h_s : s_a = 1 ∨ s_a = -1),
      !![x, y; z, w] = P_c.val * !![s_a, a; 0, s_a] * P_c.val⁻¹ := by
  have hs : (x + w) / 2 = 1 ∨ (x + w) / 2 = -1 := by
    have h1 : ((x + w) / 2) ^ 2 = 1 := by
      calc ((x + w) / 2) ^ 2 = (x + w) ^ 2 / 4 := by ring
        _ = 4 / 4 := by rw [h_tr]
        _ = 1 := by norm_num
    have h2 : (((x + w) / 2) - 1) * (((x + w) / 2) + 1) = 0 := by
      calc (((x + w) / 2) - 1) * (((x + w) / 2) + 1) = ((x + w) / 2) ^ 2 - 1 := by ring
        _ = 1 - 1 := by rw [h1]
        _ = 0 := by ring
    cases mul_eq_zero.mp h2 with
    | inl h3 => left; exact sub_eq_zero.mp h3
    | inr h4 => right; exact eq_neg_iff_add_eq_zero.mpr h4
  rcases hs with h1 | h2
  · let s_a : ℂ := 1
    have h_s : s_a = 1 ∨ s_a = -1 := Or.inl rfl
    have h_trace : 2 * s_a = x + w := by
      calc 2 * s_a = 2 * 1 := rfl
        _ = 2 * ((x + w) / 2) := by rw [h1]
        _ = x + w := by ring
    let V : Matrix (Fin 2) (Fin 2) ℂ := !![s_a - w, 1; z, 0]
    have h_comm : !![x, y; z, w] * V = V * !![s_a, 1; 0, s_a] := sl2c_jordan_case3 x y z w s_a h_det h_tr h_trace
    obtain ⟨sq, h_sq2⟩ : ∃ sq : ℂ, sq ^ 2 = (-z) ⁻¹ := IsAlgClosed.exists_pow_nat_eq ((-z) ⁻¹) (by decide : 0 < 2)
    let P_c_val := sq • V
    have h_det_V : V.det = -z := by
      simp [V, Matrix.det_fin_two]
    have h_det_Pc : P_c_val.det = 1 := by
      calc P_c_val.det = sq ^ 2 * V.det := by
            have hd2 : (sq • V).det = sq ^ (Fintype.card (Fin 2)) * V.det := Matrix.det_smul V sq
            have hcard : Fintype.card (Fin 2) = 2 := rfl
            rwa [hcard] at hd2
        _ = (-z) ⁻¹ * (-z) := by rw [h_sq2, h_det_V]
        _ = 1 := by exact inv_mul_cancel₀ (neg_ne_zero.mpr hz)
    let P_c : SpecialLinearGroup (Fin 2) ℂ := ⟨P_c_val, h_det_Pc⟩
    use P_c, 1, s_a, h_s
    have h_comm_smul : !![x, y; z, w] * P_c_val = P_c_val * !![s_a, 1; 0, s_a] := P_c_trick !![x, y; z, w] V !![s_a, 1; 0, s_a] h_comm sq
    have h_inv : P_c_val * P_c_val⁻¹ = 1 := by
      have hd_ne : P_c_val.det ≠ 0 := by rw [h_det_Pc]; exact one_ne_zero
      have hd_unit : IsUnit P_c_val.det := isUnit_iff_ne_zero.mpr hd_ne
      exact Matrix.mul_nonsing_inv P_c_val hd_unit
    exact P_c_inv_trick !![x, y; z, w] P_c_val !![s_a, 1; 0, s_a] h_comm_smul h_inv
  · let s_a : ℂ := -1
    have h_s : s_a = 1 ∨ s_a = -1 := Or.inr rfl
    have h_trace : 2 * s_a = x + w := by
      calc 2 * s_a = 2 * (-1) := rfl
        _ = 2 * ((x + w) / 2) := by rw [h2]
        _ = x + w := by ring
    let V : Matrix (Fin 2) (Fin 2) ℂ := !![s_a - w, 1; z, 0]
    have h_comm : !![x, y; z, w] * V = V * !![s_a, 1; 0, s_a] := sl2c_jordan_case3 x y z w s_a h_det h_tr h_trace
    obtain ⟨sq, h_sq2⟩ : ∃ sq : ℂ, sq ^ 2 = (-z) ⁻¹ := IsAlgClosed.exists_pow_nat_eq ((-z) ⁻¹) (by decide : 0 < 2)
    let P_c_val := sq • V
    have h_det_V : V.det = -z := by
      simp [V, Matrix.det_fin_two]
    have h_det_Pc : P_c_val.det = 1 := by
      calc P_c_val.det = sq ^ 2 * V.det := by
            have hd2 : (sq • V).det = sq ^ (Fintype.card (Fin 2)) * V.det := Matrix.det_smul V sq
            have hcard : Fintype.card (Fin 2) = 2 := rfl
            rwa [hcard] at hd2
        _ = (-z) ⁻¹ * (-z) := by rw [h_sq2, h_det_V]
        _ = 1 := by exact inv_mul_cancel₀ (neg_ne_zero.mpr hz)
    let P_c : SpecialLinearGroup (Fin 2) ℂ := ⟨P_c_val, h_det_Pc⟩
    use P_c, 1, s_a, h_s
    have h_comm_smul : !![x, y; z, w] * P_c_val = P_c_val * !![s_a, 1; 0, s_a] := P_c_trick !![x, y; z, w] V !![s_a, 1; 0, s_a] h_comm sq
    have h_inv : P_c_val * P_c_val⁻¹ = 1 := by
      have hd_ne : P_c_val.det ≠ 0 := by rw [h_det_Pc]; exact one_ne_zero
      have hd_unit : IsUnit P_c_val.det := isUnit_iff_ne_zero.mpr hd_ne
      exact Matrix.mul_nonsing_inv P_c_val hd_unit
    exact P_c_inv_trick !![x, y; z, w] P_c_val !![s_a, 1; 0, s_a] h_comm_smul h_inv

lemma sl2c_jordan_decomp (P : SpecialLinearGroup (Fin 2) ℂ) :
    (∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0), P.val = P_c.val * (diag_matrix c hc).val * P_c.val⁻¹) ∨
    (∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (s_a : ℂ) (h_s : s_a = 1 ∨ s_a = -1),
      P.val = P_c.val * !![s_a, a; 0, s_a] * P_c.val⁻¹) := by
  set x := P.val 0 0
  set y := P.val 0 1
  set z := P.val 1 0
  set w := P.val 1 1
  have h_P_val : P.val = !![x, y; z, w] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h_det : x * w - y * z = 1 := by
    have h := P.property
    rw [h_P_val] at h
    have h_det_val : (!![x, y; z, w] : Matrix (Fin 2) (Fin 2) ℂ).det = x * w - y * z := by
      calc (!![x, y; z, w] : Matrix (Fin 2) (Fin 2) ℂ).det = !![x, y; z, w] 0 0 * !![x, y; z, w] 1 1 - !![x, y; z, w] 0 1 * !![x, y; z, w] 1 0 := by
            simp [Matrix.det_fin_two]
        _ = x * w - y * z := by rw [h00, h01, h10, h11]
    rwa [h_det_val] at h
  by_cases hz : z = 0
  · by_cases h_eq : x = w
    · right
      have hx2 : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := by ring
          _ = x * w := by rw [← h_eq]
          _ = x * w - y * 0 := by ring
          _ = x * w - y * z := by rw [hz]
          _ = 1 := h_det
      have hs : x = 1 ∨ x = -1 := by
        have h1 : x ^ 2 - 1 = 0 := by rw [hx2, sub_self]
        have h2 : (x - 1) * (x + 1) = 0 := by
          calc (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
            _ = 0 := h1
        cases mul_eq_zero.mp h2 with
        | inl h3 => left; exact sub_eq_zero.mp h3
        | inr h4 => right; exact eq_neg_iff_add_eq_zero.mpr h4
      use 1, y, x, hs
      have hone : (1 : SpecialLinearGroup (Fin 2) ℂ).val = 1 := rfl
      have hinv : (1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = 1 := by simp
      rw [h_P_val, hz, h_eq, hone, hinv, Matrix.mul_one, Matrix.one_mul]
    · left
      have hd : x * w = 1 := by
        calc x * w = x * w - y * 0 := by ring
          _ = x * w - y * z := by rw [hz]
          _ = 1 := h_det
      obtain ⟨P_c, c, hc, h_decomp⟩ := sl2c_jordan_decomp_proof_case2 x y w hd h_eq
      use P_c, c, hc
      rw [h_P_val, hz]
      exact h_decomp
  · by_cases h_tr : (x + w) ^ 2 = 4
    · right
      obtain ⟨P_c, a, s_a, h_s, h_decomp⟩ := sl2c_jordan_decomp_proof_case3 x y z w h_det hz h_tr
      use P_c, a, s_a, h_s
      rw [h_P_val]
      exact h_decomp
    · left
      obtain ⟨P_c, c, hc, h_decomp⟩ := sl2c_jordan_decomp_proof_case1 x y z w h_det hz h_tr
      use P_c, c, hc
      rw [h_P_val]
      exact h_decomp

lemma M_eq_explicit_diag (P P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0)
    (hP_eq : P = P_c * (diag_matrix c hc) * P_c⁻¹)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ))) :
    ∃ M : RealLorentzLieAlgebra,
      spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M ∧
      M.val = 2 • (L * M_D c * L_inv) := by
  have h_exp_d : (spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ))) := by
    ext i j
    fin_cases i <;> fin_cases j
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 0 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 0 0; exact spinorPhi_S_matrix_to_M_diag_eq_0_0 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 0 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 0 1; exact spinorPhi_S_matrix_to_M_diag_eq_0_1 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 0 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 0 2; exact spinorPhi_S_matrix_to_M_diag_eq_0_2 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 0 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 0 3; exact spinorPhi_S_matrix_to_M_diag_eq_0_3 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 1 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 1 0; exact spinorPhi_S_matrix_to_M_diag_eq_1_0 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 1 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 1 1; exact spinorPhi_S_matrix_to_M_diag_eq_1_1 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 1 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 1 2; exact spinorPhi_S_matrix_to_M_diag_eq_1_2 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 1 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 1 3; exact spinorPhi_S_matrix_to_M_diag_eq_1_3 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 2 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 2 0; exact spinorPhi_S_matrix_to_M_diag_eq_2_0 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 2 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 2 1; exact spinorPhi_S_matrix_to_M_diag_eq_2_1 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 2 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 2 2; exact spinorPhi_S_matrix_to_M_diag_eq_2_2 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 2 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 2 3; exact spinorPhi_S_matrix_to_M_diag_eq_2_3 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 3 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 3 0; exact spinorPhi_S_matrix_to_M_diag_eq_3_0 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 3 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 3 1; exact spinorPhi_S_matrix_to_M_diag_eq_3_1 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 3 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 3 2; exact spinorPhi_S_matrix_to_M_diag_eq_3_2 c hc
    · change ((spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val) 3 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ)))) 3 3; exact spinorPhi_S_matrix_to_M_diag_eq_3_3 c hc
  have h_lorentz := M_D_lorentz c
  have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P_c L hL L_inv hL_inv
  have hL_lorentz := spinorPhi_S_matrix_to_M_aux_b P_c L hL
  have hM_lorentz := spinorPhi_S_matrix_to_M_aux_d (M_D c) L L_inv hL_lorentz h_L_inv_eq.1 h_L_inv_eq.2 h_lorentz
  have hM_lorentz2 : (2 • (L * M_D c * L_inv))ᵀ * minkowskiMetricReal + minkowskiMetricReal * (2 • (L * M_D c * L_inv)) = 0 := by
    rw [Matrix.transpose_smul]
    have h1 : (2 • (L * M_D c * L_inv)ᵀ) * minkowskiMetricReal = 2 • ((L * M_D c * L_inv)ᵀ * minkowskiMetricReal) := Matrix.smul_mul 2 _ _
    have h2 : minkowskiMetricReal * (2 • (L * M_D c * L_inv)) = 2 • (minkowskiMetricReal * (L * M_D c * L_inv)) := Matrix.mul_smul _ 2 _
    rw [h1, h2, ← smul_add, hM_lorentz, smul_zero]
  let M : RealLorentzLieAlgebra := ⟨2 • (L * M_D c * L_inv), hM_lorentz2⟩
  use M
  constructor
  · have h_e := spinorPhi_S_matrix_to_M_aux_e P P_c (diag_matrix c hc) hP_eq
    ext i j
    have h_val : ((exp_iM M).val.val) = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_D c * L_inv) (fun x => (x : ℂ)))) := by
      change NormedSpace.exp (I • real_matrix_to_complex M.val) = _
      have hM_val : M.val = 2 • (L * M_D c * L_inv) := rfl
      rw [hM_val]
      have h_eq : I • real_matrix_to_complex (2 • (L * M_D c * L_inv)) = ((2 * Complex.I) : ℂ) • Matrix.map (L * M_D c * L_inv) (fun x => (x : ℂ)) := by
        ext k l
        simp only [real_matrix_to_complex, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
        push_cast
        ring
      rw [h_eq]
    have h_val_ij : ((exp_iM M).val.val) i j = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_D c * L_inv) (fun x => (x : ℂ)))) i j := by rw [h_val]
    rw [h_val_ij]
    have h_symm := exp_conj_complex L (M_D c) L_inv h_L_inv_eq.1 h_L_inv_eq.2
    have h_symm_val : (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_D c * L_inv) (fun x => (x : ℂ)))) i j =
        (Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D c) (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ))) i j := by
      rw [h_symm]
    rw [h_symm_val]
    have h_e_val : ((spinorPhi (P, (sl2c_conj P)⁻¹)).val.val) i j = ((spinorPhi (P_c, sl2c_conj P_c)).val.val * (spinorPhi (diag_matrix c hc, (sl2c_conj (diag_matrix c hc))⁻¹)).val.val * (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val) i j := by rw [h_e]
    rw [h_e_val, hL, hL_inv, h_exp_d]
  · rfl

lemma M_eq_explicit_jordan (P P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (s_a : ℂ) (h_s : s_a = 1 ∨ s_a = -1)
    (hP_eq : P = P_c * (diag_matrix s_a (by rcases h_s with h | h <;> simp [h]) * jordan_matrix (s_a * a)) * P_c⁻¹)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ))) :
    ∃ M : RealLorentzLieAlgebra,
      spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M ∧
      M.val = 2 • (L * M_J (s_a * a) * L_inv) := by
  have h_exp_j : (spinorPhi (diag_matrix s_a (by rcases h_s with h | h <;> simp [h]) * jordan_matrix (s_a * a), (sl2c_conj (diag_matrix s_a (by rcases h_s with h | h <;> simp [h]) * jordan_matrix (s_a * a)))⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s_a * a)) (fun x => (x : ℂ))) := by
    have h_g := spinorPhi_S_matrix_to_M_aux_g s_a h_s (s_a * a)
    have h_jordan_exp : (spinorPhi (jordan_matrix (s_a * a), (sl2c_conj (jordan_matrix (s_a * a)))⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s_a * a)) (fun x => (x : ℂ))) := by
      have h_nilp : (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s_a * a)) (fun x => (x : ℂ))) ^ 3 = 0 := N_mat_nilpotent (s_a * a)
      rw [exp_of_nilpotent3 _ h_nilp]
      have h_pow2 : (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s_a * a)) (fun x => (x : ℂ))) ^ 2 = N_mat (s_a * a) * N_mat (s_a * a) := by
        change N_mat (s_a * a) ^ 2 = N_mat (s_a * a) * N_mat (s_a * a)
        rw [pow_two]
      rw [h_pow2]
      exact spinorPhi_S_matrix_to_M_jordan_eq (s_a * a)
    rw [h_g, h_jordan_exp]
  have h_lorentz := M_J_lorentz (s_a * a)
  have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P_c L hL L_inv hL_inv
  have hL_lorentz := spinorPhi_S_matrix_to_M_aux_b P_c L hL
  have hM_lorentz := spinorPhi_S_matrix_to_M_aux_d (M_J (s_a * a)) L L_inv hL_lorentz h_L_inv_eq.1 h_L_inv_eq.2 h_lorentz
  have hM_lorentz2 : (2 • (L * M_J (s_a * a) * L_inv))ᵀ * minkowskiMetricReal + minkowskiMetricReal * (2 • (L * M_J (s_a * a) * L_inv)) = 0 := by
    rw [Matrix.transpose_smul]
    have h1 : (2 • (L * M_J (s_a * a) * L_inv)ᵀ) * minkowskiMetricReal = 2 • ((L * M_J (s_a * a) * L_inv)ᵀ * minkowskiMetricReal) := Matrix.smul_mul 2 _ _
    have h2 : minkowskiMetricReal * (2 • (L * M_J (s_a * a) * L_inv)) = 2 • (minkowskiMetricReal * (L * M_J (s_a * a) * L_inv)) := Matrix.mul_smul _ 2 _
    rw [h1, h2, ← smul_add, hM_lorentz, smul_zero]
  let M : RealLorentzLieAlgebra := ⟨2 • (L * M_J (s_a * a) * L_inv), hM_lorentz2⟩
  use M
  constructor
  · have h_prf : (s_a ≠ 0) := by rcases h_s with h | h <;> simp [h]
    have h_e := spinorPhi_S_matrix_to_M_aux_e P P_c (diag_matrix s_a h_prf * jordan_matrix (s_a * a)) hP_eq
    ext i j
    have h_val : ((exp_iM M).val.val) = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_J (s_a * a) * L_inv) (fun x => (x : ℂ)))) := by
      change NormedSpace.exp (I • real_matrix_to_complex M.val) = _
      have hM_val : M.val = 2 • (L * M_J (s_a * a) * L_inv) := rfl
      rw [hM_val]
      have h_eq : I • real_matrix_to_complex (2 • (L * M_J (s_a * a) * L_inv)) = ((2 * Complex.I) : ℂ) • Matrix.map (L * M_J (s_a * a) * L_inv) (fun x => (x : ℂ)) := by
        ext k l
        simp only [real_matrix_to_complex, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
        push_cast
        ring
      rw [h_eq]
    have h_val_ij : ((exp_iM M).val.val) i j = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_J (s_a * a) * L_inv) (fun x => (x : ℂ)))) i j := by rw [h_val]
    rw [h_val_ij]
    have h_symm := exp_conj_complex L (M_J (s_a * a)) L_inv h_L_inv_eq.1 h_L_inv_eq.2
    have h_symm_val : (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M_J (s_a * a) * L_inv) (fun x => (x : ℂ)))) i j =
        (Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s_a * a)) (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ))) i j := by
      rw [h_symm]
    rw [h_symm_val]
    have h_e_val : ((spinorPhi (P, (sl2c_conj P)⁻¹)).val.val) i j = ((spinorPhi (P_c, sl2c_conj P_c)).val.val * (spinorPhi (diag_matrix s_a h_prf * jordan_matrix (s_a * a), (sl2c_conj (diag_matrix s_a h_prf * jordan_matrix (s_a * a)))⁻¹)).val.val * (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val) i j := by rw [h_e]
    rw [h_e_val, hL, hL_inv, h_exp_j]
  · rfl


lemma action_eq (A B : SpecialLinearGroup (Fin 2) ℂ) (z : Fin 4 → ℂ) :
    vec_to_spinor ((spinorPhi (A, B)) • z) = A.val * vec_to_spinor z * B.valᵀ := by
  change vec_to_spinor ((spinorPhi (A, B)).val.val.mulVec z) = A.val * vec_to_spinor z * B.valᵀ
  have h1 : (spinorPhi (A, B)).val.val = spinorPhi_matrix A B := rfl
  rw [h1]
  rw [spinorPhi_matrix_mulVec]
  dsimp [spinor_action]
  rw [vec_to_spinor_right_inv]

lemma im_part_commutes (P : Matrix (Fin 2) (Fin 2) ℂ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    (P * W * Pᴴ - (P * W * Pᴴ)ᴴ) = P * (W - Wᴴ) * Pᴴ := by
  have h_conj : (P * W * Pᴴ)ᴴ = P * Wᴴ * Pᴴ := by
    calc (P * W * Pᴴ)ᴴ = (Pᴴ)ᴴ * (P * W)ᴴ := conjTranspose_mul (P * W) Pᴴ
      _ = P * (P * W)ᴴ := by rw [conjTranspose_conjTranspose P]
      _ = P * (Wᴴ * Pᴴ) := by rw [conjTranspose_mul P W]
      _ = P * Wᴴ * Pᴴ := by rw [Matrix.mul_assoc]
  rw [h_conj]
  calc P * W * Pᴴ - P * Wᴴ * Pᴴ = (P * W - P * Wᴴ) * Pᴴ := by rw [Matrix.sub_mul]
    _ = P * (W - Wᴴ) * Pᴴ := by rw [Matrix.mul_sub]

lemma vec_to_spinor_im (z : Fin 4 → ℂ) :
    vec_to_spinor (fun k => -(z k).im : Fin 4 → ℂ) = (I / 2) • (vec_to_spinor z - (vec_to_spinor z)ᴴ) := by
  ext i j
  have hI2 : I / 2 = (1 / 2 : ℂ) * I := by ring
  fin_cases i <;> fin_cases j
  · simp [conjTranspose_apply, smul_eq_mul, hI2]
    apply Complex.ext <;> simp <;> ring
  · simp [conjTranspose_apply, smul_eq_mul, hI2]
    apply Complex.ext <;> simp <;> ring
  · simp [conjTranspose_apply, smul_eq_mul, hI2]
    apply Complex.ext <;> simp <;> ring
  · simp [conjTranspose_apply, smul_eq_mul, hI2]
    apply Complex.ext <;> simp <;> ring

lemma c_s_diag_mul_star_neg (c : ℂ) (s : ℝ) :
  c_s_diag c s * star (c_s_diag c (-s)) = Real.cos (2 * s * (Complex.log c).im) + I * Real.sin (2 * s * (Complex.log c).im) := by
  dsimp [c_s_diag]
  have h_conj : (starRingEnd ℂ) (cexp (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im))) = cexp (star (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im))) := by
    exact Eq.symm (Complex.exp_conj _)
  rw [h_conj, ←Complex.exp_add]
  have h1 : s * (log c).re + I * (s * (log c).im) + star (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im)) = (2 * s * (log c).im) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [h1, exp_mul_I]
  apply Complex.ext <;> simp

lemma c_s_diag_mul_star_pos (c : ℂ) (s : ℝ) :
  c_s_diag c s * star (c_s_diag c s) = Real.exp (2 * s * (Complex.log c).re) := by
  dsimp [c_s_diag]
  have h_conj : (starRingEnd ℂ) (cexp (↑s * ↑(log c).re + I * (↑s * ↑(log c).im))) = cexp (star (↑s * ↑(log c).re + I * (↑s * ↑(log c).im))) := by
    exact Eq.symm (Complex.exp_conj _)
  rw [h_conj, ←Complex.exp_add]
  have h1 : s * (log c).re + I * (s * (log c).im) + star (↑s * ↑(log c).re + I * (↑s * ↑(log c).im)) = 2 * s * (log c).re := by
    apply Complex.ext <;> simp <;> ring
  rw [h1]
  have h2 : (2 * ↑s * ↑(log c).re : ℂ) = ↑(2 * s * (log c).re : ℝ) := by
    push_cast; ring
  rw [h2, ←Complex.ofReal_exp]

lemma c_s_diag_neg_mul_star_neg (c : ℂ) (s : ℝ) :
  c_s_diag c (-s) * star (c_s_diag c (-s)) = Real.exp (-2 * s * (Complex.log c).re) := by
  dsimp [c_s_diag]
  have h_conj : (starRingEnd ℂ) (cexp (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im))) = cexp (star (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im))) := by
    exact Eq.symm (Complex.exp_conj _)
  rw [h_conj, ←Complex.exp_add]
  have h1 : ↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im) + star (↑(-s) * ↑(log c).re + I * (↑(-s) * ↑(log c).im)) = -2 * s * (log c).re := by
    apply Complex.ext <;> simp <;> ring
  rw [h1]
  have h2 : (-2 * ↑s * ↑(log c).re : ℂ) = ↑(-2 * s * (log c).re : ℝ) := by
    push_cast; ring
  rw [h2, ←Complex.ofReal_exp]

lemma spinorPhi_matrix_action (A B : SpecialLinearGroup (Fin 2) ℂ) (z : Fin 4 → ℂ) :
  vec_to_spinor (mulVec (spinorPhi_matrix A B) z) = A.val * vec_to_spinor z * B.valᵀ := by
  have h1 : mulVec (spinorPhi_matrix A B) z = spinor_action A.val B.val z := spinorPhi_matrix_mulVec A B z
  rw [h1]
  dsimp [spinor_action]
  rw [vec_to_spinor_right_inv]

lemma Z_H_eq (Z_re Z_im : Matrix (Fin 2) (Fin 2) ℂ) (hX : Z_re.IsHermitian) (hY : Z_im.IsHermitian) :
  (-Z_re - I • Z_im)ᴴ = -Z_re + I • Z_im := by
  rw [conjTranspose_sub, conjTranspose_neg, conjTranspose_smul]
  have hX_eq : Z_reᴴ = Z_re := hX
  have hY_eq : Z_imᴴ = Z_im := hY
  rw [hX_eq, hY_eq, star_def, conj_I]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma diag_matrix_inv_val (a : ℂ) (ha : a ≠ 0) :
  (diag_matrix a ha)⁻¹.val = ![![a⁻¹, 0], ![0, a]] := by
  have h_val : (diag_matrix a ha)⁻¹.val = adjugate (diag_matrix a ha).val := rfl
  rw [h_val, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    dsimp [diag_matrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    try simp only [neg_zero]
    try rfl
  }

lemma diag_inner_gen (R : ℝ) (hR : R ≠ 0) (E : ℂ) (hE : E ≠ 0) (hEs : (starRingEnd ℂ) E = E⁻¹)
    (hd : (R : ℂ) * E ≠ 0) (Z_re Z_im : Matrix (Fin 2) (Fin 2) ℂ) :
    (I / 2) • ((diag_matrix ((R:ℂ) * E) hd).val * (-Z_re - I • Z_im) * (diag_matrix ((R:ℂ) * E) hd)⁻¹.valᴴ
      - (diag_matrix ((R:ℂ) * E) hd)⁻¹.val * (-Z_re + I • Z_im) * (diag_matrix ((R:ℂ) * E) hd).valᴴ) =
    !![ ((E^2 + (E^2)⁻¹)/2) * Z_im 0 0 + ((E^2 - (E^2)⁻¹) / (2*I)) * Z_re 0 0,
        (((R:ℂ)^2 + ((R:ℂ)^2)⁻¹)/2) * Z_im 0 1 - I * (((R:ℂ)^2 - ((R:ℂ)^2)⁻¹)/2) * Z_re 0 1;
        (((R:ℂ)^2 + ((R:ℂ)^2)⁻¹)/2) * Z_im 1 0 + I * (((R:ℂ)^2 - ((R:ℂ)^2)⁻¹)/2) * Z_re 1 0,
        ((E^2 + (E^2)⁻¹)/2) * Z_im 1 1 - ((E^2 - (E^2)⁻¹) / (2*I)) * Z_re 1 1 ] := by
  have hRc : (starRingEnd ℂ) (R:ℂ) = R := Complex.conj_ofReal R
  have hRne : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have hI : (I:ℂ) ≠ 0 := Complex.I_ne_zero
  have hD : (diag_matrix ((R:ℂ) * E) hd).val = Matrix.diagonal ![(R:ℂ) * E, ((R:ℂ) * E)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag_matrix]
  have hDi : (diag_matrix ((R:ℂ) * E) hd)⁻¹.val = Matrix.diagonal ![((R:ℂ) * E)⁻¹, (R:ℂ) * E] := by
    rw [diag_matrix_inv_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hEs' : star E = E⁻¹ := hEs
  have hs1 : star ((R:ℂ) * E) = (R:ℂ) * E⁻¹ := by
    simp [hEs, hRc]
  have hs2 : star (((R:ℂ) * E)⁻¹) = ((R:ℂ) * E⁻¹)⁻¹ := by
    simp [hEs, hRc]
  rw [hD, hDi, Matrix.diagonal_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hs1, hEs']
    field_simp
    ring_nf
    try simp [Complex.I_sq]
    try ring_nf


noncomputable def diagR (c : ℂ) (s : ℝ) : ℝ := Real.exp (s * (Complex.log c).re)


noncomputable def diagE (c : ℂ) (s : ℝ) : ℂ := Complex.exp (((s * (Complex.log c).im : ℝ) : ℂ) * I)

lemma diagR_ne_zero (c : ℂ) (s : ℝ) : diagR c s ≠ 0 := (Real.exp_pos _).ne'

lemma diagE_ne_zero (c : ℂ) (s : ℝ) : diagE c s ≠ 0 := Complex.exp_ne_zero _

lemma diagE_conj (c : ℂ) (s : ℝ) : (starRingEnd ℂ) (diagE c s) = (diagE c s)⁻¹ := by
  unfold diagE
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

lemma c_s_diag_eq_diagR_mul (c : ℂ) (s : ℝ) : c_s_diag c s = (diagR c s : ℂ) * diagE c s := by
  unfold c_s_diag diagR diagE
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma diagE_sq (c : ℂ) (s : ℝ) :
    diagE c s ^ 2 = Complex.exp (((2 * s * (Complex.log c).im : ℝ) : ℂ) * I) := by
  unfold diagE
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma diagR_sq (c : ℂ) (s : ℝ) :
    (diagR c s : ℂ) ^ 2 = Complex.exp (((2 * s * (Complex.log c).re : ℝ) : ℂ)) := by
  unfold diagR
  rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma exp_neg_mul_I_eq_inv (θ : ℝ) :
    Complex.exp (-(θ : ℂ) * I) = (Complex.exp ((θ : ℂ) * I))⁻¹ := by
  rw [← Complex.exp_neg]
  congr 1
  ring

lemma sin_form_aux (a b : ℂ) : (b - a) * I / 2 = (a - b) / (2 * I) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination (b - a) * Complex.I_sq

lemma ofReal_cos_exp (θ : ℝ) :
    (Real.cos θ : ℂ) = (Complex.exp ((θ : ℂ) * I) + (Complex.exp ((θ : ℂ) * I))⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, exp_neg_mul_I_eq_inv]

lemma ofReal_sin_exp (θ : ℝ) :
    (Real.sin θ : ℂ) = (Complex.exp ((θ : ℂ) * I) - (Complex.exp ((θ : ℂ) * I))⁻¹) / (2 * I) := by
  rw [Complex.ofReal_sin, Complex.sin, exp_neg_mul_I_eq_inv, sin_form_aux]

lemma ofReal_cosh_exp (t : ℝ) :
    (Real.cosh t : ℂ) = (Complex.exp (t : ℂ) + (Complex.exp (t : ℂ))⁻¹) / 2 := by
  rw [Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]

lemma ofReal_sinh_exp (t : ℝ) :
    (Real.sinh t : ℂ) = (Complex.exp (t : ℂ) - (Complex.exp (t : ℂ))⁻¹) / 2 := by
  rw [Complex.ofReal_sinh, Complex.sinh, Complex.exp_neg]

lemma diag_cos_eq (c : ℂ) (s : ℝ) :
    (Real.cos (2 * s * (Complex.log c).im) : ℂ) = (diagE c s ^ 2 + (diagE c s ^ 2)⁻¹) / 2 := by
  rw [diagE_sq]; exact ofReal_cos_exp _

lemma diag_sin_eq (c : ℂ) (s : ℝ) :
    (Real.sin (2 * s * (Complex.log c).im) : ℂ) = (diagE c s ^ 2 - (diagE c s ^ 2)⁻¹) / (2 * I) := by
  rw [diagE_sq]; exact ofReal_sin_exp _

lemma diag_cosh_eq (c : ℂ) (s : ℝ) :
    (Real.cosh (2 * s * (Complex.log c).re) : ℂ) =
      ((diagR c s : ℂ) ^ 2 + ((diagR c s : ℂ) ^ 2)⁻¹) / 2 := by
  rw [diagR_sq]; exact ofReal_cosh_exp _

lemma diag_sinh_eq (c : ℂ) (s : ℝ) :
    (Real.sinh (2 * s * (Complex.log c).re) : ℂ) =
      ((diagR c s : ℂ) ^ 2 - ((diagR c s : ℂ) ^ 2)⁻¹) / 2 := by
  rw [diagR_sq]; exact ofReal_sinh_exp _

lemma diag_c_action_inner (c : ℂ) (hc : c ≠ 0) (s : ℝ) (Z_re Z_im : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : Z_re.IsHermitian) (hY : Z_im.IsHermitian) :
    let D := diag_matrix (c_s_diag c s) (c_s_diag_ne_zero c s)
    let Z := -Z_re - I • Z_im
    (I / 2) • (D.val * Z * D⁻¹.valᴴ - D⁻¹.val * Zᴴ * D.valᴴ) = tube_F_diag_c c Z_re Z_im s := by
  intro D Z
  have hRE : (diagR c s : ℂ) * diagE c s ≠ 0 :=
    mul_ne_zero (by exact_mod_cast diagR_ne_zero c s) (diagE_ne_zero c s)
  have hDe : D = diag_matrix ((diagR c s : ℂ) * diagE c s) hRE := by
    have h : ∀ (a : ℂ) (h1 : a ≠ 0) (b : ℂ) (h2 : b ≠ 0), a = b →
        diag_matrix a h1 = diag_matrix b h2 := by
      intro a h1 b h2 h
      subst h
      rfl
    exact h _ _ _ _ (c_s_diag_eq_diagR_mul c s)
  have hZ : Zᴴ = -Z_re + I • Z_im := Z_H_eq Z_re Z_im hX hY
  have hZ' : Z = -Z_re - I • Z_im := rfl
  rw [hZ, hZ', hDe, diag_inner_gen (diagR c s) (diagR_ne_zero c s) (diagE c s) (diagE_ne_zero c s)
    (diagE_conj c s) hRE Z_re Z_im]
  simp only [tube_F_diag_c]
  rw [diag_cos_eq, diag_sin_eq, diag_cosh_eq, diag_sinh_eq]

lemma A_Z_A_H_eq (P_c D : SpecialLinearGroup (Fin 2) ℂ) (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    let A := P_c * D * P_c⁻¹
    A.val * Z * A⁻¹.valᴴ = P_c.val * (D.val * (P_c⁻¹.val * Z * P_c⁻¹.valᴴ) * D⁻¹.valᴴ) * P_c.valᴴ := by
  intros A
  change (P_c * D * P_c⁻¹).val * Z * (P_c * D * P_c⁻¹)⁻¹.valᴴ = _
  have h_inv : (P_c * D * P_c⁻¹)⁻¹.val = P_c.val * D⁻¹.val * P_c⁻¹.val := by
    have h1 : (P_c * D * P_c⁻¹)⁻¹ = P_c * D⁻¹ * P_c⁻¹ := by group
    rw [h1]
    rfl
  rw [h_inv]
  have h_A_val : (P_c * D * P_c⁻¹).val = P_c.val * D.val * P_c⁻¹.val := rfl
  rw [h_A_val]
  have h_H : (P_c.val * D⁻¹.val * P_c⁻¹.val)ᴴ = P_c⁻¹.valᴴ * D⁻¹.valᴴ * P_c.valᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h_H]
  simp only [Matrix.mul_assoc]

lemma exp_iM_sM_eq (M : RealLorentzLieAlgebra) (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_D c * L_inv)) (s : ℝ) :
    ((exp_iM (s • M)).val.val) = Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D c) (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ)) := by
  have h_val : ((exp_iM (s • M)).val.val) = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * (s • M_D c) * L_inv) (fun x => (x : ℂ)))) := by
    change NormedSpace.exp (I • real_matrix_to_complex (s • M).val) = _
    have hM_s_val : (s • M).val = s • (2 • (L * M_D c * L_inv)) := by
      simp [hM_eq]
    rw [hM_s_val]
    have h_smul : L * (s • M_D c) * L_inv = s • (L * M_D c * L_inv) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h_smul]
    have h_eq : I • real_matrix_to_complex (s • (2 • (L * M_D c * L_inv))) = ((2 * Complex.I) : ℂ) • Matrix.map (s • (L * M_D c * L_inv)) (fun x => (x : ℂ)) := by
      ext k l
      simp only [real_matrix_to_complex, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      push_cast
      ring
    rw [h_eq]
  rw [h_val]
  have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P_c L hL L_inv hL_inv
  have h_symm := exp_conj_complex L (s • M_D c) L_inv h_L_inv_eq.1 h_L_inv_eq.2
  exact h_symm

lemma sl2c_conj_inv_transpose (A : SpecialLinearGroup (Fin 2) ℂ) :
  ((sl2c_conj A)⁻¹).valᵀ = (A⁻¹.val)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp [sl2c_conj, adjugate_fin_two, conjTranspose_apply, Matrix.map_apply]
  }

lemma exp_iM_sM_spinorPhi (M : RealLorentzLieAlgebra) (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_D c * L_inv)) (s : ℝ) :
    let D_s := diag_matrix (c_s_diag c s) (c_s_diag_ne_zero c s)
    let A_s := P_c * D_s * P_c⁻¹
    ((exp_iM (s • M)).val.val) = (spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val := by
  intros D_s A_s
  have h_exp := exp_iM_sM_eq M P_c c hc L L_inv hL hL_inv hM_eq s
  rw [h_exp]
  have h_Ds := spinorPhi_S_matrix_to_M_diag_s c hc s
  have h_mul1 : spinorPhi (P_c * D_s * P_c⁻¹, (sl2c_conj (P_c * D_s * P_c⁻¹))⁻¹) =
    spinorPhi (P_c, sl2c_conj P_c) * spinorPhi (D_s, (sl2c_conj D_s)⁻¹) * spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹) := by
    have h_conj : sl2c_conj (P_c * D_s * P_c⁻¹) = sl2c_conj P_c * sl2c_conj D_s * sl2c_conj P_c⁻¹ := by
      rw [sl2c_conj_mul, sl2c_conj_mul]
    rw [h_conj]
    have h_inv1 : (sl2c_conj P_c * sl2c_conj D_s * sl2c_conj P_c⁻¹)⁻¹ = (sl2c_conj P_c⁻¹)⁻¹ * (sl2c_conj D_s)⁻¹ * (sl2c_conj P_c)⁻¹ := by
      group
    rw [h_inv1]
    have h_inv_P : (sl2c_conj P_c⁻¹)⁻¹ = sl2c_conj P_c := by
      rw [sl2c_conj_inv, inv_inv]
    rw [h_inv_P]
    have h_inv_P2 : (sl2c_conj P_c)⁻¹ = sl2c_conj P_c⁻¹ := by
      rw [sl2c_conj_inv]
    rw [h_inv_P2]
    have h_eq_pair : (P_c * D_s * P_c⁻¹, sl2c_conj P_c * (sl2c_conj D_s)⁻¹ * sl2c_conj P_c⁻¹) =
                     (P_c, sl2c_conj P_c) * (D_s, (sl2c_conj D_s)⁻¹) * (P_c⁻¹, sl2c_conj P_c⁻¹) := by
      ext
      · simp [mul_assoc]
      · simp [mul_assoc]
    rw [h_eq_pair]
    rw [map_mul, map_mul]
  have h_val_mul : (spinorPhi (P_c * D_s * P_c⁻¹, (sl2c_conj (P_c * D_s * P_c⁻¹))⁻¹)).val.val =
    (spinorPhi (P_c, sl2c_conj P_c)).val.val * (spinorPhi (D_s, (sl2c_conj D_s)⁻¹)).val.val * (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val := by
    rw [h_mul1]
    rfl
  change _ = (spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val
  have h_A_s_def : A_s = P_c * D_s * P_c⁻¹ := rfl
  rw [h_A_s_def]
  rw [h_val_mul]
  rw [hL, hL_inv]
  rw [h_Ds]

lemma Z_re_im_eq_vec_to_spinor (z : Fin 4 → ℂ) :
  -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := by
  ext i j
  dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
  fin_cases i <;> fin_cases j <;> {
    simp only
    apply Complex.ext
    · simp only [add_re, add_im, sub_re, neg_re, neg_im, mul_re, mul_im, I_re, I_im, zero_re, zero_im, one_re, one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · simp only [add_re, add_im, sub_im, neg_re, neg_im, mul_re, mul_im, I_re, I_im, zero_re, zero_im, one_re, one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  }

lemma matrix_factor_action (P : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
  (I / 2) • (P * M * Pᴴ - (P * M * Pᴴ)ᴴ) = P * ((I / 2) • (M - Mᴴ)) * Pᴴ := by
  ext i j
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, conjTranspose_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

lemma exp_iM_action_eq_tube_F_diag_c (M : RealLorentzLieAlgebra) (P P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0)
    (hM : spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M)
    (hP_eq : P.val = P_c.val * (diag_matrix c hc).val * P_c.val⁻¹)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_D c * L_inv))
    (z : Fin 4 → ℂ) (hz_pos : (vec_to_spinor (fun k => -(z k).im)).PosDef) (s : ℝ) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ,
      X.IsHermitian ∧ Y.PosDef ∧
      (vec_to_spinor (fun k => -((exp_iM (s • M) • z) k).im : Fin 4 → ℂ)) = P_c.val * tube_F_diag_c c X Y s * P_c.valᴴ ∧
      (vec_to_spinor (fun k => -(z k).im : Fin 4 → ℂ)) = P_c.val * tube_F_diag_c c X Y 0 * P_c.valᴴ ∧
      (vec_to_spinor (fun k => -((exp_iM M • z) k).im : Fin 4 → ℂ)) = P_c.val * tube_F_diag_c c X Y 1 * P_c.valᴴ := by
    let Z_re := vec_to_spinor (fun k => -(z k).re)
    let Z_im := vec_to_spinor (fun k => -(z k).im)
    let X := P_c⁻¹.val * Z_re * P_c⁻¹.valᴴ
    let Y := P_c⁻¹.val * Z_im * P_c⁻¹.valᴴ
    use X, Y
    have hZ_re_herm : Z_re.IsHermitian := by
      dsimp [Z_re]
      have h_eq : (fun k => -((z k).re : ℂ)) = (fun k => ((-(z k).re : ℝ) : ℂ)) := by
        ext k
        push_cast
        rfl
      rw [h_eq]
      rw [vec_to_spinor_eq_matrix]
      exact isHerm_two_by_two (-(z 0).re + -(z 3).re) (-(z 0).re - -(z 3).re) (((-(z 1).re : ℝ) : ℂ) - ((-(z 2).re : ℝ) : ℂ) * I)
    have hX_herm : X.IsHermitian := by
      dsimp [Matrix.IsHermitian, X]
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      have h : Z_reᴴ = Z_re := hZ_re_herm
      rw [h, Matrix.mul_assoc]
    have hY_pos : Y.PosDef := by
      dsimp [Y]
      have h_det : (P_c⁻¹.val).det ≠ 0 := by
        have h := P_c⁻¹.property
        rw [h]
        exact one_ne_zero
      exact posdef_congruence Z_im P_c⁻¹.val h_det hz_pos
    refine ⟨hX_herm, hY_pos, ?_, ?_, ?_⟩
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_s := diag_matrix (c_s_diag c s) (c_s_diag_ne_zero c s)
      let A_s := P_c * D_s * P_c⁻¹
      have h_exp := exp_iM_sM_spinorPhi M P_c c hc L L_inv hL hL_inv hM_eq s
      have h_action : (vec_to_spinor (fun k => -((exp_iM (s • M) • z) k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor (exp_iM (s • M) • z) - (vec_to_spinor (exp_iM (s • M) • z))ᴴ) := by
        exact vec_to_spinor_im (exp_iM (s • M) • z)
      rw [h_action]
      have h_mulvec : vec_to_spinor (exp_iM (s • M) • z) = vec_to_spinor (mulVec (spinorPhi_matrix A_s (sl2c_conj A_s)⁻¹) z) := by
        change vec_to_spinor (mulVec ((exp_iM (s • M)).val.val) z) = _
        rw [h_exp]
        rfl
      rw [h_mulvec]
      have h_spinor_action := spinorPhi_matrix_action A_s ((sl2c_conj A_s)⁻¹) z
      rw [h_spinor_action]
      have h_transpose : ((sl2c_conj A_s)⁻¹).valᵀ = (A_s⁻¹.val)ᴴ := sl2c_conj_inv_transpose A_s
      rw [h_transpose]
      have h_A_Z_A_H := A_Z_A_H_eq P_c D_s (vec_to_spinor z)
      have h_A_s_def : A_s = P_c * D_s * P_c⁻¹ := rfl
      rw [h_A_s_def, h_A_Z_A_H]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_s.val * (-X - I • Y) * D_s⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := diag_c_action_inner c hc s X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_s.val * (-X - I • Y) * D_s⁻¹.valᴴ)ᴴ = D_s⁻¹.val * (-X - I • Y)ᴴ * D_s.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_0 := diag_matrix (c_s_diag c 0) (c_s_diag_ne_zero c 0)
      have h_action_z : (vec_to_spinor (fun k => -(z k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor z - (vec_to_spinor z)ᴴ) := by
        exact vec_to_spinor_im z
      rw [h_action_z]
      have h_z_id : vec_to_spinor z = P_c.val * (D_0.val * (P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ) * D_0⁻¹.valᴴ) * P_c.valᴴ := by
        have h_D0_id : D_0.val = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> {
            simp [D_0, diag_matrix, c_s_diag, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
          }
        have h_D0_inv_id : D_0⁻¹.valᴴ = 1 := by
          have h_inv : D_0⁻¹.val = 1 := by
            have hD0 : D_0 = 1 := Subtype.ext h_D0_id
            rw [hD0, inv_one]
            rfl
          rw [h_inv]
          exact conjTranspose_one
        rw [h_D0_id, h_D0_inv_id]
        simp only [Matrix.mul_one, Matrix.one_mul]
        have h_Pc_inv : P_c.val * P_c⁻¹.val = 1 := by
          have h : P_c * P_c⁻¹ = 1 := mul_inv_cancel P_c
          have h2 : (P_c * P_c⁻¹).val = (1 : SpecialLinearGroup (Fin 2) ℂ).val := congrArg Subtype.val h
          exact h2
        have h_Pc_inv2 : P_c⁻¹.valᴴ * P_c.valᴴ = 1 := by
          calc
            P_c⁻¹.valᴴ * P_c.valᴴ = (P_c.val * P_c⁻¹.val)ᴴ := by rw [conjTranspose_mul]
            _ = (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [h_Pc_inv]
            _ = 1 := conjTranspose_one
        rw [←Matrix.mul_assoc P_c.val, ←Matrix.mul_assoc P_c.val]
        rw [h_Pc_inv]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
        rw [h_Pc_inv2, Matrix.mul_one]
      rw [h_z_id]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_0.val * (-X - I • Y) * D_0⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := diag_c_action_inner c hc 0 X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_0.val * (-X - I • Y) * D_0⁻¹.valᴴ)ᴴ = D_0⁻¹.val * (-X - I • Y)ᴴ * D_0.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_1 := diag_matrix (c_s_diag c 1) (c_s_diag_ne_zero c 1)
      let A_1 := P_c * D_1 * P_c⁻¹
      have h_exp := exp_iM_sM_spinorPhi M P_c c hc L L_inv hL hL_inv hM_eq 1
      have h_action : (vec_to_spinor (fun k => -((exp_iM M • z) k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor (exp_iM M • z) - (vec_to_spinor (exp_iM M • z))ᴴ) := by
        exact vec_to_spinor_im (exp_iM M • z)
      rw [h_action]
      have h_mulvec : vec_to_spinor (exp_iM M • z) = vec_to_spinor (mulVec (spinorPhi_matrix A_1 (sl2c_conj A_1)⁻¹) z) := by
        have h_1M : (1 : ℝ) • M = M := one_smul ℝ M
        have h_exp2 : (exp_iM M).val.val = (spinorPhi (A_1, (sl2c_conj A_1)⁻¹)).val.val := by
          calc (exp_iM M).val.val = (exp_iM ((1 : ℝ) • M)).val.val := by rw [h_1M]
               _ = (spinorPhi (A_1, (sl2c_conj A_1)⁻¹)).val.val := h_exp
        change vec_to_spinor (mulVec ((exp_iM M).val.val) z) = _
        rw [h_exp2]
        rfl
      rw [h_mulvec]
      have h_spinor_action := spinorPhi_matrix_action A_1 ((sl2c_conj A_1)⁻¹) z
      rw [h_spinor_action]
      have h_transpose : ((sl2c_conj A_1)⁻¹).valᵀ = (A_1⁻¹.val)ᴴ := sl2c_conj_inv_transpose A_1
      rw [h_transpose]
      have h_A_Z_A_H := A_Z_A_H_eq P_c D_1 (vec_to_spinor z)
      have h_A_1_def : A_1 = P_c * D_1 * P_c⁻¹ := rfl
      rw [h_A_1_def, h_A_Z_A_H]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_1.val * (-X - I • Y) * D_1⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := diag_c_action_inner c hc 1 X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_1.val * (-X - I • Y) * D_1⁻¹.valᴴ)ᴴ = D_1⁻¹.val * (-X - I • Y)ᴴ * D_1.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]

lemma jordan_matrix_inv_val (z : ℂ) : (jordan_matrix z)⁻¹.val = (jordan_matrix (-z)).val := by
  have h1 : (jordan_matrix z).val * (jordan_matrix (-z)).val = 1 := by
    ext i j
    dsimp [jordan_matrix, J_mat]
    fin_cases i <;> fin_cases j <;> {
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    }
  have h : jordan_matrix z * jordan_matrix (-z) = 1 := Subtype.ext h1
  exact congrArg Subtype.val (inv_eq_of_mul_eq_one_right h)

lemma jordan_inner_gen (t : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (I / 2) • (J_mat t * (-X - I • Y) * (J_mat (-t))ᴴ - J_mat (-t) * (-X + I • Y) * (J_mat t)ᴴ) =
    !![ Y 0 0 + I * (star t * X 0 1 - t * X 1 0) - (t * star t) * Y 1 1, Y 0 1 - I * t * X 1 1;
        Y 1 0 + I * star t * X 1 1, Y 1 1 ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Matrix.of_apply]
    simp [J_mat]
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma jordan_F00_herm (t : ℂ) (x01 x10 : ℂ) (h : x10 = star x01) :
    I * (star t * x01 - t * x10) = -2 * ((star t * x01).im : ℂ) := by
  subst h
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma jordan_normsq_cast (b : ℂ) (s : ℝ) :
    ((s * b) * star (s * b)) = (s:ℂ)^2 * ((‖b‖:ℝ):ℂ)^2 := by
  have h := Complex.mul_conj b
  rw [Complex.normSq_eq_norm_sq] at h
  push_cast at h
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  linear_combination (s:ℂ)^2 * h

lemma jordan_inner_eq_tube (b : ℂ) (s : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (I / 2) • (J_mat (s * b) * (-X - I • Y) * (J_mat (-(s * b)))ᴴ -
      J_mat (-(s * b)) * (-X - I • Y)ᴴ * (J_mat (s * b))ᴴ) = tube_F_jordan_c b X Y s := by
  have hZ : (-X - I • Y)ᴴ = -X + I • Y := by
    rw [conjTranspose_sub, conjTranspose_neg, conjTranspose_smul]
    have hX_eq : Xᴴ = X := hX
    have hY_eq : Yᴴ = Y := hY
    rw [hX_eq, hY_eq, star_def, conj_I]
    ext i j
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hZ, jordan_inner_gen]
  have hx10 : X 1 0 = star (X 0 1) := (congr_fun (congr_fun (show Xᴴ = X from hX) 1) 0).symm
  have h00 := jordan_F00_herm (s * b) (X 0 1) (X 1 0) hx10
  have hn := jordan_normsq_cast b s
  have him : (star ((s:ℂ) * b) * X 0 1).im = s * (star b * X 0 1).im := by
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [him] at h00
  rw [h00, hn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tube_F_jordan_c]
  all_goals ring

lemma jordan_c_action_inner (b : ℂ) (s : ℝ) (Z_re Z_im : Matrix (Fin 2) (Fin 2) ℂ)
  (h_re : Z_re.IsHermitian) (h_im : Z_im.IsHermitian) :
  let D := jordan_matrix (s * b)
  let Z := -Z_re - I • Z_im
  (I / 2) • (D.val * Z * D⁻¹.valᴴ - D⁻¹.val * Zᴴ * D.valᴴ) = tube_F_jordan_c b Z_re Z_im s := by
  intros D Z
  rw [jordan_matrix_inv_val]
  exact jordan_inner_eq_tube b s Z_re Z_im h_re h_im


lemma exp_iM_sM_eq_jordan (M : RealLorentzLieAlgebra) (P_c : SpecialLinearGroup (Fin 2) ℂ) (a s_a : ℂ)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_J (s_a * a) * L_inv)) (s : ℝ) :
    ((exp_iM (s • M)).val.val) = Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_J (s_a * a)) (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ)) := by
  have h_val : ((exp_iM (s • M)).val.val) = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * (s • M_J (s_a * a)) * L_inv) (fun x => (x : ℂ)))) := by
    change NormedSpace.exp (I • real_matrix_to_complex (s • M).val) = _
    have hM_s_val : (s • M).val = s • (2 • (L * M_J (s_a * a) * L_inv)) := by
      simp [hM_eq]
    rw [hM_s_val]
    have h_smul : L * (s • M_J (s_a * a)) * L_inv = s • (L * M_J (s_a * a) * L_inv) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h_smul]
    have h_eq : I • real_matrix_to_complex (s • (2 • (L * M_J (s_a * a) * L_inv))) = ((2 * Complex.I) : ℂ) • Matrix.map (s • (L * M_J (s_a * a) * L_inv)) (fun x => (x : ℂ)) := by
      ext k l
      simp only [real_matrix_to_complex, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      push_cast
      ring
    rw [h_eq]
  rw [h_val]
  have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P_c L hL L_inv hL_inv
  have h_symm := exp_conj_complex L (s • M_J (s_a * a)) L_inv h_L_inv_eq.1 h_L_inv_eq.2
  exact h_symm

lemma exp_iM_sM_spinorPhi_jordan (M : RealLorentzLieAlgebra) (P_c : SpecialLinearGroup (Fin 2) ℂ) (a s_a : ℂ)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_J (s_a * a) * L_inv)) (s : ℝ) :
    let D_s := jordan_matrix (s * (s_a * a))
    let A_s := P_c * D_s * P_c⁻¹
    ((exp_iM (s • M)).val.val) = (spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val := by
  intros D_s A_s
  have h_exp := exp_iM_sM_eq_jordan M P_c a s_a L L_inv hL hL_inv hM_eq s
  rw [h_exp]
  have h_Ds := spinorPhi_S_matrix_to_M_jordan_s_exact (s_a * a) s
  have h_mul1 : spinorPhi (P_c * D_s * P_c⁻¹, (sl2c_conj (P_c * D_s * P_c⁻¹))⁻¹) =
    spinorPhi (P_c, sl2c_conj P_c) * spinorPhi (D_s, (sl2c_conj D_s)⁻¹) * spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹) := by
    have h_conj : sl2c_conj (P_c * D_s * P_c⁻¹) = sl2c_conj P_c * sl2c_conj D_s * sl2c_conj P_c⁻¹ := by
      rw [sl2c_conj_mul, sl2c_conj_mul]
    rw [h_conj]
    have h_inv1 : (sl2c_conj P_c * sl2c_conj D_s * sl2c_conj P_c⁻¹)⁻¹ = (sl2c_conj P_c⁻¹)⁻¹ * (sl2c_conj D_s)⁻¹ * (sl2c_conj P_c)⁻¹ := by
      group
    rw [h_inv1]
    have h_inv_P : (sl2c_conj P_c⁻¹)⁻¹ = sl2c_conj P_c := by
      rw [sl2c_conj_inv, inv_inv]
    rw [h_inv_P]
    have h_inv_P2 : (sl2c_conj P_c)⁻¹ = sl2c_conj P_c⁻¹ := by
      rw [sl2c_conj_inv]
    rw [h_inv_P2]
    have h_eq_pair : (P_c * D_s * P_c⁻¹, sl2c_conj P_c * (sl2c_conj D_s)⁻¹ * sl2c_conj P_c⁻¹) =
                     (P_c, sl2c_conj P_c) * (D_s, (sl2c_conj D_s)⁻¹) * (P_c⁻¹, sl2c_conj P_c⁻¹) := by
      ext
      · simp [mul_assoc]
      · simp [mul_assoc]
    rw [h_eq_pair]
    rw [map_mul, map_mul]
  have h_val_mul : (spinorPhi (P_c * D_s * P_c⁻¹, (sl2c_conj (P_c * D_s * P_c⁻¹))⁻¹)).val.val =
    (spinorPhi (P_c, sl2c_conj P_c)).val.val * (spinorPhi (D_s, (sl2c_conj D_s)⁻¹)).val.val * (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val := by
    rw [h_mul1]
    rfl
  have h_step1 : Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_J (s_a * a)) (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ)) = (spinorPhi (P_c, sl2c_conj P_c)).val.val * (spinorPhi (D_s, (sl2c_conj D_s)⁻¹)).val.val * (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val := by
    rw [←h_Ds, ←hL, ←hL_inv]
  exact Eq.trans h_step1 h_val_mul.symm

lemma exp_iM_action_eq_tube_F_jordan_c (M : RealLorentzLieAlgebra) (P P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (s_a : ℂ) (h_s : s_a = 1 ∨ s_a = -1)
    (hM : spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M)
    (hP_eq : P.val = P_c.val * !![s_a, a; 0, s_a] * P_c.val⁻¹)
    (L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (hL_inv : (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)))
    (hM_eq : M.val = 2 • (L * M_J (s_a * a) * L_inv))
    (z : Fin 4 → ℂ) (hz_pos : (vec_to_spinor (fun k => -(z k).im)).PosDef) (s : ℝ) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ,
      X.IsHermitian ∧ Y.PosDef ∧
      (vec_to_spinor (fun k => -((exp_iM (s • M) • z) k).im : Fin 4 → ℂ)) = P_c.val * tube_F_jordan_c (s_a * a) X Y s * P_c.valᴴ ∧
      (vec_to_spinor (fun k => -(z k).im : Fin 4 → ℂ)) = P_c.val * tube_F_jordan_c (s_a * a) X Y 0 * P_c.valᴴ ∧
      (vec_to_spinor (fun k => -((exp_iM M • z) k).im : Fin 4 → ℂ)) = P_c.val * tube_F_jordan_c (s_a * a) X Y 1 * P_c.valᴴ := by
    let Z_re := vec_to_spinor (fun k => -(z k).re)
    let Z_im := vec_to_spinor (fun k => -(z k).im)
    let X := P_c⁻¹.val * Z_re * P_c⁻¹.valᴴ
    let Y := P_c⁻¹.val * Z_im * P_c⁻¹.valᴴ
    use X, Y
    have hZ_re_herm : Z_re.IsHermitian := by
      dsimp [Z_re]
      have h_eq : (fun k => -((z k).re : ℂ)) = (fun k => ((-(z k).re : ℝ) : ℂ)) := by
        ext k
        push_cast
        rfl
      rw [h_eq]
      rw [vec_to_spinor_eq_matrix]
      exact isHerm_two_by_two (-(z 0).re + -(z 3).re) (-(z 0).re - -(z 3).re) (((-(z 1).re : ℝ) : ℂ) - ((-(z 2).re : ℝ) : ℂ) * I)
    have hX_herm : X.IsHermitian := by
      dsimp [Matrix.IsHermitian, X]
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      have h : Z_reᴴ = Z_re := hZ_re_herm
      rw [h, Matrix.mul_assoc]
    have hY_pos : Y.PosDef := by
      dsimp [Y]
      have h_det : (P_c⁻¹.val).det ≠ 0 := by
        have h := P_c⁻¹.property
        rw [h]
        exact one_ne_zero
      exact posdef_congruence Z_im P_c⁻¹.val h_det hz_pos
    refine ⟨hX_herm, hY_pos, ?_, ?_, ?_⟩
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_s := jordan_matrix (s * (s_a * a))
      let A_s := P_c * D_s * P_c⁻¹
      have h_exp := exp_iM_sM_spinorPhi_jordan M P_c a s_a L L_inv hL hL_inv hM_eq s
      have h_action : (vec_to_spinor (fun k => -((exp_iM (s • M) • z) k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor (exp_iM (s • M) • z) - (vec_to_spinor (exp_iM (s • M) • z))ᴴ) := by
        exact vec_to_spinor_im (exp_iM (s • M) • z)
      rw [h_action]
      have h_mulvec : vec_to_spinor (exp_iM (s • M) • z) = vec_to_spinor (mulVec (spinorPhi_matrix A_s (sl2c_conj A_s)⁻¹) z) := by
        have h_eq : vec_to_spinor (exp_iM (s • M) • z) = vec_to_spinor (mulVec ((exp_iM (s • M)).val.val) z) := rfl
        have h_exp2 : (exp_iM (s • M)).val.val = (spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val := h_exp
        have h_eq2 : vec_to_spinor (mulVec ((exp_iM (s • M)).val.val) z) = vec_to_spinor (mulVec ((spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val) z) := by
          rw [h_exp2]
        have h_eq3 : vec_to_spinor (mulVec ((spinorPhi (A_s, (sl2c_conj A_s)⁻¹)).val.val) z) = vec_to_spinor (mulVec (spinorPhi_matrix A_s (sl2c_conj A_s)⁻¹) z) := rfl
        exact h_eq.trans (h_eq2.trans h_eq3)
      rw [h_mulvec]
      have h_spinor_action := spinorPhi_matrix_action A_s ((sl2c_conj A_s)⁻¹) z
      rw [h_spinor_action]
      have h_transpose : ((sl2c_conj A_s)⁻¹).valᵀ = (A_s⁻¹.val)ᴴ := sl2c_conj_inv_transpose A_s
      rw [h_transpose]
      have h_A_Z_A_H := A_Z_A_H_eq P_c D_s (vec_to_spinor z)
      have h_A_s_def : A_s = P_c * D_s * P_c⁻¹ := rfl
      rw [h_A_s_def, h_A_Z_A_H]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_s.val * (-X - I • Y) * D_s⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := jordan_c_action_inner (s_a * a) s X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_s.val * (-X - I • Y) * D_s⁻¹.valᴴ)ᴴ = D_s⁻¹.val * (-X - I • Y)ᴴ * D_s.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_0 := jordan_matrix ((0 : ℝ) * (s_a * a))
      have h_action_z : (vec_to_spinor (fun k => -(z k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor z - (vec_to_spinor z)ᴴ) := by
        exact vec_to_spinor_im z
      rw [h_action_z]
      have h_z_id : vec_to_spinor z = P_c.val * (D_0.val * (P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ) * D_0⁻¹.valᴴ) * P_c.valᴴ := by
        have h_D0_id : D_0.val = 1 := by
          ext i j
          dsimp [D_0, jordan_matrix, J_mat]
          fin_cases i <;> fin_cases j <;> {
            simp [Matrix.cons_val_zero, zero_mul]
          }
        have h_D0_inv_id : D_0⁻¹.valᴴ = 1 := by
          have hD0 : D_0 = 1 := Subtype.ext h_D0_id
          rw [hD0, inv_one]
          exact conjTranspose_one
        rw [h_D0_id, h_D0_inv_id]
        simp only [Matrix.mul_one, Matrix.one_mul]
        have h_Pc_inv : P_c.val * P_c⁻¹.val = 1 := by
          have h : P_c * P_c⁻¹ = 1 := mul_inv_cancel P_c
          have h2 : (P_c * P_c⁻¹).val = (1 : SpecialLinearGroup (Fin 2) ℂ).val := congrArg Subtype.val h
          exact h2
        have h_Pc_inv2 : P_c⁻¹.valᴴ * P_c.valᴴ = 1 := by
          calc
            P_c⁻¹.valᴴ * P_c.valᴴ = (P_c.val * P_c⁻¹.val)ᴴ := by rw [conjTranspose_mul]
            _ = (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [h_Pc_inv]
            _ = 1 := conjTranspose_one
        rw [←Matrix.mul_assoc P_c.val, ←Matrix.mul_assoc P_c.val]
        rw [h_Pc_inv]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
        rw [h_Pc_inv2, Matrix.mul_one]
      rw [h_z_id]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_0.val * (-X - I • Y) * D_0⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := jordan_c_action_inner (s_a * a) 0 X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_0.val * (-X - I • Y) * D_0⁻¹.valᴴ)ᴴ = D_0⁻¹.val * (-X - I • Y)ᴴ * D_0.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]
    · 
      have h_Z : -(vec_to_spinor (fun k => -(z k).re)) - I • (vec_to_spinor (fun k => -(z k).im)) = vec_to_spinor z := Z_re_im_eq_vec_to_spinor z
      let D_1 := jordan_matrix ((1 : ℝ) * (s_a * a))
      let A_1 := P_c * D_1 * P_c⁻¹
      have h_exp := exp_iM_sM_spinorPhi_jordan M P_c a s_a L L_inv hL hL_inv hM_eq 1
      have h_action : (vec_to_spinor (fun k => -((exp_iM M • z) k).im : Fin 4 → ℂ)) = (I / 2) • (vec_to_spinor (exp_iM M • z) - (vec_to_spinor (exp_iM M • z))ᴴ) := by
        exact vec_to_spinor_im (exp_iM M • z)
      rw [h_action]
      have h_mulvec : vec_to_spinor (exp_iM M • z) = vec_to_spinor (mulVec (spinorPhi_matrix A_1 (sl2c_conj A_1)⁻¹) z) := by
        have h_1M : (1 : ℝ) • M = M := one_smul ℝ M
        have h_exp2 : (exp_iM M).val.val = (spinorPhi (A_1, (sl2c_conj A_1)⁻¹)).val.val := by
          calc (exp_iM M).val.val = (exp_iM ((1 : ℝ) • M)).val.val := by rw [h_1M]
               _ = (spinorPhi (A_1, (sl2c_conj A_1)⁻¹)).val.val := h_exp
        change vec_to_spinor (mulVec ((exp_iM M).val.val) z) = _
        rw [h_exp2]
        rfl
      rw [h_mulvec]
      have h_spinor_action := spinorPhi_matrix_action A_1 ((sl2c_conj A_1)⁻¹) z
      rw [h_spinor_action]
      have h_transpose : ((sl2c_conj A_1)⁻¹).valᵀ = (A_1⁻¹.val)ᴴ := sl2c_conj_inv_transpose A_1
      rw [h_transpose]
      have h_A_Z_A_H := A_Z_A_H_eq P_c D_1 (vec_to_spinor z)
      have h_A_1_def : A_1 = P_c * D_1 * P_c⁻¹ := rfl
      rw [h_A_1_def, h_A_Z_A_H]
      have h_subst : P_c⁻¹.val * vec_to_spinor z * P_c⁻¹.valᴴ = -X - I • Y := by
        dsimp [X, Y, Z_re, Z_im]
        rw [←h_Z]
        ext i j
        simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Matrix.smul_apply, Fin.sum_univ_two, smul_eq_mul]
        ring
      rw [h_subst]
      have h_factor := matrix_factor_action P_c.val (D_1.val * (-X - I • Y) * D_1⁻¹.valᴴ)
      rw [h_factor]
      have h_inner := jordan_c_action_inner (s_a * a) 1 X Y hX_herm hY_pos.1
      rw [←h_inner]
      have h_herm_prod : (D_1.val * (-X - I • Y) * D_1⁻¹.valᴴ)ᴴ = D_1⁻¹.val * (-X - I • Y)ᴴ * D_1.valᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, ←Matrix.mul_assoc]
      rw [h_herm_prod]
