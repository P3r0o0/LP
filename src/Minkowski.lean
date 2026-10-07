import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

namespace Geometry

open Matrix





def minkowskiMetricReal : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, 0],
    ![0, 0, 0, -1]]

def minkowskiInner (x y : Fin 4 → ℝ) : ℝ :=
  dotProduct x (minkowskiMetricReal.mulVec y)

lemma minkowskiInner_explicit (x y : Fin 4 → ℝ) :
  minkowskiInner x y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  simp [minkowskiInner, dotProduct, mulVec, minkowskiMetricReal, Fin.sum_univ_four]
  ring

lemma cauchy_schwarz_3 (a c e b d f : ℝ) :
  (a * b + c * d + e * f)^2 ≤ (a^2 + c^2 + e^2) * (b^2 + d^2 + f^2) := by
  have h : (a^2 + c^2 + e^2) * (b^2 + d^2 + f^2) - (a * b + c * d + e * f)^2 =
    (a * d - b * c)^2 + (a * f - b * e)^2 + (c * f - d * e)^2 := by ring
  linarith [sq_nonneg (a * d - b * c), sq_nonneg (a * f - b * e), sq_nonneg (c * f - d * e)]


def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1, 0, 0, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, 0],
    ![0, 0, 0, -1]]

lemma minkowskiMetric_transpose : minkowskiMetricᵀ = minkowskiMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl






def SpecialComplexLorentzGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℂ) where
  carrier := { Λ | (Λ.val)ᵀ * minkowskiMetric * Λ.val = minkowskiMetric }
  mul_mem' {A B} hA hB := by
    change (A.val * B.val)ᵀ * minkowskiMetric * (A.val * B.val) = minkowskiMetric
    rw [Matrix.transpose_mul]
    
    
    have h1 : A.valᵀ * minkowskiMetric * A.val = minkowskiMetric := hA
    have h2 : B.valᵀ * (A.valᵀ * minkowskiMetric * A.val) * B.val = B.valᵀ * minkowskiMetric * B.val := by
      rw [h1]
    
    
    have h_assoc : (B.valᵀ * A.valᵀ) * minkowskiMetric * (A.val * B.val) = B.valᵀ * (A.valᵀ * minkowskiMetric * A.val) * B.val := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, h2]
    exact hB
  one_mem' := by
    change (1 : Matrix (Fin 4) (Fin 4) ℂ)ᵀ * minkowskiMetric * 1 = minkowskiMetric
    simp
  inv_mem' {A} hA := by
    change (A.inv)ᵀ * minkowskiMetric * A.inv = minkowskiMetric
    
    have h1 : A.invᵀ * (A.valᵀ * minkowskiMetric * A.val) * A.inv = A.invᵀ * minkowskiMetric * A.inv := by
      rw [hA]
    have h2 : A.invᵀ * A.valᵀ = 1 := by
      rw [←Matrix.transpose_mul, A.val_inv, Matrix.transpose_one]
    have h3 : A.invᵀ * (A.valᵀ * minkowskiMetric * A.val) * A.inv = A.invᵀ * A.valᵀ * minkowskiMetric * (A.val * A.inv) := by
      simp only [Matrix.mul_assoc]
    rw [h3, h2, A.val_inv] at h1
    rw [Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm





def SpecialSpecialComplexLorentzGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℂ) where
  carrier := { Λ | (Λ.val)ᵀ * minkowskiMetric * Λ.val = minkowskiMetric ∧ (Λ.val).det = 1 }
  mul_mem' {A B} hA hB := by
    constructor
    · exact SpecialComplexLorentzGroup.mul_mem' hA.1 hB.1
    · change (A.val * B.val).det = 1
      rw [det_mul, hA.2, hB.2, mul_one]
  one_mem' := by
    constructor
    · exact SpecialComplexLorentzGroup.one_mem'
    · change (1 : Matrix (Fin 4) (Fin 4) ℂ).det = 1
      exact det_one
  inv_mem' {A} hA := by
    constructor
    · exact SpecialComplexLorentzGroup.inv_mem' hA.1
    · change (A.inv).det = 1
      have h1 : (A.val * A.inv).det = (1 : Matrix (Fin 4) (Fin 4) ℂ).det := by
        rw [A.val_inv]
      rw [det_mul, hA.2, one_mul, det_one] at h1
      exact h1





def RealLorentzGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℝ) where
  carrier := { Λ | (Λ.val)ᵀ * minkowskiMetricReal * Λ.val = minkowskiMetricReal }
  mul_mem' {A B} hA hB := by
    change (A.val * B.val)ᵀ * minkowskiMetricReal * (A.val * B.val) = minkowskiMetricReal
    rw [Matrix.transpose_mul]
    have h1 : A.valᵀ * minkowskiMetricReal * A.val = minkowskiMetricReal := hA
    have h2 : B.valᵀ * (A.valᵀ * minkowskiMetricReal * A.val) * B.val = B.valᵀ * minkowskiMetricReal * B.val := by
      rw [h1]
    have h_assoc : (B.valᵀ * A.valᵀ) * minkowskiMetricReal * (A.val * B.val) = B.valᵀ * (A.valᵀ * minkowskiMetricReal * A.val) * B.val := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, h2]
    exact hB
  one_mem' := by
    change (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * minkowskiMetricReal * 1 = minkowskiMetricReal
    simp
  inv_mem' {A} hA := by
    change (A.inv)ᵀ * minkowskiMetricReal * A.inv = minkowskiMetricReal
    have h1 : A.invᵀ * (A.valᵀ * minkowskiMetricReal * A.val) * A.inv = A.invᵀ * minkowskiMetricReal * A.inv := by
      rw [hA]
    have h2 : A.invᵀ * A.valᵀ = 1 := by
      rw [←Matrix.transpose_mul, A.val_inv, Matrix.transpose_one]
    have h3 : A.invᵀ * (A.valᵀ * minkowskiMetricReal * A.val) * A.inv = A.invᵀ * A.valᵀ * minkowskiMetricReal * (A.val * A.inv) := by
      simp only [Matrix.mul_assoc]
    rw [h3, h2, A.val_inv] at h1
    rw [Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm

def SpecialRealLorentzGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℝ) where
  carrier := { Λ | (Λ.val)ᵀ * minkowskiMetricReal * Λ.val = minkowskiMetricReal ∧ (Λ.val).det = 1 }
  mul_mem' {A B} hA hB := by
    constructor
    · exact RealLorentzGroup.mul_mem' hA.1 hB.1
    · change (A.val * B.val).det = 1
      rw [det_mul, hA.2, hB.2, mul_one]
  one_mem' := by
    constructor
    · exact RealLorentzGroup.one_mem'
    · change (1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1
      exact det_one
  inv_mem' {A} hA := by
    constructor
    · exact RealLorentzGroup.inv_mem' hA.1
    · change (A.inv).det = 1
      have h1 : (A.val * A.inv).det = (1 : Matrix (Fin 4) (Fin 4) ℝ).det := by
        rw [A.val_inv]
      rw [det_mul, hA.2, one_mul, det_one] at h1
      exact h1

lemma minkowskiMetricReal_sq : minkowskiMetricReal * minkowskiMetricReal = 1 := by
  ext i j
  simp [Matrix.mul_apply, minkowskiMetricReal, Matrix.one_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num

lemma lorentz_inv_eq (A : Matrix.GeneralLinearGroup (Fin 4) ℝ) (h : A.valᵀ * minkowskiMetricReal * A.val = minkowskiMetricReal) :
  (A⁻¹).val = minkowskiMetricReal * A.valᵀ * minkowskiMetricReal := by
  have h1 : A.valᵀ * minkowskiMetricReal * A.val = minkowskiMetricReal := h
  have h2 : (A.valᵀ * minkowskiMetricReal * A.val) * (A⁻¹).val = minkowskiMetricReal * (A⁻¹).val := by rw [h1]
  have h3 : (A.valᵀ * minkowskiMetricReal * A.val) * (A⁻¹).val = A.valᵀ * minkowskiMetricReal * (A.val * (A⁻¹).val) := by
    rw [Matrix.mul_assoc (A.valᵀ * minkowskiMetricReal) A.val (A⁻¹).val]
  rw [h3] at h2
  have h4 : A.val * (A⁻¹).val = 1 := by exact Units.mul_inv A
  rw [h4, Matrix.mul_one] at h2
  have h5 : minkowskiMetricReal * (A.valᵀ * minkowskiMetricReal) = minkowskiMetricReal * (minkowskiMetricReal * (A⁻¹).val) := by rw [h2]
  have h6 : minkowskiMetricReal * (A.valᵀ * minkowskiMetricReal) = (minkowskiMetricReal * A.valᵀ) * minkowskiMetricReal := by
    rw [←Matrix.mul_assoc]
  have h7 : minkowskiMetricReal * (minkowskiMetricReal * (A⁻¹).val) = (minkowskiMetricReal * minkowskiMetricReal) * (A⁻¹).val := by
    rw [←Matrix.mul_assoc]
  rw [h7, minkowskiMetricReal_sq, Matrix.one_mul] at h5
  rw [h6] at h5
  exact h5.symm

lemma lorentz_row_eq (A : Matrix.GeneralLinearGroup (Fin 4) ℝ) (h : A.valᵀ * minkowskiMetricReal * A.val = minkowskiMetricReal) :
  A.val * minkowskiMetricReal * A.valᵀ = minkowskiMetricReal := by
  have hinv : (A⁻¹).val = minkowskiMetricReal * A.valᵀ * minkowskiMetricReal := lorentz_inv_eq A h
  have h2 : A.val * (A⁻¹).val = 1 := by exact Units.mul_inv A
  have h3 : A.val * (minkowskiMetricReal * A.valᵀ * minkowskiMetricReal) = 1 := by
    rw [←hinv]
    exact h2
  have h4 : (A.val * (minkowskiMetricReal * A.valᵀ * minkowskiMetricReal)) * minkowskiMetricReal = 1 * minkowskiMetricReal := by rw [h3]
  rw [Matrix.one_mul] at h4
  have h5 : (A.val * (minkowskiMetricReal * A.valᵀ * minkowskiMetricReal)) * minkowskiMetricReal = A.val * ((minkowskiMetricReal * A.valᵀ * minkowskiMetricReal) * minkowskiMetricReal) := by
    rw [Matrix.mul_assoc]
  rw [h5] at h4
  have h6 : (minkowskiMetricReal * A.valᵀ * minkowskiMetricReal) * minkowskiMetricReal = minkowskiMetricReal * A.valᵀ * (minkowskiMetricReal * minkowskiMetricReal) := by
    rw [Matrix.mul_assoc]
  rw [h6, minkowskiMetricReal_sq, Matrix.mul_one] at h4
  have h7 : A.val * (minkowskiMetricReal * A.valᵀ) = (A.val * minkowskiMetricReal) * A.valᵀ := by
    rw [←Matrix.mul_assoc]
  rw [h7] at h4
  exact h4

lemma lorentz_row_00_sq (A : Matrix.GeneralLinearGroup (Fin 4) ℝ) (h : A.val * minkowskiMetricReal * A.valᵀ = minkowskiMetricReal) :
  (A.val 0 0)^2 = 1 + (A.val 0 1)^2 + (A.val 0 2)^2 + (A.val 0 3)^2 := by
  have h_eq := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, minkowskiMetricReal, transpose_apply, Fin.sum_univ_four] at h_eq
  linarith

lemma lorentz_col_00_sq (A : Matrix.GeneralLinearGroup (Fin 4) ℝ) (h : A.valᵀ * minkowskiMetricReal * A.val = minkowskiMetricReal) :
  (A.val 0 0)^2 = 1 + (A.val 1 0)^2 + (A.val 2 0)^2 + (A.val 3 0)^2 := by
  have h_eq := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, minkowskiMetricReal, transpose_apply, Fin.sum_univ_four] at h_eq
  linarith

lemma sq_sum_ineq (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
  (ha : a0 ^ 2 = 1 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) (ha0 : a0 > 0)
  (hb : b0 ^ 2 = 1 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) (hb0 : b0 > 0) :
  a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 > 0 := by
  have hid : (a1^2 + a2^2 + a3^2) * (b1^2 + b2^2 + b3^2) - (a1*b1 + a2*b2 + a3*b3)^2 =
    (a1*b2 - a2*b1)^2 + (a2*b3 - a3*b2)^2 + (a3*b1 - a1*b3)^2 := by ring
  have hpos : 0 ≤ (a1*b2 - a2*b1)^2 + (a2*b3 - a3*b2)^2 + (a3*b1 - a1*b3)^2 := by positivity
  have hcs : (a1*b1 + a2*b2 + a3*b3)^2 ≤ (a1^2 + a2^2 + a3^2) * (b1^2 + b2^2 + b3^2) := by linarith
  have ha2 : a1^2 + a2^2 + a3^2 = a0^2 - 1 := by linarith
  have hb2 : b1^2 + b2^2 + b3^2 = b0^2 - 1 := by linarith
  have hbnd : (a1*b1 + a2*b2 + a3*b3)^2 ≤ (a0^2 - 1) * (b0^2 - 1) := by nlinarith
  have hbnd2 : (a0^2 - 1) * (b0^2 - 1) < a0^2 * b0^2 := by
    calc (a0^2 - 1) * (b0^2 - 1)
      _ = a0^2 * b0^2 - (a0^2 + b0^2) + 1 := by ring
      _ < a0^2 * b0^2 := by
        have h1 : a1^2 + a2^2 + a3^2 ≥ 0 := by positivity
        have h2 : b1^2 + b2^2 + b3^2 ≥ 0 := by positivity
        have h3 : a0^2 ≥ 1 := by linarith
        have h4 : b0^2 ≥ 1 := by linarith
        nlinarith
  have hsq : (a1*b1 + a2*b2 + a3*b3)^2 < (a0*b0)^2 := by nlinarith
  have hsq2 : -(a0*b0) < a1*b1 + a2*b2 + a3*b3 := by
    have h_abs : |a1*b1 + a2*b2 + a3*b3| < |a0*b0| := by
      exact (sq_lt_sq.1 hsq)
    have h_y_pos : a0 * b0 > 0 := by positivity
    have h_abs2 : |a0*b0| = a0*b0 := abs_of_pos h_y_pos
    rw [h_abs2] at h_abs
    exact (abs_lt.mp h_abs).1
  linarith

def ProperOrthochronousLorentzGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℝ) where
  carrier := { Λ | (Λ.val)ᵀ * minkowskiMetricReal * Λ.val = minkowskiMetricReal ∧ (Λ.val).det = 1 ∧ Λ.val 0 0 > 0 }
  mul_mem' {A B} hA hB := by
    constructor
    · exact SpecialRealLorentzGroup.mul_mem' ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩ |>.1
    · constructor
      · exact SpecialRealLorentzGroup.mul_mem' ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩ |>.2
      · have hA_row := lorentz_row_eq A hA.1
        have ha_sq := lorentz_row_00_sq A hA_row
        have hb_sq := lorentz_col_00_sq B hB.1
        change (A.val * B.val) 0 0 > 0
        have h_exp : (A.val * B.val) 0 0 = A.val 0 0 * B.val 0 0 + A.val 0 1 * B.val 1 0 + A.val 0 2 * B.val 2 0 + A.val 0 3 * B.val 3 0 := by
          simp [Matrix.mul_apply, Fin.sum_univ_four]
        rw [h_exp]
        exact sq_sum_ineq (A.val 0 0) (A.val 0 1) (A.val 0 2) (A.val 0 3) (B.val 0 0) (B.val 1 0) (B.val 2 0) (B.val 3 0) ha_sq hA.2.2 hb_sq hB.2.2
  one_mem' := by
    constructor
    · exact SpecialRealLorentzGroup.one_mem'.1
    · constructor
      · exact SpecialRealLorentzGroup.one_mem'.2
      · change (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 0 > 0
        simp
  inv_mem' {A} hA := by
    constructor
    · exact SpecialRealLorentzGroup.inv_mem' ⟨hA.1, hA.2.1⟩ |>.1
    · constructor
      · exact SpecialRealLorentzGroup.inv_mem' ⟨hA.1, hA.2.1⟩ |>.2
      · have hinv : (A⁻¹).val = minkowskiMetricReal * A.valᵀ * minkowskiMetricReal := lorentz_inv_eq A hA.1
        change (A⁻¹).val 0 0 > 0
        have h_exp : (A⁻¹).val 0 0 = A.val 0 0 := by
          calc (A⁻¹).val 0 0
            _ = (minkowskiMetricReal * A.valᵀ * minkowskiMetricReal) 0 0 := by rw [hinv]
            _ = A.val 0 0 := by
              simp [Matrix.mul_apply, minkowskiMetricReal, transpose_apply, Fin.sum_univ_four]
        rw [h_exp]
        exact hA.2.2





def forward_light_cone : Set (Fin 4 → ℝ) :=
  { x | x 0 > 0 ∧ minkowskiInner x x > 0 }

lemma forward_light_cone_inner_pos {x y : Fin 4 → ℝ}
  (hx : x ∈ forward_light_cone) (hy : y ∈ forward_light_cone) :
  minkowskiInner x y > 0 := by
  have hx0 : x 0 > 0 := hx.1
  have hy0 : y 0 > 0 := hy.1
  have hxx : minkowskiInner x x > 0 := hx.2
  have hyy : minkowskiInner y y > 0 := hy.2
  rw [minkowskiInner_explicit] at hxx hyy ⊢
  have hxx2 : (x 0)^2 > (x 1)^2 + (x 2)^2 + (x 3)^2 := by linarith
  have hyy2 : (y 0)^2 > (y 1)^2 + (y 2)^2 + (y 3)^2 := by linarith
  have hA : (x 1)^2 + (x 2)^2 + (x 3)^2 ≥ 0 := by positivity
  have hB : (y 1)^2 + (y 2)^2 + (y 3)^2 ≥ 0 := by positivity
  have h_prod : (x 0)^2 * (y 0)^2 > ((x 1)^2 + (x 2)^2 + (x 3)^2) * ((y 1)^2 + (y 2)^2 + (y 3)^2) := by nlinarith
  have hCS := cauchy_schwarz_3 (x 1) (x 2) (x 3) (y 1) (y 2) (y 3)
  have h_sq : (x 0 * y 0)^2 > (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)^2 := by linarith
  have h_xy0 : x 0 * y 0 > 0 := mul_pos hx0 hy0
  have h_diff : (x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)) * (x 0 * y 0 + (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)) > 0 := by
    calc
      _ = (x 0 * y 0)^2 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)^2 := by ring
      _ > 0 := by linarith
  rcases mul_pos_iff.mp h_diff with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · have h_contra : x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3) > 0 := by linarith
    linarith

lemma forward_light_cone_convex : Convex ℝ forward_light_cone := by
  intro x hx y hy a b ha hb hab
  have hx0 : x 0 > 0 := hx.1
  have hy0 : y 0 > 0 := hy.1
  have h_add0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by rfl
  have h_pos0 : (a • x + b • y) 0 > 0 := by
    rw [h_add0]
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      linarith
    · have ha_pos : a > 0 := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_nonneg : b * y 0 ≥ 0 := mul_nonneg hb (le_of_lt hy0)
      have ha_pos' : a * x 0 > 0 := mul_pos ha_pos hx0
      linarith
  have h_inner : minkowskiInner (a • x + b • y) (a • x + b • y) =
    a^2 * minkowskiInner x x + b^2 * minkowskiInner y y + 2 * a * b * minkowskiInner x y := by
    rw [minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit]
    have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
    have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
    have h2 : (a • x + b • y) 2 = a * x 2 + b * y 2 := rfl
    have h3 : (a • x + b • y) 3 = a * x 3 + b * y 3 := rfl
    rw [h0, h1, h2, h3]
    ring
  have hxx : minkowskiInner x x > 0 := hx.2
  have hyy : minkowskiInner y y > 0 := hy.2
  have hxy : minkowskiInner x y > 0 := forward_light_cone_inner_pos hx hy

  constructor
  · exact h_pos0
  · rw [h_inner]
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      nlinarith
    · have ha_pos : a > 0 := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1_pos : a^2 * minkowskiInner x x > 0 := mul_pos (pow_pos ha_pos 2) hxx
      have h2_nonneg : b^2 * minkowskiInner y y ≥ 0 := mul_nonneg (sq_nonneg b) (le_of_lt hyy)
      have h3_nonneg : 2 * a * b * minkowskiInner x y ≥ 0 := by
        apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · exact hb
        · exact le_of_lt hxy
      linarith

def forward_tube : Set (Fin 4 → ℂ) :=
  { z | (fun (i : Fin 4) => -(z i).im) ∈ forward_light_cone }

def forward_tube_n (n : ℕ) : Set (Fin n → Fin 4 → ℂ) :=
  { z | ∀ (i : Fin n) (hi : i.val + 1 < n), (fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) ∈ forward_light_cone }

def backward_light_cone : Set (Fin 4 → ℝ) :=
  { x | x 0 < 0 ∧ minkowskiInner x x > 0 }

def backward_tube : Set (Fin 4 → ℂ) :=
  { z | (fun (i : Fin 4) => -(z i).im) ∈ backward_light_cone }

def backward_tube_n (n : ℕ) : Set (Fin n → Fin 4 → ℂ) :=
  { z | ∀ (i : Fin n) (hi : i.val + 1 < n), (fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) ∈ backward_light_cone }

def extended_tube_n (n : ℕ) : Set (Fin n → Fin 4 → ℂ) :=
  ⋃ Λ : SpecialSpecialComplexLorentzGroup, (fun z => Λ • z) '' forward_tube_n n


def coeReal (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℂ :=
  fun i j => (x i j : ℂ)


def is_spacelike (v : Fin 4 → ℝ) : Prop :=
  minkowskiInner v v < 0

def jost_differences_n (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  { v | ∃ (i : Fin n) (hi : i.val + 1 < n), v = x i - x ⟨i.val + 1, hi⟩ }

def jost_convex_hull (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  convexHull ℝ (jost_differences_n n x)

def jost_points_n (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  { x | ∀ v ∈ jost_convex_hull n x, is_spacelike v }

lemma jost_convex_hull_convex (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
  Convex ℝ (jost_convex_hull n x) := convex_convexHull ℝ (jost_differences_n n x)

lemma jost_differences_n_finite (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
  (jost_differences_n n x).Finite := by
  let f : {i : Fin n // i.val + 1 < n} → (Fin 4 → ℝ) := fun ⟨i, hi⟩ => x i - x ⟨i.val + 1, hi⟩
  have h_eq : jost_differences_n n x = Set.range f := by
    ext v
    simp only [jost_differences_n, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [h_eq]
  exact Set.finite_range f

lemma jost_convex_hull_compact (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
  IsCompact (jost_convex_hull n x) := by
  unfold jost_convex_hull
  apply Set.Finite.isCompact_convexHull
  exact jost_differences_n_finite n x

lemma continuous_minkowskiInner_self : Continuous (fun (v : Fin 4 → ℝ) => minkowskiInner v v) := by
  dsimp [minkowskiInner, minkowskiMetricReal, dotProduct, Matrix.mulVec]
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul
  · exact continuous_apply i
  · apply continuous_finsetSum
    intro j _
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_apply j

lemma spacelike_margin {K : Set (Fin 4 → ℝ)} (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_spacelike : ∀ v ∈ K, is_spacelike v) :
  K = ∅ ∨ ∃ ε > 0, ∀ v ∈ K, minkowskiInner v v ≤ -ε := by
  by_cases h : K = ∅
  · left; exact h
  · right
    let S : Set ℝ := (fun v => minkowskiInner v v) '' K
    have h_img_compact : IsCompact S := hK_compact.image continuous_minkowskiInner_self
    have h_img_ne : S.Nonempty := Set.Nonempty.image (fun v => minkowskiInner v v) (Set.nonempty_iff_ne_empty.mpr h)
    have h_cont_id : ContinuousOn (id : ℝ → ℝ) S := continuousOn_id
    obtain ⟨M, hM_mem, hM_max⟩ := h_img_compact.exists_isMaxOn h_img_ne h_cont_id
    obtain ⟨v, hv_mem, hv_eq⟩ := (Set.mem_image _ _ _).mp hM_mem
    have hv_space : minkowskiInner v v < 0 := hK_spacelike v hv_mem
    use -M
    constructor
    · linarith [hv_space, hv_eq]
    · intro w hw
      have h_le : (fun v => minkowskiInner v v) w ≤ M := by
        have hw_S : (fun v => minkowskiInner v v) w ∈ S := Set.mem_image_of_mem _ hw
        exact hM_max hw_S
      linarith

def algebraic_rotation_z (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0],
    ![0, c, -s, 0],
    ![0, s, c, 0],
    ![0, 0, 0, 1]]

def algebraic_rotation_y (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0],
    ![0, c, 0, s],
    ![0, 0, 1, 0],
    ![0, -s, 0, c]]

lemma algebraic_rotation_z_is_lorentz (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
  Matrix.transpose (algebraic_rotation_z c s) * minkowskiMetricReal * (algebraic_rotation_z c s) = minkowskiMetricReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    repeat rw [Fin.sum_univ_four]
    simp [algebraic_rotation_z, minkowskiMetricReal]
    try ring_nf
    try nlinarith [h]
  }

lemma lorentz_mul (A B : Matrix (Fin 4) (Fin 4) ℝ)
  (hA : Aᵀ * minkowskiMetricReal * A = minkowskiMetricReal)
  (hB : Bᵀ * minkowskiMetricReal * B = minkowskiMetricReal) :
  (A * B)ᵀ * minkowskiMetricReal * (A * B) = minkowskiMetricReal := by
  calc (A * B)ᵀ * minkowskiMetricReal * (A * B)
    _ = Bᵀ * Aᵀ * minkowskiMetricReal * (A * B) := by rw [Matrix.transpose_mul]
    _ = Bᵀ * (Aᵀ * minkowskiMetricReal * A) * B := by simp only [Matrix.mul_assoc]
    _ = Bᵀ * minkowskiMetricReal * B := by rw [hA]
    _ = minkowskiMetricReal := hB

lemma algebraic_rotation_y_is_lorentz (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
  Matrix.transpose (algebraic_rotation_y c s) * minkowskiMetricReal * (algebraic_rotation_y c s) = minkowskiMetricReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    repeat rw [Fin.sum_univ_four]
    simp [algebraic_rotation_y, minkowskiMetricReal]
    try ring_nf
    try nlinarith [h]
  }

noncomputable def rotation_z (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  algebraic_rotation_z (Real.cos θ) (Real.sin θ)

noncomputable def rotation_y (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  algebraic_rotation_y (Real.cos θ) (Real.sin θ)

noncomputable def real_boost_z (v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let γ := 1 / Real.sqrt (1 - v^2)
  ![![γ, 0, 0, -γ * v],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![-γ * v, 0, 0, γ]]

lemma rotation_z_is_lorentz (θ : ℝ) :
  Matrix.transpose (rotation_z θ) * minkowskiMetricReal * (rotation_z θ) = minkowskiMetricReal := by
  have h : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := by
    have h2 := Real.sin_sq_add_cos_sq θ
    linarith
  exact algebraic_rotation_z_is_lorentz (Real.cos θ) (Real.sin θ) h

lemma rotation_y_is_lorentz (θ : ℝ) :
  Matrix.transpose (rotation_y θ) * minkowskiMetricReal * (rotation_y θ) = minkowskiMetricReal := by
  have h : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := by
    have h2 := Real.sin_sq_add_cos_sq θ
    linarith
  exact algebraic_rotation_y_is_lorentz (Real.cos θ) (Real.sin θ) h

lemma real_boost_z_is_lorentz (v : ℝ) (hv : v ^ 2 < 1) :
  Matrix.transpose (real_boost_z v) * minkowskiMetricReal * (real_boost_z v) = minkowskiMetricReal := by
  have hγsq : (1 / Real.sqrt (1 - v ^ 2)) ^ 2 = 1 / (1 - v ^ 2) := by
    rw [one_div, one_div, inv_pow, Real.sq_sqrt (by linarith)]
  have hinv : (1 - v ^ 2) * (1 - v ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by linarith : (1 : ℝ) - v ^ 2 ≠ 0)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
    have hpos : (0 : ℝ) < 1 - v ^ 2 := by linarith
    have hsq : Real.sqrt (1 - v ^ 2) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by linarith)
    have hsqne : Real.sqrt (1 - v ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    field_simp
    nlinarith [Real.sq_sqrt (show (0:Real) ≤ 1 - v^2 by linarith)]
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp; ring
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp; ring
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, real_boost_z, minkowskiMetricReal]; repeat rw [Fin.sum_univ_four]; simp
    have hpos : (0 : ℝ) < 1 - v ^ 2 := by linarith
    have hsqne : Real.sqrt (1 - v ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    field_simp
    nlinarith [Real.sq_sqrt (show (0:Real) ≤ 1 - v^2 by linarith)]

lemma algebraic_rotation_z_det (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (algebraic_rotation_z c s).det = 1 := by
  dsimp [algebraic_rotation_z]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  ring_nf
  exact h

lemma algebraic_rotation_y_det (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (algebraic_rotation_y c s).det = 1 := by
  dsimp [algebraic_rotation_y]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  ring_nf
  exact h

lemma real_boost_z_det (v : ℝ) (h : v ^ 2 < 1) : (real_boost_z v).det = 1 := by
  dsimp [real_boost_z]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have h1 : ![0, 0, (1 : ℝ), 0] (Fin.succAbove 3 2) = 1 := rfl
  rw [h1]
  let γ := (Real.sqrt (1 - v^2))⁻¹
  have h_eq : γ * γ + (-1) ^ 3 * (γ * v) * (1 * (γ * v)) = γ ^ 2 - v ^ 2 * γ ^ 2 := by
    dsimp [γ]
    ring
  rw [h_eq]
  have h_den : 1 - v^2 ≠ 0 := by linarith
  have h_den2 : Real.sqrt (1 - v^2) ^ 2 = 1 - v^2 := Real.sq_sqrt (by linarith)
  have h_inv : γ ^ 2 = (1 - v ^ 2)⁻¹ := by
    dsimp [γ]
    calc (Real.sqrt (1 - v ^ 2))⁻¹ ^ 2
      _ = (Real.sqrt (1 - v ^ 2) ^ 2)⁻¹ := by rw [← inv_pow]
      _ = (1 - v ^ 2)⁻¹ := by rw [h_den2]
  rw [h_inv]
  calc (1 - v ^ 2)⁻¹ - v ^ 2 * (1 - v ^ 2)⁻¹
    _ = (1 - v ^ 2) * (1 - v ^ 2)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ h_den


lemma lorentz_align_non_spacelike (u : Fin 4 → ℝ) (hu : ¬ is_spacelike u) :
  ∃ (Λ : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    (Λ.valᵀ * minkowskiMetricReal * Λ.val = minkowskiMetricReal) ∧
    (Λ.val.det = 1) ∧
    ((Λ.val *ᵥ u) 1 = 0) ∧ ((Λ.val *ᵥ u) 2 = 0) ∧ ((Λ.val *ᵥ u) 0 = u 0) ∧
    (∀ x : Fin 4 → ℝ, (Λ.val *ᵥ x) 0 = x 0) := by
  let r12 := Real.sqrt (u 1 ^ 2 + u 2 ^ 2)
  by_cases hr : r12 = 0
  · have h12 : u 1 ^ 2 + u 2 ^ 2 = 0 := by
      have hs := Real.sqrt_eq_zero'.mp hr
      exact le_antisymm hs (by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)])
    have hu1_sq : u 1 ^ 2 = 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), h12]
    have hu2_sq : u 2 ^ 2 = 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), h12]
    have hu1 : u 1 = 0 := sq_eq_zero_iff.mp hu1_sq
    have hu2 : u 2 = 0 := sq_eq_zero_iff.mp hu2_sq
    let Λ := (1 : Matrix.GeneralLinearGroup (Fin 4) ℝ)
    use Λ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * minkowskiMetricReal * 1 = minkowskiMetricReal
      simp
    · change (1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1
      exact Matrix.det_one
    · change (∑ j : Fin 4, (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 j * u j) = 0
      rw [Fin.sum_univ_four]
      simp
      exact hu1
    · change (∑ j : Fin 4, (1 : Matrix (Fin 4) (Fin 4) ℝ) 2 j * u j) = 0
      rw [Fin.sum_univ_four]
      simp
      exact hu2
    · change (∑ j : Fin 4, (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 j * u j) = u 0
      rw [Fin.sum_univ_four]
      simp
    · intro x
      change (1 *ᵥ x) 0 = x 0
      rw [Matrix.one_mulVec]
  · let cz := u 1 / r12
    let sz := -(u 2) / r12
    have hcz_sz : cz^2 + sz^2 = 1 := by
      have hr2 : r12^2 = u 1 ^ 2 + u 2 ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)])
      calc cz^2 + sz^2 = (u 1 ^ 2) / r12^2 + (u 2 ^ 2) / r12^2 := by ring
        _ = (u 1 ^ 2 + u 2 ^ 2) / (u 1 ^ 2 + u 2 ^ 2) := by rw [hr2, add_div]
        _ = 1 := div_self (by
          intro h_zero
          have hr_zero : r12^2 = 0 := by rw [hr2, h_zero]
          exact hr (sq_eq_zero_iff.mp hr_zero))

    let Λz_val := algebraic_rotation_z cz sz
    have hΛz_lorentz : Λz_valᵀ * minkowskiMetricReal * Λz_val = minkowskiMetricReal := algebraic_rotation_z_is_lorentz cz sz hcz_sz
    let Λz_inv := algebraic_rotation_z cz (-sz)
    have hz_mul_inv : Λz_val * Λz_inv = 1 := by
      change algebraic_rotation_z cz sz * algebraic_rotation_z cz (-sz) = 1
      ext i j; fin_cases i <;> fin_cases j <;> { simp only [Matrix.mul_apply, Matrix.one_apply]; rw [Fin.sum_univ_four]; simp [algebraic_rotation_z]; try ring_nf; try nlinarith [hcz_sz] }
    have hz_inv_mul : Λz_inv * Λz_val = 1 := by
      change algebraic_rotation_z cz (-sz) * algebraic_rotation_z cz sz = 1
      ext i j; fin_cases i <;> fin_cases j <;> { simp only [Matrix.mul_apply, Matrix.one_apply]; rw [Fin.sum_univ_four]; simp [algebraic_rotation_z]; try ring_nf; try nlinarith [hcz_sz] }
    let Λz : Matrix.GeneralLinearGroup (Fin 4) ℝ := ⟨Λz_val, Λz_inv, hz_mul_inv, hz_inv_mul⟩

    let u' := Λz.val *ᵥ u
    have hu'1 : u' 1 = r12 := by
      change (∑ j : Fin 4, algebraic_rotation_z cz sz 1 j * u j) = r12
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_z cz sz 1 j * u j) = algebraic_rotation_z cz sz 1 0 * u 0 + algebraic_rotation_z cz sz 1 1 * u 1 + algebraic_rotation_z cz sz 1 2 * u 2 + algebraic_rotation_z cz sz 1 3 * u 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum]
      simp [algebraic_rotation_z, cz, sz]
      have hr2 : r12^2 = u 1 ^ 2 + u 2 ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)])
      calc u 1 / r12 * u 1 + -(-u 2 / r12 * u 2)
        _ = (u 1 ^ 2 + u 2 ^ 2) / r12 := by ring
        _ = r12^2 / r12 := by rw [← hr2]
        _ = r12 := by
          have : r12^2 / r12 = r12 * r12 / r12 := by ring
          rw [this, mul_div_cancel_right₀ r12 hr]
    have hu'2 : u' 2 = 0 := by
      change (∑ j : Fin 4, algebraic_rotation_z cz sz 2 j * u j) = 0
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_z cz sz 2 j * u j) = algebraic_rotation_z cz sz 2 0 * u 0 + algebraic_rotation_z cz sz 2 1 * u 1 + algebraic_rotation_z cz sz 2 2 * u 2 + algebraic_rotation_z cz sz 2 3 * u 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum]
      simp [algebraic_rotation_z, cz, sz]
      ring
    have hu'3 : u' 3 = u 3 := by
      change (∑ j : Fin 4, algebraic_rotation_z cz sz 3 j * u j) = u 3
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_z cz sz 3 j * u j) = algebraic_rotation_z cz sz 3 0 * u 0 + algebraic_rotation_z cz sz 3 1 * u 1 + algebraic_rotation_z cz sz 3 2 * u 2 + algebraic_rotation_z cz sz 3 3 * u 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum]
      simp [algebraic_rotation_z]
    have hu'0 : u' 0 = u 0 := by
      change (∑ j : Fin 4, algebraic_rotation_z cz sz 0 j * u j) = u 0
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_z cz sz 0 j * u j) = algebraic_rotation_z cz sz 0 0 * u 0 + algebraic_rotation_z cz sz 0 1 * u 1 + algebraic_rotation_z cz sz 0 2 * u 2 + algebraic_rotation_z cz sz 0 3 * u 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum]
      simp [algebraic_rotation_z]

    let r123 := Real.sqrt (r12 ^ 2 + u 3 ^ 2)
    have hr123 : r123 ≠ 0 := by
      intro h_zero
      have h123 : r12 ^ 2 + u 3 ^ 2 = 0 := le_antisymm (Real.sqrt_eq_zero'.mp h_zero) (by nlinarith [sq_nonneg r12, sq_nonneg (u 3)])
      have hr12_sq : r12 ^ 2 = 0 := by nlinarith [sq_nonneg r12, sq_nonneg (u 3), h123]
      exact hr (sq_eq_zero_iff.mp hr12_sq)

    let cy := -(u 3) / r123
    let sy := r12 / r123
    have hcy_sy : cy^2 + sy^2 = 1 := by
      have hr2 : r123^2 = r12 ^ 2 + u 3 ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg r12, sq_nonneg (u 3)])
      calc cy^2 + sy^2 = (u 3 ^ 2) / r123^2 + (r12 ^ 2) / r123^2 := by ring
        _ = (r12 ^ 2 + u 3 ^ 2) / (r12 ^ 2 + u 3 ^ 2) := by rw [hr2, add_div]; ring
        _ = 1 := div_self (by
          intro h_zero
          have hr_zero : r123^2 = 0 := by rw [hr2, h_zero]
          exact hr123 (sq_eq_zero_iff.mp hr_zero))

    let Λy_val := algebraic_rotation_y cy sy
    have hΛy_lorentz : Λy_valᵀ * minkowskiMetricReal * Λy_val = minkowskiMetricReal := algebraic_rotation_y_is_lorentz cy sy hcy_sy
    let Λy_inv := algebraic_rotation_y cy (-sy)
    have hy_mul_inv : Λy_val * Λy_inv = 1 := by
      change algebraic_rotation_y cy sy * algebraic_rotation_y cy (-sy) = 1
      ext i j; fin_cases i <;> fin_cases j <;> { simp only [Matrix.mul_apply, Matrix.one_apply]; rw [Fin.sum_univ_four]; simp [algebraic_rotation_y]; try ring_nf; try nlinarith [hcy_sy] }
    have hy_inv_mul : Λy_inv * Λy_val = 1 := by
      change algebraic_rotation_y cy (-sy) * algebraic_rotation_y cy sy = 1
      ext i j; fin_cases i <;> fin_cases j <;> { simp only [Matrix.mul_apply, Matrix.one_apply]; rw [Fin.sum_univ_four]; simp [algebraic_rotation_y]; try ring_nf; try nlinarith [hcy_sy] }
    let Λy : Matrix.GeneralLinearGroup (Fin 4) ℝ := ⟨Λy_val, Λy_inv, hy_mul_inv, hy_inv_mul⟩

    let Λ := Λy * Λz
    use Λ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lorentz_mul Λy_val Λz_val hΛy_lorentz hΛz_lorentz
    · change (Λy.val * Λz.val).det = 1
      rw [Matrix.det_mul, algebraic_rotation_y_det cy sy hcy_sy, algebraic_rotation_z_det cz sz hcz_sz, mul_one]
    · have h_mulVec : ↑Λ *ᵥ u = Λy.val *ᵥ u' := by
        change (Λy.val * Λz.val) *ᵥ u = Λy.val *ᵥ (Λz.val *ᵥ u)
        rw [Matrix.mulVec_mulVec]
      rw [h_mulVec]
      change (∑ j : Fin 4, algebraic_rotation_y cy sy 1 j * u' j) = 0
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_y cy sy 1 j * u' j) = algebraic_rotation_y cy sy 1 0 * u' 0 + algebraic_rotation_y cy sy 1 1 * u' 1 + algebraic_rotation_y cy sy 1 2 * u' 2 + algebraic_rotation_y cy sy 1 3 * u' 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum, hu'1, hu'3]
      dsimp [cy, sy]
      simp [algebraic_rotation_y]
      try ring
    · have h_mulVec : ↑Λ *ᵥ u = Λy.val *ᵥ u' := by
        change (Λy.val * Λz.val) *ᵥ u = Λy.val *ᵥ (Λz.val *ᵥ u)
        rw [Matrix.mulVec_mulVec]
      rw [h_mulVec]
      change (∑ j : Fin 4, algebraic_rotation_y cy sy 2 j * u' j) = 0
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_y cy sy 2 j * u' j) = algebraic_rotation_y cy sy 2 0 * u' 0 + algebraic_rotation_y cy sy 2 1 * u' 1 + algebraic_rotation_y cy sy 2 2 * u' 2 + algebraic_rotation_y cy sy 2 3 * u' 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum, hu'2]
      simp [algebraic_rotation_y]
      try ring
    · have h_mulVec : ↑Λ *ᵥ u = Λy.val *ᵥ u' := by
        change (Λy.val * Λz.val) *ᵥ u = Λy.val *ᵥ (Λz.val *ᵥ u)
        rw [Matrix.mulVec_mulVec]
      rw [h_mulVec]
      change (∑ j : Fin 4, algebraic_rotation_y cy sy 0 j * u' j) = u 0
      have eq_sum : (∑ j : Fin 4, algebraic_rotation_y cy sy 0 j * u' j) = algebraic_rotation_y cy sy 0 0 * u' 0 + algebraic_rotation_y cy sy 0 1 * u' 1 + algebraic_rotation_y cy sy 0 2 * u' 2 + algebraic_rotation_y cy sy 0 3 * u' 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum, hu'0]
      simp [algebraic_rotation_y]
    · intro x
      have h_mulVec : ↑Λ *ᵥ x = Λy.val *ᵥ (Λz.val *ᵥ x) := by
        change (Λy.val * Λz.val) *ᵥ x = Λy.val *ᵥ (Λz.val *ᵥ x)
        rw [Matrix.mulVec_mulVec]
      rw [h_mulVec]
      change (∑ j : Fin 4, algebraic_rotation_y cy sy 0 j * (Λz.val *ᵥ x) j) = x 0
      have eq_sum1 : (∑ j : Fin 4, algebraic_rotation_y cy sy 0 j * (Λz.val *ᵥ x) j) = algebraic_rotation_y cy sy 0 0 * (Λz.val *ᵥ x) 0 + algebraic_rotation_y cy sy 0 1 * (Λz.val *ᵥ x) 1 + algebraic_rotation_y cy sy 0 2 * (Λz.val *ᵥ x) 2 + algebraic_rotation_y cy sy 0 3 * (Λz.val *ᵥ x) 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum1]
      simp [algebraic_rotation_y]
      change (∑ j : Fin 4, algebraic_rotation_z cz sz 0 j * x j) = x 0
      have eq_sum2 : (∑ j : Fin 4, algebraic_rotation_z cz sz 0 j * x j) = algebraic_rotation_z cz sz 0 0 * x 0 + algebraic_rotation_z cz sz 0 1 * x 1 + algebraic_rotation_z cz sz 0 2 * x 2 + algebraic_rotation_z cz sz 0 3 * x 3 := by
        repeat rw [Fin.sum_univ_four]
      rw [eq_sum2]
      simp [algebraic_rotation_z]






instance : MulAction (Matrix.GeneralLinearGroup (Fin 4) ℂ) (Fin 4 → ℂ) where
  smul Λ v := (Λ.val : Matrix (Fin 4) (Fin 4) ℂ).mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul Λ₁ Λ₂ v := (Matrix.mulVec_mulVec v Λ₁.val Λ₂.val).symm


instance : MulAction SpecialComplexLorentzGroup (Fin 4 → ℂ) :=
  MulAction.compHom (Fin 4 → ℂ) (Subgroup.subtype SpecialComplexLorentzGroup)

instance : MulAction SpecialSpecialComplexLorentzGroup (Fin 4 → ℂ) :=
  MulAction.compHom (Fin 4 → ℂ) (Subgroup.subtype SpecialSpecialComplexLorentzGroup)


instance lorentz_action_n (n : ℕ) : MulAction SpecialComplexLorentzGroup (Fin n → Fin 4 → ℂ) :=
  Pi.mulAction _

instance special_lorentz_action_n (n : ℕ) : MulAction SpecialSpecialComplexLorentzGroup (Fin n → Fin 4 → ℂ) :=
  Pi.mulAction _


instance : MulAction (Matrix.GeneralLinearGroup (Fin 4) ℝ) (Fin 4 → ℝ) where
  smul Λ v := (Λ.val : Matrix (Fin 4) (Fin 4) ℝ).mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul Λ₁ Λ₂ v := (Matrix.mulVec_mulVec v Λ₁.val Λ₂.val).symm

instance : MulAction RealLorentzGroup (Fin 4 → ℝ) :=
  MulAction.compHom (Fin 4 → ℝ) (Subgroup.subtype RealLorentzGroup)

instance real_lorentz_action_n (n : ℕ) : MulAction RealLorentzGroup (Fin n → Fin 4 → ℝ) :=
  Pi.mulAction _

lemma minkowskiInner_mulVec_eq (R : Matrix (Fin 4) (Fin 4) ℝ)
    (hR : Rᵀ * minkowskiMetricReal * R = minkowskiMetricReal)
    (x y : Fin 4 → ℝ) :
    minkowskiInner (R *ᵥ x) (R *ᵥ y) = minkowskiInner x y := by
  dsimp [minkowskiInner]
  have h1 : dotProduct (R *ᵥ x) (minkowskiMetricReal *ᵥ (R *ᵥ y)) = dotProduct x (Rᵀ *ᵥ (minkowskiMetricReal *ᵥ (R *ᵥ y))) := by
    rw [dotProduct_comm (R *ᵥ x)]
    have h_vecMul := Matrix.dotProduct_mulVec (minkowskiMetricReal *ᵥ (R *ᵥ y)) R x
    rw [h_vecMul]
    rw [dotProduct_comm]
    congr 1
    ext i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct]
    simp_rw [mul_comm]
  rw [h1]
  have h2 : Rᵀ *ᵥ (minkowskiMetricReal *ᵥ (R *ᵥ y)) = (Rᵀ * minkowskiMetricReal * R) *ᵥ y := by
    rw [mulVec_mulVec, mulVec_mulVec]
  rw [h2, hR]

lemma real_lorentz_preserves_forward_cone (R : ProperOrthochronousLorentzGroup)
    (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    R.val.val *ᵥ v ∈ forward_light_cone := by
  dsimp [forward_light_cone] at hv ⊢
  constructor
  · have hR_metric := R.property.1
    have hR_00 := R.property.2.2
    have H_exp : (R.val.val *ᵥ v) 0 = R.val.val 0 0 * v 0 + R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3 := by
      simp [mulVec, dotProduct, Fin.sum_univ_four]
    have ha_sq := lorentz_row_00_sq R.val (lorentz_row_eq R.val hR_metric)
    have hv_sq : (v 0)^2 > (v 1)^2 + (v 2)^2 + (v 3)^2 := by
      have hv_inner := hv.2
      rw [minkowskiInner_explicit] at hv_inner
      linarith
    have hB : (R.val.val 0 1)^2 + (R.val.val 0 2)^2 + (R.val.val 0 3)^2 ≥ 0 := by positivity
    have hD : (v 1)^2 + (v 2)^2 + (v 3)^2 ≥ 0 := by positivity
    have hCS := cauchy_schwarz_3 (R.val.val 0 1) (R.val.val 0 2) (R.val.val 0 3) (v 1) (v 2) (v 3)
    have h1 : (R.val.val 0 0)^2 * (v 0)^2 > ((R.val.val 0 1)^2 + (R.val.val 0 2)^2 + (R.val.val 0 3)^2) * ((v 1)^2 + (v 2)^2 + (v 3)^2) := by
      nlinarith [ha_sq, hv_sq, hB, hD]
    have h2 : (R.val.val 0 0 * v 0)^2 > (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)^2 := by
      calc
        _ = (R.val.val 0 0)^2 * (v 0)^2 := by ring
        _ > ((R.val.val 0 1)^2 + (R.val.val 0 2)^2 + (R.val.val 0 3)^2) * ((v 1)^2 + (v 2)^2 + (v 3)^2) := h1
        _ ≥ (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)^2 := hCS
    have h3 : R.val.val 0 0 * v 0 > 0 := mul_pos hR_00 hv.1
    have h4 : (R.val.val 0 0 * v 0)^2 - (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)^2 > 0 := by linarith
    have h5 : (R.val.val 0 0 * v 0 - (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)) * (R.val.val 0 0 * v 0 + (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)) > 0 := by
      calc
        _ = (R.val.val 0 0 * v 0)^2 - (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3)^2 := by ring
        _ > 0 := h4
    rcases mul_pos_iff.mp h5 with ⟨hA, hB_pos⟩ | ⟨hA, hB_pos⟩
    · rw [H_exp]
      linarith
    · have h_contra : R.val.val 0 0 * v 0 - (R.val.val 0 1 * v 1 + R.val.val 0 2 * v 2 + R.val.val 0 3 * v 3) > 0 := by linarith
      linarith
  · have hR_metric := R.property.1
    have h1 := minkowskiInner_mulVec_eq R.val.val hR_metric v v
    rw [h1]
    exact hv.2

lemma minkowskiMetric_eq_map : minkowskiMetric = RingHom.mapMatrix (algebraMap ℝ ℂ) minkowskiMetricReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiMetric, minkowskiMetricReal]


noncomputable def real_to_complex_lorentz (Λ : ProperOrthochronousLorentzGroup) : SpecialSpecialComplexLorentzGroup :=
  ⟨⟨RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val,
    RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.inv,
    by
      rw [←RingHom.map_mul]
      have h2 : Λ.val.val * Λ.val.inv = 1 := Λ.val.val_inv
      rw [h2, RingHom.map_one],
    by
      rw [←RingHom.map_mul]
      have h2 : Λ.val.inv * Λ.val.val = 1 := Λ.val.inv_val
      rw [h2, RingHom.map_one]⟩,
    by
      have ht : Matrix.transpose (RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val) = RingHom.mapMatrix (algebraMap ℝ ℂ) (Matrix.transpose Λ.val.val) := by rfl
      have h1 : Matrix.transpose (RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val) * minkowskiMetric * RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val = minkowskiMetric := by
        rw [minkowskiMetric_eq_map, ht, ←RingHom.map_mul, ←RingHom.map_mul]
        have hL : Matrix.transpose Λ.val.val * minkowskiMetricReal * Λ.val.val = minkowskiMetricReal := Λ.property.1
        rw [hL]
      have h2 : (RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val).det = 1 := by
        have hd1 : (RingHom.mapMatrix (algebraMap ℝ ℂ) Λ.val.val).det = (algebraMap ℝ ℂ) (Λ.val.val.det) := (RingHom.map_det (algebraMap ℝ ℂ) Λ.val.val).symm
        rw [hd1]
        have hd2 : Λ.val.val.det = 1 := Λ.property.2.1
        rw [hd2]
        exact RingHom.map_one _
      exact ⟨h1, h2⟩⟩


noncomputable def real_lorentz_action_complex_n (n : ℕ) (Λ : ProperOrthochronousLorentzGroup) (z : Fin n → Fin 4 → ℂ) : Fin n → Fin 4 → ℂ :=
  (real_to_complex_lorentz Λ) • z


def is_real_lorentz_invariant_n (n : ℕ) (f : (Fin n → Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ (Λ : ProperOrthochronousLorentzGroup) (z : Fin n → Fin 4 → ℂ),
    f (real_lorentz_action_complex_n n Λ z) = f z


def is_complex_lorentz_invariant_n (n : ℕ) (F : (Fin n → Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ (Λ : SpecialSpecialComplexLorentzGroup) (z : Fin n → Fin 4 → ℂ),
    F (Λ • z) = F z

def orbit_domain (n : ℕ) (z : Fin n → Fin 4 → ℂ) : Set SpecialSpecialComplexLorentzGroup :=
  { Λ | Λ • z ∈ forward_tube_n n }

end Geometry
