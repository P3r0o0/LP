import Minkowski
import RealGivens
import Spinor
import PolarPlan
import MatrixAnalysis
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Algebra.Exponential
import Lightcone
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Geometry.PolarDecomposition
open Complex Matrix Geometry Geometry.SpinorTopology Geometry.RealGivens Geometry.MatrixAnalysis
open scoped Matrix ComplexOrder











lemma diag_matrix_sq (b : ℂ) (hb : b ≠ 0) :
    (diag_matrix b hb) * (diag_matrix b hb) = diag_matrix (b * b) (mul_ne_zero hb hb) := by
  apply Subtype.ext
  ext i j
  simp [diag_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases i <;> fin_cases j <;> norm_num

lemma jordan_matrix_sq (c : ℂ) :
    (jordan_matrix c) * (jordan_matrix c) = jordan_matrix (c + c) := by
  apply Subtype.ext
  ext i j
  change ((J_mat c) * (J_mat c)) i j = (J_mat (c + c)) i j
  dsimp [J_mat, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

lemma sl2c_exists_sq_diag (P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (ha : a ≠ 0) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      (P * P = P_c * diag_matrix a ha * P_c⁻¹ ∨ P * P = -(P_c * diag_matrix a ha * P_c⁻¹)) ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  have h_sqrt : ∃ b : ℂ, b * b = a := by
    have := IsAlgClosed.exists_pow_nat_eq a zero_lt_two
    rcases this with ⟨b, hb⟩
    use b
    have hb2 : b * b = b ^ 2 := by ring
    rw [hb2]
    exact hb
  rcases h_sqrt with ⟨b, hb⟩
  have hb_ne : b ≠ 0 := by intro h; rw [h, mul_zero] at hb; exact ha hb.symm
  let P_diag : SpecialLinearGroup (Fin 2) ℂ := diag_matrix b hb_ne
  use P_c * P_diag * P_c⁻¹
  use P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val
  constructor
  · left
    calc
      (P_c * P_diag * P_c⁻¹) * (P_c * P_diag * P_c⁻¹)
        = P_c * (P_diag * P_diag) * P_c⁻¹ := by group
      _ = P_c * (diag_matrix (b * b) (mul_ne_zero hb_ne hb_ne)) * P_c⁻¹ := by rw [diag_matrix_sq b hb_ne]
      _ = P_c * (diag_matrix a ha) * P_c⁻¹ := by
            have h_b_sq : b * b = a := hb
            have h_eq : diag_matrix (b * b) (mul_ne_zero hb_ne hb_ne) = diag_matrix a ha := by
              ext i j
              dsimp [diag_matrix]
              rw [h_b_sq]
            rw [h_eq]
  · constructor
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_conj := exp_conj_matrix P_c.val (Matrix.diagonal ![Complex.log b, -Complex.log b]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
      rw [h_conj]
      have h_exp_neg : cexp (-Complex.log b) = b⁻¹ := by rw [Complex.exp_neg, Complex.exp_log hb_ne]
      have h_exp_diag : NormedSpace.exp (Matrix.diagonal ![Complex.log b, -Complex.log b]) = Matrix.diagonal ![b, b⁻¹] := by
        rw [MatrixAnalysis.exp_diagonal]
        ext i j
        simp [ Matrix.diagonal, Matrix.of_apply, ← Complex.exp_eq_exp_ℂ]
        fin_cases i <;> fin_cases j <;> simp [Complex.exp_log hb_ne, h_exp_neg]
      rw [h_exp_diag]
      ext i j
      dsimp [P_diag, diag_matrix]
      rfl
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_trace_conj : (P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val).trace = (Matrix.diagonal ![Complex.log b, -Complex.log b]).trace := by
        calc (P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val).trace
           = (P_c.val * (Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
         _ = ((Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
         _ = (Matrix.diagonal ![Complex.log b, -Complex.log b] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
         _ = (Matrix.diagonal ![Complex.log b, -Complex.log b]).trace := by rw [P_c_inv_mul, Matrix.mul_one]
      rw [h_trace_conj]
      simp [Matrix.trace_diagonal, Fin.sum_univ_two]

lemma sl2c_exists_sq_jor1 (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      (P * P = P_c * jordan_matrix c * P_c⁻¹ ∨ P * P = -(P_c * jordan_matrix c * P_c⁻¹)) ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  let P_jor : SpecialLinearGroup (Fin 2) ℂ := jordan_matrix (c / 2)
  use P_c * P_jor * P_c⁻¹
  use P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val
  constructor
  · left
    calc
      (P_c * P_jor * P_c⁻¹) * (P_c * P_jor * P_c⁻¹)
        = P_c * (P_jor * P_jor) * P_c⁻¹ := by group
      _ = P_c * (jordan_matrix (c / 2 + c / 2)) * P_c⁻¹ := by rw [jordan_matrix_sq (c / 2)]
      _ = P_c * (jordan_matrix c) * P_c⁻¹ := by
            have h_eq : c / 2 + c / 2 = c := by ring
            rw [h_eq]
  · constructor
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_conj := exp_conj_matrix P_c.val (Matrix.of ![![0, c / 2], ![0, 0]]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
      rw [h_conj]
      have h_nilp : (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = 0 := by
        rw [pow_succ, pow_succ, pow_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.zero_apply] <;> ring
      have h_exp_jor : NormedSpace.exp (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) = jordan_matrix (c / 2) := by
        rw [exp_of_nilpotent3 _ h_nilp]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [pow_two, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring
      rw [h_exp_jor]
      ext i j
      dsimp [P_jor, jordan_matrix]
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_trace_conj : (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by
        calc (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace
           = (P_c.val * (Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
         _ = ((Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
         _ = (Matrix.of ![![0, c / 2], ![0, 0]] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
         _ = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by rw [P_c_inv_mul, Matrix.mul_one]
      rw [h_trace_conj]
      simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma sl2c_exists_sq_jor_neg1 (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      (P * P = P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹ ∨
       P * P = -(P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹)) ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  let P_jor : SpecialLinearGroup (Fin 2) ℂ := jordan_matrix (c / 2)
  use P_c * P_jor * P_c⁻¹
  use P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val
  constructor
  · right
    calc
      (P_c * P_jor * P_c⁻¹) * (P_c * P_jor * P_c⁻¹)
        = P_c * (P_jor * P_jor) * P_c⁻¹ := by group
      _ = P_c * (jordan_matrix (c / 2 + c / 2)) * P_c⁻¹ := by rw [jordan_matrix_sq (c / 2)]
      _ = P_c * (jordan_matrix c) * P_c⁻¹ := by
            have h_eq : c / 2 + c / 2 = c := by ring
            rw [h_eq]
      _ = P_c * (- (diag_matrix (-1) (by norm_num) * jordan_matrix c)) * P_c⁻¹ := by
            have h_eq : jordan_matrix c = - (diag_matrix (-1) (by norm_num) * jordan_matrix c) := by
              apply Subtype.ext
              ext i j
              dsimp [jordan_matrix, diag_matrix, J_mat, Matrix.mul_apply]
              fin_cases i <;> fin_cases j <;> norm_num <;> ring
            have h_eq2 : P_c * (jordan_matrix c) * P_c⁻¹ = P_c * (- (diag_matrix (-1) (by norm_num) * jordan_matrix c)) * P_c⁻¹ :=
              congrArg (fun X => P_c * X * P_c⁻¹) h_eq
            exact h_eq2
      _ = - (P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹) := by
            have h_eq : P_c * -(diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹ = - (P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹) := by
              apply Subtype.ext
              simp
            rw [h_eq]
  · constructor
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_conj := exp_conj_matrix P_c.val (Matrix.of ![![0, c / 2], ![0, 0]]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
      rw [h_conj]
      have h_nilp : (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = 0 := by
        rw [pow_succ, pow_succ, pow_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.zero_apply] <;> ring
      have h_exp_jor : NormedSpace.exp (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) = jordan_matrix (c / 2) := by
        rw [exp_of_nilpotent3 _ h_nilp]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [pow_two, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring
      rw [h_exp_jor]
      ext i j
      dsimp [P_jor, jordan_matrix]
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have h_trace_conj : (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by
        calc (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace
           = (P_c.val * (Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
         _ = ((Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
         _ = (Matrix.of ![![0, c / 2], ![0, 0]] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
         _ = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by rw [P_c_inv_mul, Matrix.mul_one]
      rw [h_trace_conj]
      simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma sl2c_exists_sq_or_neg_sq (C : SpecialLinearGroup (Fin 2) ℂ) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      (P * P = C ∨ P * P = -C) ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  have h_class := sl2c_classification C
  rcases h_class with ⟨P_c, a, ha, h_diag⟩ | ⟨P_c, ε, hε, c, h_jor⟩
  · 
    have h_diag_case := sl2c_exists_sq_diag P_c a ha
    rcases h_diag_case with ⟨P, H, h_sq_eq, h_P_exp, h_H_tr⟩
    use P, H
    constructor
    · rcases h_sq_eq with h_pos | h_neg
      · left; rw [h_pos]; exact h_diag.symm
      · right; rw [h_neg]; exact congrArg (fun X => -X) h_diag.symm
    · exact ⟨h_P_exp, h_H_tr⟩
  · 
    rcases hε with h1 | h_1
    · 
      have h_jor_case := sl2c_exists_sq_jor1 P_c c
      rcases h_jor_case with ⟨P, H, h_sq_eq, h_P_exp, h_H_tr⟩
      use P, H
      constructor
      · rcases h_sq_eq with h_pos | h_neg
        · left
          rw [h_pos]
          subst h1
          have h_eq : diag_matrix 1 (by norm_num) = 1 := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [diag_matrix]
          have h_jor_rw : P_c * (diag_matrix 1 (by norm_num) * jordan_matrix c) * P_c⁻¹ = P_c * (jordan_matrix c) * P_c⁻¹ := by rw [h_eq, one_mul]
          rw [← h_jor_rw]
          exact h_jor.symm
        · right
          rw [h_neg]
          subst h1
          have h_eq : diag_matrix 1 (by norm_num) = 1 := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [diag_matrix]
          have h_jor_rw : P_c * (diag_matrix 1 (by norm_num) * jordan_matrix c) * P_c⁻¹ = P_c * (jordan_matrix c) * P_c⁻¹ := by rw [h_eq, one_mul]
          rw [← h_jor_rw]
          exact congrArg (fun X => -X) h_jor.symm
      · exact ⟨h_P_exp, h_H_tr⟩
    · 
      have h_jor_neg_case := sl2c_exists_sq_jor_neg1 P_c c
      rcases h_jor_neg_case with ⟨P, H, h_sq_eq, h_P_exp, h_H_tr⟩
      use P, H
      constructor
      · rcases h_sq_eq with h_pos | h_neg
        · left; rw [h_pos]; subst h_1; exact h_jor.symm
        · right; rw [h_neg]; subst h_1; exact congrArg (fun X => -X) h_jor.symm
      · exact ⟨h_P_exp, h_H_tr⟩



lemma spinorPhi_neg_left (A B : SpecialLinearGroup (Fin 2) ℂ) :
    (spinorPhi (-A, B)).val = - (spinorPhi (A, B)).val := by
  ext i j
  change spinorPhi_matrix (-A) B i j = - (spinorPhi_matrix A B i j)
  rw [spinorPhi_matrix_apply, spinorPhi_matrix_apply]
  dsimp [spinor_action]
  fin_cases i <;> simp <;> ring


lemma spinorPhi_neg_neg (A B : SpecialLinearGroup (Fin 2) ℂ) :
    spinorPhi (-A, -B) = spinorPhi (A, B) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change spinorPhi_matrix (-A) (-B) i j = spinorPhi_matrix A B i j
  rw [spinorPhi_matrix_apply, spinorPhi_matrix_apply]
  dsimp [spinor_action]
  fin_cases i <;> simp <;> ring

lemma sl2c_conj_neg (A : SpecialLinearGroup (Fin 2) ℂ) :
    sl2c_conj (-A) = -sl2c_conj A := by
  apply Subtype.ext
  ext i j
  simp [sl2c_conj]

lemma sl_inv_neg (A : SpecialLinearGroup (Fin 2) ℂ) : (-A)⁻¹ = -A⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])

lemma spinorPhi_neg_conj (P : SpecialLinearGroup (Fin 2) ℂ) :
    spinorPhi (-P, (sl2c_conj (-P))⁻¹) = spinorPhi (P, (sl2c_conj P)⁻¹) := by
  rw [sl2c_conj_neg, sl_inv_neg]
  exact spinorPhi_neg_neg _ _


noncomputable def sl2c_lie_to_lorentz_lie (H : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let a := H 0 0
  let b := H 0 1
  let c := H 1 0
  let x1 := ((b + c) / 2).re
  let y1 := ((b + c) / 2).im
  let x2 := (-(b - c) / 2).im
  let y2 := ((b - c) / 2).re
  let x3 := a.re
  let y3 := a.im
  !![ 0,  x1,  x2,  x3;
      x1,  0, -y3,  y2;
      x2,  y3,  0, -y1;
      x3, -y2,  y1,  0 ]

lemma sl2c_lie_to_lorentz_lie_mem (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (sl2c_lie_to_lorentz_lie H)ᵀ * minkowskiMetricReal + minkowskiMetricReal * (sl2c_lie_to_lorentz_lie H) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [Matrix.mul_apply, Matrix.transpose, Fin.sum_univ_succ, sl2c_lie_to_lorentz_lie, minkowskiMetricReal]
    try ring


noncomputable def sl2c_lie_to_lorentz_lie_alg (H : Matrix (Fin 2) (Fin 2) ℂ) : RealLorentzLieAlgebra :=
  ⟨sl2c_lie_to_lorentz_lie H, sl2c_lie_to_lorentz_lie_mem H⟩

noncomputable def cosh_w (w : ℂ) : ℂ := (Complex.exp w + Complex.exp (-w)) / 2
noncomputable def sinch_w (w : ℂ) : ℂ := if w = 0 then 1 else (Complex.exp w - Complex.exp (-w)) / (2 * w)

lemma P_inv_conjTranspose_mul_u_ne_zero (P : SpecialLinearGroup (Fin 2) ℂ) : (P.val⁻¹)ᴴ *ᵥ ![0, 1] ≠ 0 := by
  intro h
  let P_val := P.val
  let P_inv := (P_val)⁻¹
  have h_det_P : P_val.det = 1 := P.property
  have h_P_isUnit : IsUnit P_val.det := by rw [h_det_P]; exact isUnit_one
  have h_v_P : P_valᴴ *ᵥ (P_invᴴ *ᵥ ![0, 1]) = ![0, 1] := by
    have h2 : P_valᴴ *ᵥ (P_invᴴ *ᵥ ![0, 1]) = (P_valᴴ * P_invᴴ) *ᵥ ![0, 1] := Matrix.mulVec_mulVec _ _ _
    rw [h2]
    have h_mul : P_valᴴ * P_invᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ h_P_isUnit, Matrix.conjTranspose_one]
    rw [h_mul, Matrix.one_mulVec]
  have h_zero : P_valᴴ *ᵥ (P_invᴴ *ᵥ ![0, 1]) = 0 := by
    rw [h, Matrix.mulVec_zero]
  rw [h_zero] at h_v_P
  have h1 : (0 : ℂ) = (![0, 1] : Fin 2 → ℂ) 1 := congr_fun h_v_P 1
  simp at h1

lemma C_conjTranspose_mul_v (C : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (P : SpecialLinearGroup (Fin 2) ℂ)
    (hC : C = P.val * !![(-1 : ℂ), c; 0, -1] * (P.val)⁻¹) (v : Fin 2 → ℂ)
    (hv : v = (P.val⁻¹)ᴴ *ᵥ ![0, 1]) : Cᴴ *ᵥ v = -v := by
  let P_val := P.val
  let P_inv := (P_val)⁻¹
  have h_det_P : P_val.det = 1 := P.property
  have h_P_isUnit : IsUnit P_val.det := by rw [h_det_P]; exact isUnit_one
  have hCH : Cᴴ = P_invᴴ * !![(-1 : ℂ), c; 0, -1]ᴴ * P_valᴴ := by
    rw [hC, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h_PC : Cᴴ *ᵥ v = P_invᴴ *ᵥ (!![(-1 : ℂ), c; 0, -1]ᴴ *ᵥ ![0, 1]) := by
    rw [hCH, hv]
    have h1 : (P_invᴴ * !![(-1 : ℂ), c; 0, -1]ᴴ * P_valᴴ) *ᵥ (P_invᴴ *ᵥ ![0, 1]) =
              ((P_invᴴ * !![(-1 : ℂ), c; 0, -1]ᴴ * P_valᴴ) * P_invᴴ) *ᵥ ![0, 1] := Matrix.mulVec_mulVec _ _ _
    rw [h1]
    have h_assoc : P_valᴴ * P_invᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ h_P_isUnit, Matrix.conjTranspose_one]
    have h_assoc2 : (P_invᴴ * !![(-1 : ℂ), c; 0, -1]ᴴ * P_valᴴ) * P_invᴴ = P_invᴴ * !![(-1 : ℂ), c; 0, -1]ᴴ := by
      rw [Matrix.mul_assoc, h_assoc, Matrix.mul_one]
    rw [h_assoc2]
    exact (Matrix.mulVec_mulVec _ _ _).symm
  rw [h_PC]
  have h_uJ : !![(-1 : ℂ), c; 0, -1]ᴴ *ᵥ ![0, 1] = -![0, 1] := by
    ext i
    fin_cases i <;> simp [Matrix.conjTranspose, Matrix.transpose, Matrix.map_apply, mulVec, dotProduct]
  rw [h_uJ]
  have h_neg : P_invᴴ *ᵥ (-![0, 1]) = -(P_invᴴ *ᵥ ![0, 1]) := Matrix.mulVec_neg ![0, 1] P_invᴴ
  rw [h_neg, ← hv]

lemma star_v_mul_C (C : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) (hvC : Cᴴ *ᵥ v = -v) :
    star v ᵥ* C = - star v := by
  have h_star : star (Cᴴ *ᵥ v) = star (-v) := by rw [hvC]
  rw [star_neg, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose] at h_star
  exact h_star

lemma neg_two_star_v_X_v (C X : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ)
    (hvC : Cᴴ *ᵥ v = -v) (h_star_v_C : star v ᵥ* C = -star v) :
    star v ⬝ᵥ ( ( (1/2 : ℂ) • (C * X + X * Cᴴ) ) *ᵥ v) = - (star v ⬝ᵥ (X *ᵥ v)) := by
  have h1 : ((1/2 : ℂ) • (C * X + X * Cᴴ)) *ᵥ v = (1/2 : ℂ) • ((C * X + X * Cᴴ) *ᵥ v) := Matrix.smul_mulVec _ _ _
  have h_mulW : star v ⬝ᵥ ( ( (1/2 : ℂ) • (C * X + X * Cᴴ) ) *ᵥ v) =
    (1/2 : ℂ) * ( star v ⬝ᵥ ((C * X) *ᵥ v) + star v ⬝ᵥ ((X * Cᴴ) *ᵥ v) ) := by
    rw [h1]
    have h2 : (C * X + X * Cᴴ) *ᵥ v = (C * X) *ᵥ v + (X * Cᴴ) *ᵥ v := Matrix.add_mulVec _ _ _
    rw [h2]
    have h3 : star v ⬝ᵥ ((1 / 2 : ℂ) • ((C * X) *ᵥ v + (X * Cᴴ) *ᵥ v)) = (1 / 2 : ℂ) * (star v ⬝ᵥ ((C * X) *ᵥ v + (X * Cᴴ) *ᵥ v)) := dotProduct_smul _ _ _
    rw [h3, dotProduct_add]
  have h_CX : star v ⬝ᵥ ((C * X) *ᵥ v) = - (star v ⬝ᵥ (X *ᵥ v)) := by
    have h2 : (C * X) *ᵥ v = C *ᵥ (X *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [h2, Matrix.dotProduct_mulVec, h_star_v_C, neg_dotProduct]
  have h_XC : star v ⬝ᵥ ((X * Cᴴ) *ᵥ v) = - (star v ⬝ᵥ (X *ᵥ v)) := by
    have h2 : (X * Cᴴ) *ᵥ v = X *ᵥ (Cᴴ *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [h2, hvC, Matrix.mulVec_neg, dotProduct_neg]
  rw [h_CX, h_XC] at h_mulW
  have h_calc : (1 / 2 : ℂ) * (- (star v ⬝ᵥ (X *ᵥ v)) + - (star v ⬝ᵥ (X *ᵥ v))) = - (star v ⬝ᵥ (X *ᵥ v)) := by ring
  rw [h_calc] at h_mulW
  exact h_mulW

lemma neg_I_half_star_v_Y_v (C Y : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ)
    (hvC : Cᴴ *ᵥ v = -v) (h_star_v_C : star v ᵥ* C = -star v) :
    star v ⬝ᵥ ( ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) ) *ᵥ v) = 0 := by
  have h1 : (( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) )) *ᵥ v = (-I / 2 : ℂ) • ((C * Y - Y * Cᴴ) *ᵥ v) := Matrix.smul_mulVec _ _ _
  have h_mulW : star v ⬝ᵥ ( ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) ) *ᵥ v) =
    (-I / 2 : ℂ) * ( star v ⬝ᵥ ((C * Y) *ᵥ v) - star v ⬝ᵥ ((Y * Cᴴ) *ᵥ v) ) := by
    rw [h1]
    have h2 : (C * Y - Y * Cᴴ) *ᵥ v = (C * Y) *ᵥ v - (Y * Cᴴ) *ᵥ v := Matrix.sub_mulVec _ _ _
    rw [h2]
    have h3 : star v ⬝ᵥ ((-I / 2 : ℂ) • ((C * Y) *ᵥ v - (Y * Cᴴ) *ᵥ v)) = (-I / 2 : ℂ) * (star v ⬝ᵥ ((C * Y) *ᵥ v - (Y * Cᴴ) *ᵥ v)) := dotProduct_smul _ _ _
    rw [h3, dotProduct_sub]
  have h_CY : star v ⬝ᵥ ((C * Y) *ᵥ v) = - (star v ⬝ᵥ (Y *ᵥ v)) := by
    have h2 : (C * Y) *ᵥ v = C *ᵥ (Y *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [h2, Matrix.dotProduct_mulVec, h_star_v_C, neg_dotProduct]
  have h_YC : star v ⬝ᵥ ((Y * Cᴴ) *ᵥ v) = - (star v ⬝ᵥ (Y *ᵥ v)) := by
    have h2 : (Y * Cᴴ) *ᵥ v = Y *ᵥ (Cᴴ *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [h2, hvC, Matrix.mulVec_neg, dotProduct_neg]
  rw [h_CY, h_YC] at h_mulW
  have h_calc : (-I / 2 : ℂ) * (- (star v ⬝ᵥ (Y *ᵥ v)) - - (star v ⬝ᵥ (Y *ᵥ v))) = 0 := by ring
  rw [h_calc] at h_mulW
  exact h_mulW

lemma no_tube_preserver_trace_neg_two_proof (C X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.PosDef) (hY : Y.IsHermitian) (c : ℂ) (P : SpecialLinearGroup (Fin 2) ℂ)
    (hC : C = P.val * !![(-1 : ℂ), c; 0, -1] * (P.val)⁻¹) :
    ¬ ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) + (1/2 : ℂ) • (C * X + X * Cᴴ) ).PosDef := by
  intro hW
  let v := (P.val⁻¹)ᴴ *ᵥ ![0, 1]
  have hv_ne_zero : v ≠ 0 := P_inv_conjTranspose_mul_u_ne_zero P
  have hvC : Cᴴ *ᵥ v = -v := C_conjTranspose_mul_v C c P hC v rfl
  have h_star_v_C : star v ᵥ* C = -star v := star_v_mul_C C v hvC

  have h_W_pos := hW.dotProduct_mulVec_pos hv_ne_zero
  have h_X_pos := hX.dotProduct_mulVec_pos hv_ne_zero

  have h_eval_X : star v ⬝ᵥ ( ( (1/2 : ℂ) • (C * X + X * Cᴴ) ) *ᵥ v) = - (star v ⬝ᵥ (X *ᵥ v)) :=
    neg_two_star_v_X_v C X v hvC h_star_v_C

  have h_eval_Y : star v ⬝ᵥ ( ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) ) *ᵥ v) = 0 :=
    neg_I_half_star_v_Y_v C Y v hvC h_star_v_C

  have h_W_split : star v ⬝ᵥ ( ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) + (1/2 : ℂ) • (C * X + X * Cᴴ) ) *ᵥ v) =
    star v ⬝ᵥ ( ( (-I / 2 : ℂ) • (C * Y - Y * Cᴴ) ) *ᵥ v) + star v ⬝ᵥ ( ( (1/2 : ℂ) • (C * X + X * Cᴴ) ) *ᵥ v) := by
    rw [Matrix.add_mulVec, dotProduct_add]

  rw [h_eval_Y, h_eval_X, zero_add] at h_W_split
  rw [h_W_split] at h_W_pos

  have h_contra : 0 < - (star v ⬝ᵥ X *ᵥ v) := h_W_pos
  have h_contra2 : star v ⬝ᵥ X *ᵥ v < 0 := neg_pos.mp h_contra

  have h_trans : (0 : ℂ) < 0 := LT.lt.trans h_X_pos h_contra2
  exact lt_irrefl 0 h_trans

lemma M11_eq_of_trace_neg_two (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M.trace = -2) : M 1 1 = -2 - M 0 0 := by
  have h1 : M 0 0 + M 1 1 = M.trace := by simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have h2 : M 0 0 + M 1 1 = -2 := by rw [h1, h]
  calc M 1 1 = -M 0 0 + (M 0 0 + M 1 1) := by ring
    _ = -M 0 0 + -2 := by rw [h2]
    _ = -2 - M 0 0 := by ring

lemma M10_eq_of_det_one_trace_neg_two (M : Matrix (Fin 2) (Fin 2) ℂ) (h_det : M.det = 1) (h_tr : M.trace = -2) (h01 : M 0 1 ≠ 0) :
    M 1 0 = (- (M 0 0)^2 - 2 * M 0 0 - 1) * (M 0 1)⁻¹ := by
  have h11 := M11_eq_of_trace_neg_two M h_tr
  have h1 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = M.det := by simp [Matrix.det_fin_two]
  have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [h1, h_det]
  have h3 : M 0 1 * M 1 0 = M 0 0 * M 1 1 - 1 := by
    calc M 0 1 * M 1 0 = M 0 0 * M 1 1 - (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by ring
      _ = M 0 0 * M 1 1 - 1 := by rw [h2]
  have h4 : M 0 1 * M 1 0 = - (M 0 0)^2 - 2 * M 0 0 - 1 := by
    calc M 0 1 * M 1 0 = M 0 0 * (-2 - M 0 0) - 1 := by rw [h3, h11]
      _ = - (M 0 0)^2 - 2 * M 0 0 - 1 := by ring
  calc M 1 0 = 1 * M 1 0 := by ring
    _ = ((M 0 1)⁻¹ * M 0 1) * M 1 0 := by rw [inv_mul_cancel₀ h01]
    _ = (M 0 1)⁻¹ * (M 0 1 * M 1 0) := by rw [mul_assoc]
    _ = (M 0 1)⁻¹ * (- (M 0 0)^2 - 2 * M 0 0 - 1) := by rw [h4]
    _ = (- (M 0 0)^2 - 2 * M 0 0 - 1) * (M 0 1)⁻¹ := by ring

lemma P_det_eq_one (M : Matrix (Fin 2) (Fin 2) ℂ) (h01 : M 0 1 ≠ 0) :
    !![M 0 1, 0; M 1 1 + 1, (M 0 1)⁻¹].det = 1 := by
  have h_mul : M 0 1 * (M 0 1)⁻¹ = 1 := mul_inv_cancel₀ h01
  calc !![M 0 1, 0; M 1 1 + 1, (M 0 1)⁻¹].det = M 0 1 * (M 0 1)⁻¹ - 0 * (M 1 1 + 1) := by simp [Matrix.det_fin_two]
    _ = M 0 1 * (M 0 1)⁻¹ := by ring
    _ = 1 := h_mul

lemma P_mul_J_eq_M_mul_P (M : Matrix (Fin 2) (Fin 2) ℂ) (h_det : M.det = 1) (h_tr : M.trace = -2) (h01 : M 0 1 ≠ 0) :
    M * !![M 0 1, 0; M 1 1 + 1, (M 0 1)⁻¹] = !![M 0 1, 0; M 1 1 + 1, (M 0 1)⁻¹] * !![(-1 : ℂ), (M 0 1)⁻¹; 0, -1] := by
  have h11 := M11_eq_of_trace_neg_two M h_tr
  have h10 := M10_eq_of_det_one_trace_neg_two M h_det h_tr h01
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    try rw [h11]
    try ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h_step : M 1 0 * M 0 1 + M 1 1 * (M 1 1 + 1) = (- (M 0 0)^2 - 2 * M 0 0 - 1) * (M 0 1)⁻¹ * M 0 1 + (-2 - M 0 0) * (-2 - M 0 0 + 1) := by rw [h10, h11]
    rw [h_step]
    have h_mul : (M 0 1)⁻¹ * M 0 1 = 1 := inv_mul_cancel₀ h01
    calc (- (M 0 0)^2 - 2 * M 0 0 - 1) * (M 0 1)⁻¹ * M 0 1 + (-2 - M 0 0) * (-2 - M 0 0 + 1)
      = (- (M 0 0)^2 - 2 * M 0 0 - 1) * ( (M 0 1)⁻¹ * M 0 1 ) + (-2 - M 0 0) * (-2 - M 0 0 + 1) := by ring
      _ = (- (M 0 0)^2 - 2 * M 0 0 - 1) * 1 + (-2 - M 0 0) * (-2 - M 0 0 + 1) := by rw [h_mul]
      _ = M 0 0 + 1 := by ring
      _ = - (-2 - M 0 0) - 1 := by ring
      _ = - M 1 1 - 1 := by rw [← h11]
      _ = -1 + - M 1 1 := by ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring

lemma jordan_form_case1 (C : SpecialLinearGroup (Fin 2) ℂ) (h_tr : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace = -2) (h_ne : C ≠ -1) (h01 : (C.val : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ), (C.val : Matrix (Fin 2) (Fin 2) ℂ) = P.val * !![(-1 : ℂ), c; 0, -1] * P.val⁻¹ := by
  let M := (C.val : Matrix (Fin 2) (Fin 2) ℂ)
  have h_det : M.det = 1 := C.property
  let P_val : Matrix (Fin 2) (Fin 2) ℂ := !![M 0 1, 0; M 1 1 + 1, (M 0 1)⁻¹]
  have hP_det : P_val.det = 1 := P_det_eq_one M h01
  let P : SpecialLinearGroup (Fin 2) ℂ := ⟨P_val, hP_det⟩
  let c : ℂ := (M 0 1)⁻¹
  use P, c
  have h_mul_P : M * P_val = P_val * !![(-1 : ℂ), c; 0, -1] := P_mul_J_eq_M_mul_P M h_det h_tr h01
  have h_unit : IsUnit P_val.det := by rw [hP_det]; exact isUnit_one
  calc (C.val : Matrix (Fin 2) (Fin 2) ℂ) = M := rfl
    _ = M * 1 := by rw [Matrix.mul_one]
    _ = M * (P_val * P_val⁻¹) := by rw [Matrix.mul_nonsing_inv P_val h_unit]
    _ = M * P_val * P_val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P_val * !![(-1 : ℂ), c; 0, -1] * P_val⁻¹ := by rw [h_mul_P]

lemma jordan_form_case2 (C : SpecialLinearGroup (Fin 2) ℂ) (h_tr : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace = -2) (h_ne : C ≠ -1) (h01 : (C.val : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ), (C.val : Matrix (Fin 2) (Fin 2) ℂ) = P.val * !![(-1 : ℂ), c; 0, -1] * P.val⁻¹ := by
  let M := (C.val : Matrix (Fin 2) (Fin 2) ℂ)
  have h01' : M 0 1 = 0 := h01
  have h_det : M.det = 1 := C.property
  have h11 := M11_eq_of_trace_neg_two M h_tr
  have h_det2 : M 0 0 * M 1 1 - 0 * M 1 0 = 1 := by
    calc M 0 0 * M 1 1 - 0 * M 1 0 = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by rw [h01']
      _ = M.det := by simp [Matrix.det_fin_two]
      _ = 1 := h_det
  have h_M00 : M 0 0 = -1 := by
    have h : M 0 0 * (-2 - M 0 0) - 0 * M 1 0 = 1 := by
      calc M 0 0 * (-2 - M 0 0) - 0 * M 1 0 = M 0 0 * M 1 1 - 0 * M 1 0 := by rw [h11]
        _ = 1 := h_det2
    have h2 : - (M 0 0)^2 - 2 * M 0 0 - 1 = 0 := by
      calc - (M 0 0)^2 - 2 * M 0 0 - 1 = M 0 0 * (-2 - M 0 0) - 0 * M 1 0 - 1 := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by ring
    have h3 : - (M 0 0 + 1)^2 = 0 := by
      calc - (M 0 0 + 1)^2 = - (M 0 0)^2 - 2 * M 0 0 - 1 := by ring
        _ = 0 := h2
    have h4 : (M 0 0 + 1)^2 = 0 := by
      calc (M 0 0 + 1)^2 = - (- (M 0 0 + 1)^2) := by ring
        _ = - 0 := by rw [h3]
        _ = 0 := by ring
    have h5 : M 0 0 + 1 = 0 := sq_eq_zero_iff.mp h4
    calc M 0 0 = (M 0 0 + 1) - 1 := by ring
      _ = 0 - 1 := by rw [h5]
      _ = -1 := by ring
  have h_M11_val : M 1 1 = -1 := by
    calc M 1 1 = -2 - M 0 0 := h11
      _ = -2 - (-1) := by rw [h_M00]
      _ = -1 := by ring
  have h10 : M 1 0 ≠ 0 := by
    intro h_10_eq_0
    have h_eq : C = -1 := by
      apply Subtype.ext
      change M = -1
      ext i j
      match i, j with
      | 0, 0 => simp [h_M00]
      | 0, 1 => simp [h01']
      | 1, 0 => simp [h_10_eq_0]
      | 1, 1 => simp [h_M11_val]
    exact h_ne h_eq
  let P_val : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]
  have hP_val : P_val = !![0, Complex.I; Complex.I, 0] := rfl
  have hP_det : P_val.det = 1 := by
    calc P_val.det = P_val 0 0 * P_val 1 1 - P_val 0 1 * P_val 1 0 := by simp only [Matrix.det_fin_two]
      _ = 0 * 0 - Complex.I * Complex.I := by rw [hP_val]; rfl
      _ = 1 := by
        rw [Complex.I_mul_I]
        ring
  let P : SpecialLinearGroup (Fin 2) ℂ := ⟨P_val, hP_det⟩
  use P, M 1 0
  have h_mul : M * P_val = P_val * !![(-1 : ℂ), M 1 0; 0, -1] := by
    rw [hP_val]
    ext i j
    match i, j with
    | 0, 0 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      try rw [h01']
      try ring
    | 0, 1 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      try rw [h_M00]
      try ring
    | 1, 0 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      try rw [h_M11_val]
      try ring
    | 1, 1 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      try ring
  have h_unit : IsUnit P_val.det := by rw [hP_det]; exact isUnit_one
  calc (C.val : Matrix (Fin 2) (Fin 2) ℂ) = M := rfl
    _ = M * 1 := by rw [Matrix.mul_one]
    _ = M * (P_val * P_val⁻¹) := by rw [Matrix.mul_nonsing_inv P_val h_unit]
    _ = M * P_val * P_val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P_val * !![(-1 : ℂ), M 1 0; 0, -1] * P_val⁻¹ := by rw [h_mul]

lemma exists_jordan_form_of_trace_neg_two (C : SpecialLinearGroup (Fin 2) ℂ) (h_tr : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace = -2) (h_ne : C ≠ -1) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ), (C.val : Matrix (Fin 2) (Fin 2) ℂ) = P.val * !![(-1 : ℂ), c; 0, -1] * P.val⁻¹ := by
  by_cases h01 : (C.val : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0
  · exact jordan_form_case2 C h_tr h_ne h01
  · exact jordan_form_case1 C h_tr h_ne h01

lemma Lambda_mulVec (A B : SpecialLinearGroup (Fin 2) ℂ) (v : Fin 4 → ℂ) :
    spinorPhi (A, B) • v = spinorPhi_matrix A B *ᵥ v := rfl

lemma vec_to_spinor_im (w : Fin 4 → ℂ) :
    vec_to_spinor (fun k => ((w k).im : ℂ)) = (-I / 2 : ℂ) • (vec_to_spinor w - (vec_to_spinor w)ᴴ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, Complex.ext_iff]
    try constructor
    all_goals ring
  }

lemma vec_to_spinor_re (w : Fin 4 → ℂ) :
    vec_to_spinor (fun k => ((w k).re : ℂ)) = (1 / 2 : ℂ) • (vec_to_spinor w + (vec_to_spinor w)ᴴ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, Complex.ext_iff]
    try constructor
    all_goals ring
  }

lemma vec_to_spinor_to_vec (M : Matrix (Fin 2) (Fin 2) ℂ) : vec_to_spinor (spinor_to_vec M) = M := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3]
    ring
  · simp [vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3]
    have h : I * I = -1 := Complex.I_mul_I
    have h2 : I ^ 2 = -1 := Complex.I_sq
    calc
      _ = M 0 1 * (1 / 2) + M 0 1 * (I ^ 2) * (-1 / 2) + M 1 0 * (1 / 2) + M 1 0 * (I ^ 2) * (1 / 2) := by ring
      _ = M 0 1 * (1 / 2) + M 0 1 * (-1) * (-1 / 2) + M 1 0 * (1 / 2) + M 1 0 * (-1) * (1 / 2) := by rw [h2]
      _ = M 0 1 := by ring
  · simp [vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3]
    have h2 : I ^ 2 = -1 := Complex.I_sq
    calc
      _ = M 0 1 * (1 / 2) + M 0 1 * (I ^ 2) * (1 / 2) + M 1 0 * (1 / 2) + M 1 0 * (I ^ 2) * (-1 / 2) := by ring
      _ = M 0 1 * (1 / 2) + M 0 1 * (-1) * (1 / 2) + M 1 0 * (1 / 2) + M 1 0 * (-1) * (-1 / 2) := by rw [h2]
      _ = M 1 0 := by ring
  · simp [vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3]
    ring

lemma spinor_action_im (A B : SpecialLinearGroup (Fin 2) ℂ) (w : Fin 4 → ℂ) :
    vec_to_spinor (fun k => (((spinorPhi_matrix A B *ᵥ w) k).im : ℂ)) =
    (-I / 2 : ℂ) • (A.val * vec_to_spinor w * B.valᵀ - (A.val * vec_to_spinor w * B.valᵀ)ᴴ) := by
  rw [vec_to_spinor_im]
  have h_action : vec_to_spinor (spinorPhi_matrix A B *ᵥ w) = A.val * vec_to_spinor w * B.valᵀ := by
    rw [spinorPhi_matrix_mulVec A B w]
    simp [spinor_action, vec_to_spinor_right_inv]
  rw [h_action]

lemma sl2c_conj_eq_conjTranspose_transpose (B : SpecialLinearGroup (Fin 2) ℂ) :
    (sl2c_conj B).val = B.valᵀᴴ := by
  ext i j
  simp [sl2c_conj, Matrix.conjTranspose_apply, Matrix.map_apply]

lemma C_val_X (A B : SpecialLinearGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * (sl2c_conj B)⁻¹).val * ((sl2c_conj B).val * V * B.valᵀ) = A.val * V * B.valᵀ := by
  have h1 : (A * (sl2c_conj B)⁻¹).val = A.val * ((sl2c_conj B)⁻¹).val := rfl
  rw [h1]
  have h_inv : ((sl2c_conj B)⁻¹).val * (sl2c_conj B).val = 1 := by
    have h2 : ((sl2c_conj B)⁻¹ * (sl2c_conj B)).val = 1 := by rw [inv_mul_cancel] ; rfl
    exact h2
  calc A.val * ((sl2c_conj B)⁻¹).val * ((sl2c_conj B).val * V * B.valᵀ)
    _ = A.val * (((sl2c_conj B)⁻¹).val * (sl2c_conj B).val) * V * B.valᵀ := by simp only [Matrix.mul_assoc]
    _ = A.val * 1 * V * B.valᵀ := by rw [h_inv]
    _ = A.val * V * B.valᵀ := by simp only [Matrix.mul_one]

lemma X_C_val_H (A B : SpecialLinearGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    ((sl2c_conj B).val * V * B.valᵀ) * (A * (sl2c_conj B)⁻¹).valᴴ = (sl2c_conj B).val * V * A.valᴴ := by
  have h1 : (A * (sl2c_conj B)⁻¹).val = A.val * ((sl2c_conj B)⁻¹).val := rfl
  rw [h1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  have h_inv : B.valᵀ * ((sl2c_conj B)⁻¹).valᴴ = 1 := by
    have h2 : ((sl2c_conj B)⁻¹).val = (B⁻¹).valᵀᴴ := by
      have h_map_inv : (sl2c_conj B)⁻¹.val = (sl2c_conj (B⁻¹)).val := congrArg Subtype.val (sl2c_conj_inv B).symm
      rw [h_map_inv, sl2c_conj_eq_conjTranspose_transpose (B⁻¹)]
    rw [h2]
    have h3 : ((B⁻¹).valᵀᴴ)ᴴ = (B⁻¹).valᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [h3]
    have h4 : (B⁻¹.val * B.val)ᵀ = B.valᵀ * (B⁻¹).valᵀ := Matrix.transpose_mul _ _
    rw [← h4]
    have h5 : B⁻¹.val * B.val = 1 := by
      have h6 : (B⁻¹ * B).val = 1 := by rw [inv_mul_cancel] ; rfl
      exact h6
    rw [h5]
    exact Matrix.transpose_one
  have h_rw : B.valᵀ * (((sl2c_conj B)⁻¹).valᴴ * A.valᴴ) = A.valᴴ := by
    rw [← Matrix.mul_assoc]
    have h_inv' : (↑B)ᵀ * (↑(sl2c_conj B)⁻¹)ᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := h_inv
    rw [h_inv']
    rw [Matrix.one_mul]
  rw [h_rw]

lemma tube_preserver_posdef_spinor_exists (n : ℕ) (hn : 2 ≤ n) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (hΛ : Λ • z ∈ forward_tube_n n)
    (C A B : SpecialLinearGroup (Fin 2) ℂ) (hΛ_eq : spinorPhi (A, B) = Λ)
    (hC_eq : C = A * (sl2c_conj B)⁻¹) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ, X.PosDef ∧ Y.IsHermitian ∧
      ( (-I / 2 : ℂ) • (C.val * Y - Y * C.valᴴ) + (1/2 : ℂ) • (C.val * X + X * C.valᴴ) ).PosDef := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hi : (⟨0, h0⟩ : Fin n).val + 1 < n := by omega
  let w := - (z ⟨0, h0⟩ - z ⟨1, h1⟩)

  have h_w_pos : (fun k => (w k).im) ∈ forward_light_cone := hz ⟨0, h0⟩ hi

  let U := vec_to_spinor (fun k => ((w k).re : ℂ))
  let V := vec_to_spinor (fun k => ((w k).im : ℂ))

  have h_V_posDef : V.PosDef := posDef_vec_to_spinor (fun k => (w k).im) h_w_pos

  let X := (sl2c_conj B).val * V * B.valᵀ
  let Y := (sl2c_conj B).val * U * B.valᵀ

  use X, Y

  have hX_pos : X.PosDef := by
    dsimp [X]
    have h_conj_transpose : B.valᵀ = ((sl2c_conj B).val)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply, sl2c_conj, Matrix.map_apply]
    rw [h_conj_transpose]
    apply posdef_congruence
    · have h_det : (sl2c_conj B).val.det = 1 := (sl2c_conj B).property
      rw [h_det]
      norm_num
    · exact h_V_posDef

  have hY_herm : Y.IsHermitian := by
    dsimp [Y]
    rw [sl2c_conj_eq_conjTranspose_transpose B]
    have h_transpose_conj : B.valᵀ = (B.valᵀᴴ)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [h_transpose_conj]
    have hU : U.IsHermitian := by
      dsimp [U]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals {
        simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.conjTranspose_apply]
        try ring
      }
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hU

  have h_eval : ( (-I / 2 : ℂ) • (C.val * Y - Y * C.valᴴ) + (1/2 : ℂ) • (C.val * X + X * C.valᴴ) ).PosDef := by
    have h_CY : C.val * Y = A.val * U * B.valᵀ := by
      dsimp [Y]
      rw [hC_eq]
      exact C_val_X A B U
    have h_CX : C.val * X = A.val * V * B.valᵀ := by
      dsimp [X]
      rw [hC_eq]
      exact C_val_X A B V
    have h_YCH : Y * C.valᴴ = (sl2c_conj B).val * U * A.valᴴ := by
      dsimp [Y]
      rw [hC_eq]
      exact X_C_val_H A B U
    have h_XCH : X * C.valᴴ = (sl2c_conj B).val * V * A.valᴴ := by
      dsimp [X]
      rw [hC_eq]
      exact X_C_val_H A B V

    have h_U_herm : Uᴴ = U := by
      dsimp [U]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals {
        simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.conjTranspose_apply]
        try constructor
        all_goals ring
      }
    have h_V_herm : Vᴴ = V := by
      dsimp [V]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals {
        simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.conjTranspose_apply]
        try constructor
        all_goals ring
      }

    have h_w_split : vec_to_spinor w = U + I • V := by
      dsimp [U, V]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals {
        simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.add_apply, Matrix.smul_apply, Complex.ext_iff]
        try constructor
        all_goals ring
      }

    have h_YCH_eq : Y * C.valᴴ = (C.val * Y)ᴴ := by
      rw [h_YCH, h_CY, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      have h_conj_B : (sl2c_conj B).val = B.valᵀᴴ := sl2c_conj_eq_conjTranspose_transpose B
      rw [h_conj_B, h_U_herm]
      simp [Matrix.mul_assoc]

    have h_XCH_eq : X * C.valᴴ = (C.val * X)ᴴ := by
      rw [h_XCH, h_CX, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      have h_conj_B : (sl2c_conj B).val = B.valᵀᴴ := sl2c_conj_eq_conjTranspose_transpose B
      rw [h_conj_B, h_V_herm]
      simp [Matrix.mul_assoc]

    have h_alg : (-I / 2 : ℂ) • (C.val * Y - Y * C.valᴴ) + (1/2 : ℂ) • (C.val * X + X * C.valᴴ) =
        (-I / 2 : ℂ) • (A.val * vec_to_spinor w * B.valᵀ - (A.val * vec_to_spinor w * B.valᵀ)ᴴ) := by
      rw [h_YCH_eq, h_XCH_eq]
      rw [h_CY, h_CX]
      rw [h_w_split]

      have h_expand : A.val * (U + I • V) * B.valᵀ = A.val * U * B.valᵀ + I • (A.val * V * B.valᵀ) := by
        ext i j
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
        ring

      rw [h_expand]
      have h_conj_expand : (A.val * U * B.valᵀ + I • (A.val * V * B.valᵀ))ᴴ = (A.val * U * B.valᵀ)ᴴ - I • (A.val * V * B.valᵀ)ᴴ := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
        ext i j
        simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.star_def, Complex.conj_I]
        ring

      rw [h_conj_expand]

      ext i j
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
      have h_alg_step (x1 x2 y1 y2 : ℂ) : (-I / 2) * (x1 - x2) + (2⁻¹ * y1 + 2⁻¹ * y2) = (-I / 2) * (x1 + I * y1 - (x2 - I * y2)) := by
        calc
          (-I / 2) * (x1 - x2) + (2⁻¹ * y1 + 2⁻¹ * y2) = (-I / 2) * (x1 - x2) + (- (I * I) / 2) * (y1 + y2) := by rw [Complex.I_mul_I]; ring
          _ = (-I / 2) * (x1 + I * y1 - (x2 - I * y2)) := by ring
      rw [h_alg_step]

    rw [h_alg]

    have hw_im : vec_to_spinor (fun k => ((Λ • w) k).im) = (-I / 2 : ℂ) • (A.val * vec_to_spinor w * B.valᵀ - (A.val * vec_to_spinor w * B.valᵀ)ᴴ) := by
      rw [← hΛ_eq]
      exact spinor_action_im A B w
    rw [← hw_im]

    have h_Lambda_w : Λ • w = - ((Λ • z) ⟨0, h0⟩ - (Λ • z) ⟨1, h1⟩) := by
      ext k
      rw [← hΛ_eq]
      simp [Lambda_mulVec, Pi.sub_apply, Pi.neg_apply]
      have hw : w = z ⟨1, h1⟩ - z ⟨0, h0⟩ := by
        ext
        change (-(z ⟨0, h0⟩ - z ⟨1, h1⟩)) _ = _
        simp
      rw [hw]
      have h2 : spinorPhi_matrix A B *ᵥ (z ⟨1, h1⟩ - z ⟨0, h0⟩) = spinorPhi_matrix A B *ᵥ (z ⟨1, h1⟩) - spinorPhi_matrix A B *ᵥ (z ⟨0, h0⟩) := Matrix.mulVec_sub (spinorPhi_matrix A B) (z ⟨1, h1⟩) (z ⟨0, h0⟩)
      rw [h2]
      ring
      rfl

    have hw_tube : (fun k => ((Λ • w) k).im) ∈ forward_light_cone := by
      rw [h_Lambda_w]
      exact hΛ ⟨0, h0⟩ hi

    exact posDef_vec_to_spinor _ hw_tube

  exact ⟨hX_pos, hY_herm, h_eval⟩



lemma tube_preserver_trace_neq_neg_two (n : ℕ) (hn : 2 ≤ n) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (hΛ : Λ • z ∈ forward_tube_n n)
    (C : SpecialLinearGroup (Fin 2) ℂ) (hC : ∃ (A B : SpecialLinearGroup (Fin 2) ℂ),
      spinorPhi (A, B) = Λ ∧ C = A * (sl2c_conj B)⁻¹) :
    (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace ≠ -2 ∨ C = -1 := by
  by_cases h_trace : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace = -2
  · right
    by_contra hC_ne
    
    have h_similar : ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ), (C.val : Matrix (Fin 2) (Fin 2) ℂ) = P.val * !![(-1 : ℂ), c; 0, -1] * (P.val)⁻¹ :=
      exists_jordan_form_of_trace_neg_two C h_trace hC_ne
    rcases h_similar with ⟨P, c, hC_sim⟩

    rcases hC with ⟨A, B, hΛ_eq, hC_eq⟩
    
    have hXY_exists : ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ, X.PosDef ∧ Y.IsHermitian ∧ ( (-I / 2 : ℂ) • (C.val * Y - Y * C.valᴴ) + (1/2 : ℂ) • (C.val * X + X * C.valᴴ) ).PosDef :=
      tube_preserver_posdef_spinor_exists n hn Λ z hz hΛ C A B hΛ_eq hC_eq
    rcases hXY_exists with ⟨X, Y, hX_pos, hY_herm, hCXY_pos⟩

    
    have h_contra := no_tube_preserver_trace_neg_two_proof C.val X Y hX_pos hY_herm c P hC_sim
    exact h_contra hCXY_pos
  · left; exact h_trace

lemma sl2c_exists_principal_sq_diag (P_c : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (ha : a ≠ 0) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      P * P = P_c * diag_matrix a ha * P_c⁻¹ ∧
      0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  have h_sqrt : ∃ b : ℂ, b * b = a := by
    have := IsAlgClosed.exists_pow_nat_eq a zero_lt_two
    rcases this with ⟨b, hb⟩
    use b
    have hb2 : b * b = b ^ 2 := by ring
    rw [hb2]
    exact hb
  rcases h_sqrt with ⟨b, hb⟩
  have hb_ne : b ≠ 0 := by intro h; rw [h, mul_zero] at hb; exact ha hb.symm
  by_cases h_re : 0 ≤ (b + b⁻¹).re
  · let P_diag : SpecialLinearGroup (Fin 2) ℂ := diag_matrix b hb_ne
    use P_c * P_diag * P_c⁻¹
    use P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val
    constructor
    · calc
        (P_c * P_diag * P_c⁻¹) * (P_c * P_diag * P_c⁻¹)
          = P_c * (P_diag * P_diag) * P_c⁻¹ := by group
        _ = P_c * (diag_matrix (b * b) (mul_ne_zero hb_ne hb_ne)) * P_c⁻¹ := by rw [diag_matrix_sq b hb_ne]
        _ = P_c * (diag_matrix a ha) * P_c⁻¹ := by
              have h_b_sq : b * b = a := hb
              have h_eq : diag_matrix (b * b) (mul_ne_zero hb_ne hb_ne) = diag_matrix a ha := by
                ext i j; dsimp [diag_matrix]; rw [h_b_sq]
              rw [h_eq]
    · constructor
      · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
        have h_trace_conj : (P_c * P_diag * P_c⁻¹).val.trace = P_diag.val.trace := by
          change (P_c.val * P_diag.val * (P_c⁻¹).val).trace = P_diag.val.trace
          calc (P_c.val * P_diag.val * (P_c⁻¹).val).trace
             = (P_c.val * (P_diag.val * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
           _ = ((P_diag.val * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
           _ = (P_diag.val * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
           _ = P_diag.val.trace := by rw [P_c_inv_mul, Matrix.mul_one]
        rw [h_trace_conj]
        have h_tr : P_diag.val.trace = b + b⁻¹ := by
          change (diag_matrix b hb_ne).val.trace = b + b⁻¹
          simp [diag_matrix]
        rw [h_tr]
        exact h_re
      · constructor
        · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
          have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel P_c)
          have h_conj := exp_conj_matrix P_c.val (Matrix.diagonal ![Complex.log b, -Complex.log b]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
          rw [h_conj]
          have h_exp_neg : cexp (-Complex.log b) = b⁻¹ := by rw [Complex.exp_neg, Complex.exp_log hb_ne]
          have h_exp_diag : NormedSpace.exp (Matrix.diagonal ![Complex.log b, -Complex.log b]) = Matrix.diagonal ![b, b⁻¹] := by
            rw [MatrixAnalysis.exp_diagonal]
            ext i j
            simp [Matrix.diagonal, Matrix.of_apply, ← Complex.exp_eq_exp_ℂ]
            fin_cases i <;> fin_cases j <;> simp [Complex.exp_log hb_ne, h_exp_neg]
          rw [h_exp_diag]
          ext i j
          dsimp [P_diag, diag_matrix]
          rfl
        · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
          have h_trace_conj : (P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val).trace = (Matrix.diagonal ![Complex.log b, -Complex.log b]).trace := by
            calc (P_c.val * Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val).trace
               = (P_c.val * (Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
             _ = ((Matrix.diagonal ![Complex.log b, -Complex.log b] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
             _ = (Matrix.diagonal ![Complex.log b, -Complex.log b] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
             _ = (Matrix.diagonal ![Complex.log b, -Complex.log b]).trace := by rw [P_c_inv_mul, Matrix.mul_one]
          rw [h_trace_conj]
          simp [Matrix.trace_diagonal, Fin.sum_univ_two]
  · let P_diag : SpecialLinearGroup (Fin 2) ℂ := diag_matrix (-b) (neg_ne_zero.mpr hb_ne)
    use P_c * P_diag * P_c⁻¹
    use P_c.val * Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * (P_c⁻¹).val
    constructor
    · calc
        (P_c * P_diag * P_c⁻¹) * (P_c * P_diag * P_c⁻¹)
          = P_c * (P_diag * P_diag) * P_c⁻¹ := by group
        _ = P_c * (diag_matrix ((-b) * (-b)) (mul_ne_zero (neg_ne_zero.mpr hb_ne) (neg_ne_zero.mpr hb_ne))) * P_c⁻¹ := by rw [diag_matrix_sq (-b) (neg_ne_zero.mpr hb_ne)]
        _ = P_c * (diag_matrix a ha) * P_c⁻¹ := by
              have h_b_sq : (-b) * (-b) = a := by
                rw [show (-b) * (-b) = b * b by ring]
                exact hb
              have h_eq : diag_matrix ((-b) * (-b)) (mul_ne_zero (neg_ne_zero.mpr hb_ne) (neg_ne_zero.mpr hb_ne)) = diag_matrix a ha := by
                ext i j; dsimp [diag_matrix]; rw [h_b_sq]
              rw [h_eq]
    · constructor
      · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
        have h_trace_conj : (P_c * P_diag * P_c⁻¹).val.trace = P_diag.val.trace := by
          change (P_c.val * P_diag.val * (P_c⁻¹).val).trace = P_diag.val.trace
          calc (P_c.val * P_diag.val * (P_c⁻¹).val).trace
             = (P_c.val * (P_diag.val * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
           _ = ((P_diag.val * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
           _ = (P_diag.val * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
           _ = P_diag.val.trace := by rw [P_c_inv_mul, Matrix.mul_one]
        rw [h_trace_conj]
        have h_tr : P_diag.val.trace = - (b + b⁻¹) := by
          change (diag_matrix (-b) (neg_ne_zero.mpr hb_ne)).val.trace = - (b + b⁻¹)
          have h_inv : (-b)⁻¹ = -b⁻¹ := inv_neg
          simp [diag_matrix, h_inv]
          ring
        rw [h_tr]
        have h_neg_re : (- (b + b⁻¹)).re = - (b + b⁻¹).re := Complex.neg_re (b + b⁻¹)
        rw [h_neg_re]
        linarith
      · constructor
        · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
          have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel P_c)
          have h_conj := exp_conj_matrix P_c.val (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
          rw [h_conj]
          have hb_neg_ne : -b ≠ 0 := neg_ne_zero.mpr hb_ne
          have h_exp_neg : cexp (-Complex.log (-b)) = (-b)⁻¹ := by rw [Complex.exp_neg, Complex.exp_log hb_neg_ne]
          have h_exp_diag : NormedSpace.exp (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)]) = Matrix.diagonal ![-b, (-b)⁻¹] := by
            rw [MatrixAnalysis.exp_diagonal]
            ext i j
            simp [Matrix.diagonal, Matrix.of_apply, ← Complex.exp_eq_exp_ℂ]
            fin_cases i <;> fin_cases j <;> simp [Complex.exp_log hb_neg_ne, h_exp_neg]
          rw [h_exp_diag]
          ext i j
          dsimp [P_diag, diag_matrix]
          rfl
        · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
          have h_trace_conj : (P_c.val * Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * (P_c⁻¹).val).trace = (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)]).trace := by
            calc (P_c.val * Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * (P_c⁻¹).val).trace
               = (P_c.val * (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
             _ = ((Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
             _ = (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
             _ = (Matrix.diagonal ![Complex.log (-b), -Complex.log (-b)]).trace := by rw [P_c_inv_mul, Matrix.mul_one]
          rw [h_trace_conj]
          simp [Matrix.trace_diagonal, Fin.sum_univ_two]

lemma sl2c_exists_principal_sq_jor1 (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      P * P = P_c * jordan_matrix c * P_c⁻¹ ∧
      0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  let P_jor : SpecialLinearGroup (Fin 2) ℂ := jordan_matrix (c / 2)
  use P_c * P_jor * P_c⁻¹
  use P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val
  constructor
  · calc (P_c * P_jor * P_c⁻¹) * (P_c * P_jor * P_c⁻¹)
        = P_c * (P_jor * P_jor) * P_c⁻¹ := by group
      _ = P_c * (jordan_matrix (c / 2 + c / 2)) * P_c⁻¹ := by rw [jordan_matrix_sq (c / 2)]
      _ = P_c * (jordan_matrix c) * P_c⁻¹ := by
            have h_eq : c / 2 + c / 2 = c := by ring
            rw [h_eq]
  · constructor
    · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
      have h_trace_conj : (P_c * P_jor * P_c⁻¹).val.trace = P_jor.val.trace := by
        change (P_c.val * P_jor.val * (P_c⁻¹).val).trace = P_jor.val.trace
        calc (P_c.val * P_jor.val * (P_c⁻¹).val).trace
           = (P_c.val * (P_jor.val * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
         _ = ((P_jor.val * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
         _ = (P_jor.val * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
         _ = P_jor.val.trace := by rw [P_c_inv_mul, Matrix.mul_one]
      rw [h_trace_conj]
      have h_tr : P_jor.val.trace = 2 := by
        change (jordan_matrix (c / 2)).val.trace = 2
        simp [jordan_matrix, J_mat, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        norm_num
      rw [h_tr]
      norm_num
    · constructor
      · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
        have P_c_mul_inv : P_c.val * (P_c⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel P_c)
        have h_conj := exp_conj_matrix P_c.val (Matrix.of ![![0, c / 2], ![0, 0]]) (P_c⁻¹).val P_c_mul_inv P_c_inv_mul
        rw [h_conj]
        have h_nilp : (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = 0 := by
          rw [pow_succ, pow_succ, pow_one]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.zero_apply] <;> ring
        have h_exp_jor : NormedSpace.exp (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) = jordan_matrix (c / 2) := by
          rw [exp_of_nilpotent3 _ h_nilp]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [pow_two, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring
        rw [h_exp_jor]
        ext i j
        dsimp [P_jor, jordan_matrix]
      · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
        have h_trace_conj : (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by
          calc (P_c.val * Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val).trace
             = (P_c.val * (Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
           _ = ((Matrix.of ![![0, c / 2], ![0, 0]] * (P_c⁻¹).val) * P_c.val).trace := Matrix.trace_mul_comm _ _
           _ = (Matrix.of ![![0, c / 2], ![0, 0]] * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
           _ = (Matrix.of ![![0, c / 2], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ).trace := by rw [P_c_inv_mul, Matrix.mul_one]
        rw [h_trace_conj]
        simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]


lemma sl2c_exists_principal_sq_of_trace (C : SpecialLinearGroup (Fin 2) ℂ)
    (h_tr : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace ≠ -2 ∨ C = -1) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      P * P = C ∧
      0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  by_cases h_C : C = -1
  · have h_principal := sl2c_exists_principal_sq_diag 1 (-1) (by norm_num)
    rcases h_principal with ⟨P, H, h_sq, h_re, h_exp, h_tr2⟩
    use P, H
    constructor
    · calc P * P = 1 * diag_matrix (-1) (by norm_num) * 1⁻¹ := h_sq
        _ = diag_matrix (-1) (by norm_num) := by group
        _ = -1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix, Matrix.one_fin_two]
        _ = C := h_C.symm
    · exact ⟨h_re, h_exp, h_tr2⟩
  · have h_class := sl2c_classification C
    rcases h_class with ⟨P_c, a, ha, h_diag⟩ | ⟨P_c, ε, hε, c, h_jor⟩
    · have h_principal := sl2c_exists_principal_sq_diag P_c a ha
      rcases h_principal with ⟨P, H, h_sq, h_re, h_exp, h_tr2⟩
      use P, H
      constructor
      · rw [h_sq, h_diag]
      · exact ⟨h_re, h_exp, h_tr2⟩
    · have hε_copy := hε
      rcases hε_copy with h1 | h_1
      · have h_jor_case := sl2c_exists_principal_sq_jor1 P_c c
        rcases h_jor_case with ⟨P, H, h_sq, h_re, h_exp, h_tr2⟩
        use P, H
        constructor
        · calc P * P = P_c * jordan_matrix c * P_c⁻¹ := h_sq
            _ = P_c * (diag_matrix 1 (by norm_num) * jordan_matrix c) * P_c⁻¹ := by
              have h_one : diag_matrix 1 (by norm_num) = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix]
              rw [h_one, one_mul]
            _ = C := by
              have h_diag_eq : diag_matrix ε (by rcases hε with h | h <;> simp [h]) = diag_matrix 1 (by norm_num) := by ext i j; dsimp [diag_matrix]; rw [h1]
              have h_jor2 : C = P_c * (diag_matrix 1 (by norm_num) * jordan_matrix c) * P_c⁻¹ := by
                calc C = P_c * (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c) * P_c⁻¹ := h_jor
                   _ = P_c * (diag_matrix 1 (by norm_num) * jordan_matrix c) * P_c⁻¹ := by rw [h_diag_eq]
              exact h_jor2.symm
        · exact ⟨h_re, h_exp, h_tr2⟩
      · have P_c_inv_mul : (P_c⁻¹).val * P_c.val = 1 := congrArg Subtype.val (inv_mul_cancel P_c)
        have h_trace_C : (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace = -2 := by
          have h_diag_eq : diag_matrix ε (by rcases hε with h | h <;> simp [h]) = diag_matrix (-1) (by norm_num) := by ext i j; dsimp [diag_matrix]; rw [h_1]
          have h_jor2 : C = P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹ := by
            calc C = P_c * (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c) * P_c⁻¹ := h_jor
               _ = P_c * (diag_matrix (-1) (by norm_num) * jordan_matrix c) * P_c⁻¹ := by rw [h_diag_eq]
          calc (C.val : Matrix (Fin 2) (Fin 2) ℂ).trace
             = (P_c.val * (diag_matrix (-1) (by norm_num) * jordan_matrix c).val * (P_c⁻¹).val).trace := congrArg Matrix.trace (congrArg Subtype.val h_jor2)
           _ = (P_c.val * ((diag_matrix (-1) (by norm_num) * jordan_matrix c).val * (P_c⁻¹).val)).trace := by rw [Matrix.mul_assoc]
           _ = ((diag_matrix (-1) (by norm_num) * jordan_matrix c).val * (P_c⁻¹).val * P_c.val).trace := Matrix.trace_mul_comm _ _
           _ = ((diag_matrix (-1) (by norm_num) * jordan_matrix c).val * ((P_c⁻¹).val * P_c.val)).trace := by rw [Matrix.mul_assoc]
           _ = ((diag_matrix (-1) (by norm_num) * jordan_matrix c).val : Matrix (Fin 2) (Fin 2) ℂ).trace := by rw [P_c_inv_mul, Matrix.mul_one]
           _ = -2 := by simp [diag_matrix, jordan_matrix, J_mat, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,]; ring
        rcases h_tr with h_tr1 | h_tr2
        · exfalso; exact h_tr1 h_trace_C
        · exfalso; exact h_C h_tr2



lemma sl2c_exists_principal_sq_of_tube_preserver (n : ℕ) (hn : 2 ≤ n) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (hΛ : Λ • z ∈ forward_tube_n n)
    (C : SpecialLinearGroup (Fin 2) ℂ)
    (hC : ∃ (A B : SpecialLinearGroup (Fin 2) ℂ), spinorPhi (A, B) = Λ ∧ C = A * (sl2c_conj B)⁻¹) :
    ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      P * P = C ∧
      0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re ∧
      P.val = NormedSpace.exp H ∧
      H.trace = 0 := by
  have h_tr := tube_preserver_trace_neq_neg_two n hn Λ z hz hΛ C hC
  exact sl2c_exists_principal_sq_of_trace C h_tr


lemma spinorPhi_boost_is_exp_iM (P : SpecialLinearGroup (Fin 2) ℂ) :
    ∃ M : RealLorentzLieAlgebra, spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M := by
  have h_S := spinorPhi_S_matrix_to_M P
  rcases h_S with ⟨M', hM', h_exp⟩
  let M_val : Matrix (Fin 4) (Fin 4) ℝ := 2 • M'
  have hM_val_mem : M_valᵀ * minkowskiMetricReal + minkowskiMetricReal * M_val = 0 := by
    change (2 • M')ᵀ * minkowskiMetricReal + minkowskiMetricReal * (2 • M') = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    rw [hM']
    exact smul_zero 2
  let M : RealLorentzLieAlgebra := ⟨M_val, hM_val_mem⟩
  use M
  ext i j
  change (spinorPhi (P, (sl2c_conj P)⁻¹)).val.val i j = (exp_iM M).val.val i j
  have h_exp_eq : (exp_iM M).val.val = NormedSpace.exp (Complex.I • real_matrix_to_complex M_val) := rfl
  rw [h_exp_eq]
  have h_M_val : real_matrix_to_complex M_val = 2 • real_matrix_to_complex M' := by
    ext a b
    dsimp [M_val, real_matrix_to_complex]
    push_cast
    rfl
  rw [h_M_val]
  have h_smul_assoc : Complex.I • (2 • real_matrix_to_complex M') = ((2 * Complex.I) : ℂ) • real_matrix_to_complex M' := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h_smul_assoc]
  have h_M'_map : real_matrix_to_complex M' = Matrix.map M' (fun x => (x : ℂ)) := rfl
  rw [h_M'_map]
  exact congrFun (congrFun h_exp i) j



lemma sl2c_00_bound (a b c d : ℂ) (h : a * d - b * c = 1) :
    1 ≤ ((a * star a + b * star b + c * star c + d * star d) / 2).re := by
  have h_1 : 1 = (a * d - b * c).re := by rw [h]; rfl
  have h_2 : (a * d - b * c).re = a.re * d.re - a.im * d.im - (b.re * c.re - b.im * c.im) := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [h_2] at h_1
  have h_4 : 0 ≤ (a.re - d.re) ^ 2 := sq_nonneg (a.re - d.re)
  have h_5 : 0 ≤ (a.im + d.im) ^ 2 := sq_nonneg (a.im + d.im)
  have h_6 : 0 ≤ (b.re + c.re) ^ 2 := sq_nonneg (b.re + c.re)
  have h_7 : 0 ≤ (b.im - c.im) ^ 2 := sq_nonneg (b.im - c.im)
  have h_re : ((a * star a + b * star b + c * star c + d * star d) / 2).re =
    (a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2 + c.re ^ 2 + c.im ^ 2 + d.re ^ 2 + d.im ^ 2) / 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h_re]
  nlinarith

lemma spinorPhi_is_proper_orthochronous (U : SpecialLinearGroup (Fin 2) ℂ) :
    ∃ (R : ProperOrthochronousLorentzGroup),
      real_to_complex_lorentz R = spinorPhi (U, sl2c_conj U) := by
  have h_real : Matrix.map (spinorPhi_matrix U (sl2c_conj U)) star = spinorPhi_matrix U (sl2c_conj U) := by
    have h := spinorPhi_conj U (sl2c_conj U)
    change Matrix.map (spinorPhi_matrix U (sl2c_conj U)) star = spinorPhi_matrix (sl2c_conj (sl2c_conj U)) (sl2c_conj U) at h
    rw [sl2c_conj_sl2c_conj] at h
    exact h
  
  have h_det : (spinorPhi_matrix U (sl2c_conj U)).det = 1 := by
    exact spinorPhi_matrix_det U (sl2c_conj U)
  
  have h_00 : 1 ≤ (spinorPhi_matrix U (sl2c_conj U) 0 0).re := by
    have h_00_apply : spinorPhi_matrix U (sl2c_conj U) 0 0 =
      (((U.val : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor (fun k ↦ if k = 0 then 1 else 0) * (sl2c_conj U).valᵀ) 0 0 +
      ((U.val : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor (fun k ↦ if k = 0 then 1 else 0) * (sl2c_conj U).valᵀ) 1 1) / 2 := by
      rw [spinorPhi_matrix_apply]
      dsimp [spinor_action]
    rw [h_00_apply]
    have h_vec : vec_to_spinor (fun k ↦ if k = 0 then (1:ℂ) else 0) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
    rw [h_vec]
    have h_mul_one : (U.val : Matrix (Fin 2) (Fin 2) ℂ) * 1 = (U.val : Matrix (Fin 2) (Fin 2) ℂ) := Matrix.mul_one _
    rw [h_mul_one]
    have h_det_U : U.val.det = 1 := U.property
    let a := U.val 0 0
    let b := U.val 0 1
    let c := U.val 1 0
    let d := U.val 1 1
    have h_det_eq : a * d - b * c = 1 := by
      change U.val 0 0 * U.val 1 1 - U.val 0 1 * U.val 1 0 = 1
      rw [←Matrix.det_fin_two]
      exact h_det_U
    have h_tr : (((U.val : Matrix (Fin 2) (Fin 2) ℂ) * (sl2c_conj U).valᵀ) 0 0 +
                 ((U.val : Matrix (Fin 2) (Fin 2) ℂ) * (sl2c_conj U).valᵀ) 1 1) =
                a * star a + b * star b + c * star c + d * star d := by
      dsimp [sl2c_conj, a, b, c, d]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      ring
    rw [h_tr]
    exact sl2c_00_bound a b c d h_det_eq
  let M_C := spinorPhi_matrix U (sl2c_conj U)
  let M_R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.map M_C Complex.re
  have h_M_C_eq : M_C = Matrix.map M_R (algebraMap ℝ ℂ) := by
    ext i j
    have h_star := congr_fun (congr_fun h_real i) j
    dsimp [M_C, M_R]
    apply Complex.ext
    · simp
    · simp
      have h_im : star (M_C i j) = M_C i j := h_star
      have : (star (M_C i j)).im = (M_C i j).im := congr_arg Complex.im h_im
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
  have h_lorentz := spinorPhi_is_lorentz U (sl2c_conj U)
  have h_MR_lorentz : M_Rᵀ * minkowskiMetricReal * M_R = minkowskiMetricReal := by
    have h2 : Matrix.map minkowskiMetricReal (algebraMap ℝ ℂ) = minkowskiMetric := by
      ext i j; simp [minkowskiMetric, minkowskiMetricReal, Matrix.map_apply]; fin_cases i <;> fin_cases j <;> norm_num
    have h1 : Matrix.map (M_Rᵀ * minkowskiMetricReal * M_R) (algebraMap ℝ ℂ) = M_Cᵀ * minkowskiMetric * M_C := by
      have h_map1 : (M_Rᵀ * minkowskiMetricReal * M_R).map (algebraMap ℝ ℂ) =
        (M_Rᵀ * minkowskiMetricReal).map (algebraMap ℝ ℂ) * M_R.map (algebraMap ℝ ℂ) := Matrix.map_mul
      have h_map2 : (M_Rᵀ * minkowskiMetricReal).map (algebraMap ℝ ℂ) =
        M_Rᵀ.map (algebraMap ℝ ℂ) * minkowskiMetricReal.map (algebraMap ℝ ℂ) := Matrix.map_mul
      rw [h_map1, h_map2]
      have h_map3 : M_Rᵀ.map (algebraMap ℝ ℂ) = (M_R.map (algebraMap ℝ ℂ))ᵀ := rfl
      rw [h_map3, ←h_M_C_eq, h2]
    have h3 : Matrix.map (M_Rᵀ * minkowskiMetricReal * M_R) (algebraMap ℝ ℂ) = Matrix.map minkowskiMetricReal (algebraMap ℝ ℂ) := by
      rw [h1, h_lorentz, ← h2]
    ext i j
    have h4 := congr_fun (congr_fun h3 i) j
    simp only [Matrix.map_apply] at h4
    exact Complex.ofReal_inj.mp h4
  have h_inv2 : (minkowskiMetricReal * M_Rᵀ * minkowskiMetricReal) * M_R = 1 := by
    calc (minkowskiMetricReal * M_Rᵀ * minkowskiMetricReal) * M_R
      _ = minkowskiMetricReal * (M_Rᵀ * minkowskiMetricReal * M_R) := by simp only [Matrix.mul_assoc]
      _ = minkowskiMetricReal * minkowskiMetricReal := by rw [h_MR_lorentz]
      _ = 1 := by ext i j; simp [minkowskiMetricReal, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]; fin_cases i <;> fin_cases j <;> norm_num
  have h_inv : M_R * (minkowskiMetricReal * M_Rᵀ * minkowskiMetricReal) = 1 := mul_eq_one_comm.mpr h_inv2
  let R_GL : Matrix.GeneralLinearGroup (Fin 4) ℝ := {
    val := M_R
    inv := minkowskiMetricReal * M_Rᵀ * minkowskiMetricReal
    val_inv := h_inv
    inv_val := h_inv2
  }
  have h_prop : R_GL ∈ ProperOrthochronousLorentzGroup := by
    have h_det_MC : RingHom.mapMatrix (algebraMap ℝ ℂ) M_R = M_C := h_M_C_eq.symm
    have h_det_map : (RingHom.mapMatrix (algebraMap ℝ ℂ) M_R).det = (algebraMap ℝ ℂ) M_R.det := (RingHom.map_det (algebraMap ℝ ℂ) M_R).symm
    rw [h_det_MC, h_det] at h_det_map
    have h_det3 : M_R.det = 1 := Complex.ofReal_inj.mp h_det_map.symm
    have h_00_MC : (algebraMap ℝ ℂ) (M_R 0 0) = M_C 0 0 := by
      calc (algebraMap ℝ ℂ) (M_R 0 0)
        _ = (Matrix.map M_R (algebraMap ℝ ℂ)) 0 0 := by rfl
        _ = M_C 0 0 := by rw [h_M_C_eq]
    have h_00_R : M_R 0 0 = (M_C 0 0).re := by
      have h_re : ((algebraMap ℝ ℂ) (M_R 0 0)).re = (M_C 0 0).re := by rw [h_00_MC]
      exact h_re
    have h_00_pos : 0 < M_R 0 0 := by
      rw [h_00_R]
      linarith
    exact ⟨h_MR_lorentz, h_det3, h_00_pos⟩
  use ⟨R_GL, h_prop⟩
  apply Subtype.ext
  apply Units.ext
  change RingHom.mapMatrix (algebraMap ℝ ℂ) M_R = M_C
  exact h_M_C_eq.symm


lemma sscl_polar_decomp_of_tube_preserver (n : ℕ) (hn : 2 ≤ n) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (hΛ : Λ • z ∈ forward_tube_n n) :
    ∃ (R : ProperOrthochronousLorentzGroup) (M : RealLorentzLieAlgebra)
      (P : SpecialLinearGroup (Fin 2) ℂ),
      0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re ∧
      spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M ∧
      Λ.val = (exp_iM M * real_to_complex_lorentz R).val := by
  
  have h_surj := spinorPhi_surjective Λ
  rcases h_surj with ⟨⟨A, B⟩, h_AB⟩
  
  have h_C_def : ∃ (C : SpecialLinearGroup (Fin 2) ℂ), C = A * (sl2c_conj B)⁻¹ := ⟨_, rfl⟩
  rcases h_C_def with ⟨C, hC⟩
  have h_sq := sl2c_exists_principal_sq_of_tube_preserver n hn Λ z hz hΛ C ⟨A, B, h_AB, hC⟩
  rcases h_sq with ⟨P, H, h_sq_eq, h_P_tr, h_P_exp, h_H_tr⟩
  
  have h_pos : P * P = C := h_sq_eq
  let U : SpecialLinearGroup (Fin 2) ℂ := P⁻¹ * A
  have hA : A = P * U := by
    change A = P * (P⁻¹ * A)
    group
  have hB : B = (sl2c_conj P)⁻¹ * sl2c_conj U := by
    have h_P2 : P * P = A * (sl2c_conj B)⁻¹ := by rw [h_pos, hC]
    have h1 : P * P * sl2c_conj B = A := by
      calc P * P * sl2c_conj B
        _ = A * (sl2c_conj B)⁻¹ * sl2c_conj B := by rw [h_P2]
        _ = A := by group
    have h2 : sl2c_conj B = P⁻¹ * U := by
      calc sl2c_conj B
        _ = P⁻¹ * P⁻¹ * (P * P * sl2c_conj B) := by group
        _ = P⁻¹ * P⁻¹ * A := by rw [h1]
        _ = P⁻¹ * (P⁻¹ * A) := by rw [mul_assoc]
    have h3 : sl2c_conj (sl2c_conj B) = sl2c_conj (P⁻¹ * U) := by rw [h2]
    rw [sl2c_conj_sl2c_conj B] at h3
    rw [h3]
    rw [sl2c_conj_mul]
    rw [sl2c_conj_inv]
  have h_boost := spinorPhi_boost_is_exp_iM P
  have h_rot := spinorPhi_is_proper_orthochronous U
  rcases h_boost with ⟨M, hM_eq⟩
  rcases h_rot with ⟨R, hR_eq⟩
  use R, M, P
  constructor
  · exact h_P_tr
  · constructor
    · exact hM_eq
    · have h_A_B : spinorPhi (A, B) = spinorPhi (P * U, (sl2c_conj P)⁻¹ * sl2c_conj U) := by rw [hA, hB]
      have h_hom : spinorPhi (P * U, (sl2c_conj P)⁻¹ * sl2c_conj U) = spinorPhi (P, (sl2c_conj P)⁻¹) * spinorPhi (U, sl2c_conj U) := map_mul spinorPhi (P, (sl2c_conj P)⁻¹) (U, sl2c_conj U)
      have h_subst : spinorPhi (A, B) = exp_iM M * real_to_complex_lorentz R := by
        rw [h_A_B, h_hom, hM_eq, ← hR_eq]
      have h_surj_eq : spinorPhi (A, B) = Λ := h_AB
      rw [h_surj_eq] at h_subst
      exact congrArg Subtype.val h_subst








lemma real_lorentz_action_im (R : ProperOrthochronousLorentzGroup) (v : Fin 4 → ℂ) :
    (fun k => ((real_to_complex_lorentz R • v) k).im) = R.val.val *ᵥ (fun k => (v k).im) := by
  ext k
  change (∑ j, (R.val.val k j : ℂ) * v j).im = ∑ j, R.val.val k j * (v j).im
  simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]


lemma real_lorentz_preserves_tube (n : ℕ) (R : ProperOrthochronousLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    (real_to_complex_lorentz R) • z ∈ forward_tube_n n := by
  dsimp [forward_tube_n] at hz ⊢
  intro i hi
  have hzi := hz i hi
  have h_im : (fun k => -(((real_to_complex_lorentz R • z i) k).im - ((real_to_complex_lorentz R • z ⟨i.val + 1, hi⟩) k).im)) =
              R.val.val *ᵥ (fun k => -((z i k).im - (z ⟨i.val + 1, hi⟩ k).im)) := by
    ext k
    have h1 := congr_fun (real_lorentz_action_im R (z i)) k
    have h2 := congr_fun (real_lorentz_action_im R (z ⟨i.val + 1, hi⟩)) k
    rw [h1, h2]
    change - (∑ j, R.val.val k j * (z i j).im - ∑ j, R.val.val k j * (z ⟨i.val + 1, hi⟩ j).im) = ∑ j, R.val.val k j * -((z i j).im - (z ⟨i.val + 1, hi⟩ j).im)
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [h_im]
  exact real_lorentz_preserves_forward_cone R _ hzi

lemma forward_tube_n_iff_posDef_im_spinor (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    z ∈ forward_tube_n n ↔ ∀ (i : Fin n) (hi : i.val + 1 < n),
      (vec_to_spinor (fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im)).PosDef := by
  dsimp [forward_tube_n]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [← posDef_vec_to_spinor_iff]
  congr! 2
  ext k
  push_cast
  rfl



lemma exp_iM_preserves_tube_aux (n : ℕ) (M : RealLorentzLieAlgebra)
    (P : SpecialLinearGroup (Fin 2) ℂ)
    (hM : spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (h_end : exp_iM M • z ∈ forward_tube_n n)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hdec :
      (∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (c : ℂ) (hc : c ≠ 0),
        0 ≤ c.re ∧
        P.val = P_c.val * (diag_matrix c hc).val * P_c.val⁻¹ ∧
        ∃ L L_inv : Matrix (Fin 4) (Fin 4) ℝ,
          (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)) ∧
          (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)) ∧
          M.val = 2 • (L * M_D c * L_inv)) ∨
      (∃ (P_c : SpecialLinearGroup (Fin 2) ℂ) (a s_a : ℂ) (h_s : s_a = 1 ∨ s_a = -1),
        P.val = P_c.val * !![s_a, a; 0, s_a] * P_c.val⁻¹ ∧
        ∃ L L_inv : Matrix (Fin 4) (Fin 4) ℝ,
          (spinorPhi (P_c, sl2c_conj P_c)).val.val = Matrix.map L (fun x => (x : ℂ)) ∧
          (spinorPhi (P_c⁻¹, sl2c_conj P_c⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)) ∧
          M.val = 2 • (L * M_J (s_a * a) * L_inv))) :
    exp_iM (s • M) • z ∈ forward_tube_n n := by
  rw [forward_tube_n_iff_posDef_im_spinor] at hz h_end ⊢
  intro i hi
  have h_z := hz i hi
  have h_z_end := h_end i hi

  have h_diff_end : (fun k => -(((exp_iM M • z) i - (exp_iM M • z) ⟨i.val + 1, hi⟩) k).im : Fin 4 → ℂ) = (fun k => -((exp_iM M • (fun k => z i k - z ⟨i.val + 1, hi⟩ k)) k).im : Fin 4 → ℂ) := by
    ext k
    have h_action : (exp_iM M • (fun k => z i k - z ⟨i.val + 1, hi⟩ k)) = (exp_iM M).val.val *ᵥ (z i - z ⟨i.val + 1, hi⟩) := rfl
    have h_action1 : (exp_iM M • z) i = (exp_iM M).val.val *ᵥ (z i) := rfl
    have h_action2 : (exp_iM M • z) ⟨i.val + 1, hi⟩ = (exp_iM M).val.val *ᵥ (z ⟨i.val + 1, hi⟩) := rfl
    rw [h_action, h_action1, h_action2]
    simp [Matrix.mulVec_sub]
  have h_diff_s : (fun k => -(((exp_iM (s • M) • z) i - (exp_iM (s • M) • z) ⟨i.val + 1, hi⟩) k).im : Fin 4 → ℂ) = (fun k => -((exp_iM (s • M) • (fun k => z i k - z ⟨i.val + 1, hi⟩ k)) k).im : Fin 4 → ℂ) := by
    ext k
    have h_action : (exp_iM (s • M) • (fun k => z i k - z ⟨i.val + 1, hi⟩ k)) = (exp_iM (s • M)).val.val *ᵥ (z i - z ⟨i.val + 1, hi⟩) := rfl
    have h_action1 : (exp_iM (s • M) • z) i = (exp_iM (s • M)).val.val *ᵥ (z i) := rfl
    have h_action2 : (exp_iM (s • M) • z) ⟨i.val + 1, hi⟩ = (exp_iM (s • M)).val.val *ᵥ (z ⟨i.val + 1, hi⟩) := rfl
    rw [h_action, h_action1, h_action2]
    simp [Matrix.mulVec_sub]

  rcases hdec with ⟨P_c, c, hc, hre, hP_eq, L, L_inv, hL, hL_inv, hM_eq⟩ | ⟨P_c, a, s_a, hs_a, hP_eq, L, L_inv, hL, hL_inv, hM_eq⟩
  · have h_action := exp_iM_action_eq_tube_F_diag_c M P P_c c hc hM hP_eq L L_inv hL hL_inv hM_eq (fun k => z i k - z ⟨i.val + 1, hi⟩ k) h_z s
    rcases h_action with ⟨X, Y, hX_herm, hY_pos, h_s, h_0, h_1⟩
    have hF1 : (tube_F_diag_c c X Y 1).PosDef := by
      apply posdef_congruence_inv _ P_c.val (ne_of_eq_of_ne P_c.property one_ne_zero)
      rw [← h_1, ← h_diff_end]
      exact h_z_end
    have hF_s_pos := tube_F_diag_c_posdef c X Y hX_herm hY_pos hF1
      (by rw [Complex.log_im]; exact Complex.abs_arg_le_pi_div_two_iff.mpr hre) s hs0 hs1
    have h_goal : (P_c.val * tube_F_diag_c c X Y s * P_c.valᴴ).PosDef := posdef_congruence _ P_c.val (ne_of_eq_of_ne P_c.property one_ne_zero) hF_s_pos
    rw [← h_s, ← h_diff_s] at h_goal
    exact h_goal
  · have h_action := exp_iM_action_eq_tube_F_jordan_c M P P_c a s_a hs_a hM hP_eq L L_inv hL hL_inv hM_eq (fun k => z i k - z ⟨i.val + 1, hi⟩ k) h_z s
    rcases h_action with ⟨X, Y, hX_herm, hY_pos, h_s, h_0, h_1⟩
    have hF1 : (tube_F_jordan_c (s_a * a) X Y 1).PosDef := by
      apply posdef_congruence_inv _ P_c.val (ne_of_eq_of_ne P_c.property one_ne_zero)
      rw [← h_1, ← h_diff_end]
      exact h_z_end
    have hF_s_pos := tube_F_jordan_c_posdef (s_a * a) X Y hX_herm hY_pos hF1 s hs0 hs1
    have h_goal : (P_c.val * tube_F_jordan_c (s_a * a) X Y s * P_c.valᴴ).PosDef := posdef_congruence _ P_c.val (ne_of_eq_of_ne P_c.property one_ne_zero) hF_s_pos
    rw [← h_s, ← h_diff_s] at h_goal
    exact h_goal

lemma sl_inv_val_fin2 (Q : SpecialLinearGroup (Fin 2) ℂ) :
    ((Q⁻¹ : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (Q : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, Matrix.SpecialLinearGroup.det_coe,
    Ring.inverse_one, one_smul]


lemma exp_iM_preserves_tube (n : ℕ) (M : RealLorentzLieAlgebra)
    (P : SpecialLinearGroup (Fin 2) ℂ)
    (hM : spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (h_end : exp_iM M • z ∈ forward_tube_n n) :
    ∃ M' : RealLorentzLieAlgebra, exp_iM M' = exp_iM M ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → exp_iM (s • M') • z ∈ forward_tube_n n := by
  rcases sl2c_jordan_decomp P with ⟨P_c, c, hc, hP_eq⟩ | ⟨P_c, a, s_a, hs_a, hP_eq⟩
  · obtain ⟨L, hL⟩ := spinorPhi_is_real P_c
    obtain ⟨L_inv, hL_inv⟩ := spinorPhi_is_real P_c⁻¹
    have hP_grp : P = P_c * (diag_matrix c hc) * P_c⁻¹ := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, sl_inv_val_fin2]
      exact hP_eq
    by_cases hre : 0 ≤ c.re
    · obtain ⟨M', hM'1, hM'2⟩ := M_eq_explicit_diag P P_c c hc hP_grp L L_inv hL hL_inv
      have hexp : exp_iM M' = exp_iM M := hM'1.symm.trans hM
      refine ⟨M', hexp, fun s hs0 hs1 => ?_⟩
      exact exp_iM_preserves_tube_aux n M' P hM'1 z hz (by rw [hexp]; exact h_end) s hs0 hs1
        (Or.inl ⟨P_c, c, hc, hre, hP_eq, L, L_inv, hL, hL_inv, hM'2⟩)
    · 
      have hre' : 0 ≤ (-c).re := by
        rw [Complex.neg_re]; linarith [not_le.mp hre]
      have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
      have hd_neg : (diag_matrix (-c) hc').val = -(diag_matrix c hc).val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diag_matrix]
      have hP'_val : P_c.val * (diag_matrix (-c) hc').val * P_c.val⁻¹ = (-P).val := by
        rw [Matrix.SpecialLinearGroup.coe_neg, hP_eq, hd_neg]
        simp
      have hP'_grp : -P = P_c * (diag_matrix (-c) hc') * P_c⁻¹ := by
        apply Subtype.ext
        simp only [Matrix.SpecialLinearGroup.coe_mul, sl_inv_val_fin2]
        exact hP'_val.symm
      obtain ⟨M', hM'1, hM'2⟩ := M_eq_explicit_diag (-P) P_c (-c) hc' hP'_grp L L_inv hL hL_inv
      have hexp : exp_iM M' = exp_iM M := by
        rw [← hM'1, spinorPhi_neg_conj, hM]
      refine ⟨M', hexp, fun s hs0 hs1 => ?_⟩
      exact exp_iM_preserves_tube_aux n M' (-P) hM'1 z hz (by rw [hexp]; exact h_end) s hs0 hs1
        (Or.inl ⟨P_c, -c, hc', hre', hP'_val.symm, L, L_inv, hL, hL_inv, hM'2⟩)
  · obtain ⟨L, hL⟩ := spinorPhi_is_real P_c
    obtain ⟨L_inv, hL_inv⟩ := spinorPhi_is_real P_c⁻¹
    have h_ne : s_a ≠ 0 := by rcases hs_a with h | h <;> simp [h]
    have h_mat : (diag_matrix s_a h_ne * jordan_matrix (s_a * a)).val = !![s_a, a; 0, s_a] := by
      rcases hs_a with rfl | rfl <;>
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [diag_matrix, jordan_matrix, J_mat, Matrix.mul_apply, Fin.sum_univ_two]
    have hP_grp : P = P_c * (diag_matrix s_a h_ne * jordan_matrix (s_a * a)) * P_c⁻¹ := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, sl_inv_val_fin2]
      have h_mat' : (diag_matrix s_a h_ne).val * (jordan_matrix (s_a * a)).val = !![s_a, a; 0, s_a] := by
        rw [← Matrix.SpecialLinearGroup.coe_mul]; exact h_mat
      rw [h_mat']
      exact hP_eq
    obtain ⟨M', hM'1, hM'2⟩ := M_eq_explicit_jordan P P_c a s_a hs_a hP_grp L L_inv hL hL_inv
    have hexp : exp_iM M' = exp_iM M := hM'1.symm.trans hM
    refine ⟨M', hexp, fun s hs0 hs1 => ?_⟩
    exact exp_iM_preserves_tube_aux n M' P hM'1 z hz (by rw [hexp]; exact h_end) s hs0 hs1
      (Or.inr ⟨P_c, a, s_a, hs_a, hP_eq, L, L_inv, hL, hL_inv, hM'2⟩)






@[simp] lemma real_to_complex_lorentz_one :
    real_to_complex_lorentz 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [real_to_complex_lorentz]

@[simp] lemma real_to_complex_lorentz_mul (R1 R2 : ProperOrthochronousLorentzGroup) :
    real_to_complex_lorentz (R1 * R2) = real_to_complex_lorentz R1 * real_to_complex_lorentz R2 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [real_to_complex_lorentz, Matrix.mul_apply]

@[simp] lemma exp_iM_zero : exp_iM 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [exp_iM, real_matrix_to_complex, lorentz_exp, NormedSpace.exp_zero]

@[continuity] lemma continuous_rmc : Continuous real_matrix_to_complex := by
  apply continuous_matrix
  intro i j
  change Continuous (fun M : Matrix (Fin 4) (Fin 4) ℝ => (M i j : ℂ))
  exact Complex.continuous_ofReal.comp (continuous_apply_apply i j)

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace Matrix.linftyOpIsBoundedSMul
attribute [local instance] Matrix.linftyOpNormSMulClass Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

@[continuity] lemma continuous_lorentz_exp : Continuous (fun M : Matrix (Fin 4) (Fin 4) ℂ => lorentz_exp M) := by
  dsimp [lorentz_exp]
  exact NormedSpace.exp_continuous

@[continuity] lemma continuous_exp_iM : Continuous exp_iM := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun M : RealLorentzLieAlgebra => lorentz_exp (I • real_matrix_to_complex M.val))
    have hc : Continuous (fun M : RealLorentzLieAlgebra => I • real_matrix_to_complex M.val) := by
      have hc1 : Continuous (fun M : RealLorentzLieAlgebra => (I : ℂ)) := continuous_const
      have hc2 : Continuous (fun M : RealLorentzLieAlgebra => real_matrix_to_complex M.val) := continuous_rmc.comp continuous_subtype_val
      exact hc1.smul hc2
    exact continuous_lorentz_exp.comp hc
  · change Continuous (fun M : RealLorentzLieAlgebra => lorentz_exp ((-I) • real_matrix_to_complex M.val))
    have hc : Continuous (fun M : RealLorentzLieAlgebra => (-I) • real_matrix_to_complex M.val) := by
      have hc1 : Continuous (fun M : RealLorentzLieAlgebra => (-I : ℂ)) := continuous_const
      have hc2 : Continuous (fun M : RealLorentzLieAlgebra => real_matrix_to_complex M.val) := continuous_rmc.comp continuous_subtype_val
      exact hc1.smul hc2
    exact continuous_lorentz_exp.comp hc


noncomputable def polar_decomp_path (R : ProperOrthochronousLorentzGroup) (M : RealLorentzLieAlgebra) :
    Path (exp_iM M * real_to_complex_lorentz R) (real_to_complex_lorentz R) where
  toFun := fun t => exp_iM ((1 - (t : ℝ)) • M) * real_to_complex_lorentz R
  continuous_toFun := by
    have hc_const : Continuous (fun (t : Set.Icc (0 : ℝ) 1) => real_to_complex_lorentz R) := continuous_const
    have hc_scalar : Continuous (fun (t : Set.Icc (0 : ℝ) 1) => (1 - (t : ℝ))) := continuous_const.sub continuous_subtype_val
    have hc_M : Continuous (fun (t : Set.Icc (0 : ℝ) 1) => M) := continuous_const
    have hc_smul : Continuous (fun (t : Set.Icc (0 : ℝ) 1) => (1 - (t : ℝ)) • M) := hc_scalar.smul hc_M
    have hc_exp : Continuous (fun (t : Set.Icc (0 : ℝ) 1) => exp_iM ((1 - (t : ℝ)) • M)) := continuous_exp_iM.comp hc_smul
    exact hc_exp.mul hc_const
  source' := by
    dsimp
    have h : 1 - (0 : ℝ) = 1 := sub_zero 1
    rw [h, one_smul]
  target' := by
    dsimp
    have h : 1 - (1 : ℝ) = 0 := sub_self 1
    rw [h, zero_smul, exp_iM_zero, one_mul]


lemma real_lorentz_preserves_tube_iff (n : ℕ) (R : ProperOrthochronousLorentzGroup)
    (w : Fin n → Fin 4 → ℂ) :
    (real_to_complex_lorentz R) • w ∈ forward_tube_n n ↔ w ∈ forward_tube_n n := by
  constructor
  · intro h
    have h2 := real_lorentz_preserves_tube n R⁻¹ _ h
    have h_inv : real_to_complex_lorentz R⁻¹ * real_to_complex_lorentz R = 1 := by
      rw [← real_to_complex_lorentz_mul, inv_mul_cancel, real_to_complex_lorentz_one]
    have h_smul : (real_to_complex_lorentz R⁻¹ * real_to_complex_lorentz R) • w = real_to_complex_lorentz R⁻¹ • real_to_complex_lorentz R • w := mul_smul _ _ _
    have h3 : (real_to_complex_lorentz R⁻¹ * real_to_complex_lorentz R) • w ∈ forward_tube_n n := by
      rw [h_smul]
      exact h2
    rw [h_inv] at h3
    have h_one : (1 : SpecialSpecialComplexLorentzGroup) • w = w := one_smul _ w
    rwa [h_one] at h3
  · exact real_lorentz_preserves_tube n R w

lemma joined_pos (n : ℕ) (Λ : SpecialSpecialComplexLorentzGroup)
    (R : ProperOrthochronousLorentzGroup) (M : RealLorentzLieAlgebra)
    (P : SpecialLinearGroup (Fin 2) ℂ) (hP : 0 ≤ (P.val : Matrix (Fin 2) (Fin 2) ℂ).trace.re)
    (hM : spinorPhi (P, (sl2c_conj P)⁻¹) = exp_iM M)
    (h_pos : Λ.val = (exp_iM M * real_to_complex_lorentz R).val)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (hΛ : Λ • z ∈ forward_tube_n n) :
    ∃ R' : ProperOrthochronousLorentzGroup, Joined Λ (real_to_complex_lorentz R') ∧
      ∃ γ : Path Λ (real_to_complex_lorentz R'),
        ∀ t, γ t • z ∈ forward_tube_n n := by
  have h_eq : Λ = exp_iM M * real_to_complex_lorentz R := Subtype.ext h_pos
  subst h_eq
  have h1 : (real_to_complex_lorentz R) • z ∈ forward_tube_n n := real_lorentz_preserves_tube n R z hz
  have h2 : exp_iM M • (real_to_complex_lorentz R • z) ∈ forward_tube_n n := by
    have h_smul : exp_iM M • real_to_complex_lorentz R • z = (exp_iM M * real_to_complex_lorentz R) • z := (mul_smul _ _ _).symm
    rw [h_smul]
    exact hΛ
  obtain ⟨M', hexp, h_flow⟩ := exp_iM_preserves_tube n M P hM (real_to_complex_lorentz R • z) h1 h2
  rw [← hexp]
  use R
  constructor
  · exact ⟨polar_decomp_path R M'⟩
  · use polar_decomp_path R M'
    intro t
    have h_param_1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.property.2]
    have h_param_2 : 1 - (t : ℝ) ≤ 1 := by linarith [t.property.1]
    have h3 := h_flow (1 - (t : ℝ)) h_param_1 h_param_2
    have h_path : (polar_decomp_path R M') t • z = exp_iM ((1 - (t : ℝ)) • M') • (real_to_complex_lorentz R • z) := by
      exact (mul_smul (exp_iM ((1 - (t : ℝ)) • M')) (real_to_complex_lorentz R) z)
    rw [h_path]
    exact h3

lemma real_linear_pos_implies_zero (v0 w0 : ℝ) (h : ∀ k : ℝ, 0 ≤ k * v0 + w0) : v0 = 0 := by
  by_contra h_neq
  rcases lt_or_gt_of_ne h_neq with h_lt | h_gt
  · let k := (-w0 - 1) / v0
    have hk : k * v0 + w0 = -1 := by
      calc k * v0 + w0 = ((-w0 - 1) / v0) * v0 + w0 := rfl
        _ = (-w0 - 1) + w0 := by rw [div_mul_cancel₀ _ (ne_of_lt h_lt)]
        _ = -1 := by ring
    have h1 := h k
    rw [hk] at h1
    norm_num at h1
  · let k := (-w0 - 1) / v0
    have hk : k * v0 + w0 = -1 := by
      calc k * v0 + w0 = ((-w0 - 1) / v0) * v0 + w0 := rfl
        _ = (-w0 - 1) + w0 := by rw [div_mul_cancel₀ _ (ne_of_gt h_gt)]
        _ = -1 := by ring
    have h1 := h k
    rw [hk] at h1
    norm_num at h1

lemma real_quadratic_bounded (v w C : ℝ) (hC : 0 ≤ C) (h : ∀ k : ℝ, (k * v + w)^2 ≤ C) : v = 0 := by
  by_contra h_neq
  let k := (C + 1 - w) / v
  have hk : k * v + w = C + 1 := by
    calc k * v + w = ((C + 1 - w) / v) * v + w := rfl
      _ = (C + 1 - w) + w := by rw [div_mul_cancel₀ _ h_neq]
      _ = C + 1 := by ring
  have h1 := h k
  rw [hk] at h1
  nlinarith



lemma orbit_domain_joined_to_real (n : ℕ) (hn : 2 ≤ n) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (hΛ : Λ • z ∈ forward_tube_n n) :
    ∃ R : ProperOrthochronousLorentzGroup, Joined Λ (real_to_complex_lorentz R) ∧
      ∃ γ : Path Λ (real_to_complex_lorentz R),
        ∀ t, γ t • z ∈ forward_tube_n n := by
  have h_polar := sscl_polar_decomp_of_tube_preserver n hn Λ z hz hΛ
  rcases h_polar with ⟨R, M, P, hP_trace, hM, h_eq⟩
  exact joined_pos n Λ R M P hP_trace hM h_eq z hz hΛ

lemma is_real_givens_proper_xy (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (RealGivens.givens_xy c s)ᵀ * minkowskiMetricReal * RealGivens.givens_xy c s = minkowskiMetricReal ∧
    (RealGivens.givens_xy c s).det = 1 ∧
    (RealGivens.givens_xy c s) 0 0 > 0 := by
  have h_lor := IsRealGivens_lorentz (IsRealGivens.xy c s h)
  refine ⟨h_lor, ?_, ?_⟩
  · have H : (RealGivens.givens_xy c s).det = c ^ 2 + s ^ 2 := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_xy, Fin.succAbove]
      ring
    rw [H, h]
  · change (RealGivens.givens_xy c s) 0 0 > 0
    dsimp [RealGivens.givens_xy]
    exact zero_lt_one

lemma is_real_givens_proper_zx (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (RealGivens.givens_zx c s)ᵀ * minkowskiMetricReal * RealGivens.givens_zx c s = minkowskiMetricReal ∧
    (RealGivens.givens_zx c s).det = 1 ∧
    (RealGivens.givens_zx c s) 0 0 > 0 := by
  have h_lor := IsRealGivens_lorentz (IsRealGivens.zx c s h)
  refine ⟨h_lor, ?_, ?_⟩
  · have H : (RealGivens.givens_zx c s).det = c ^ 2 + s ^ 2 := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_zx, Fin.succAbove]
      ring
    rw [H, h]
  · change (RealGivens.givens_zx c s) 0 0 > 0
    dsimp [RealGivens.givens_zx]
    exact zero_lt_one

lemma is_real_givens_proper_tx (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (hpos : c > 0) :
    (RealGivens.givens_t_x c s)ᵀ * minkowskiMetricReal * RealGivens.givens_t_x c s = minkowskiMetricReal ∧
    (RealGivens.givens_t_x c s).det = 1 ∧
    (RealGivens.givens_t_x c s) 0 0 > 0 := by
  have h_lor := IsRealGivens_lorentz (IsRealGivens.tx c s h hpos)
  refine ⟨h_lor, ?_, ?_⟩
  · have H : (RealGivens.givens_t_x c s).det = c ^ 2 - s ^ 2 := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_t_x, Fin.succAbove]
      ring
    rw [H, h]
  · change (RealGivens.givens_t_x c s) 0 0 > 0
    dsimp [RealGivens.givens_t_x]
    exact hpos

lemma is_real_givens_proper_one :
    (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * minkowskiMetricReal * 1 = minkowskiMetricReal ∧
    (1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1 ∧
    (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 0 > 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · exact Matrix.det_one
  · change (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 0 > 0
    simp

lemma is_real_givens_proper_mul (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : IsRealGivens A) (hB : IsRealGivens B)
    (ihA : Aᵀ * minkowskiMetricReal * A = minkowskiMetricReal ∧ A.det = 1 ∧ A 0 0 > 0)
    (ihB : Bᵀ * minkowskiMetricReal * B = minkowskiMetricReal ∧ B.det = 1 ∧ B 0 0 > 0) :
    (A * B)ᵀ * minkowskiMetricReal * (A * B) = minkowskiMetricReal ∧
    (A * B).det = 1 ∧
    (A * B) 0 0 > 0 := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (A * B)ᵀ * minkowskiMetricReal * (A * B)
        = Bᵀ * Aᵀ * minkowskiMetricReal * (A * B) := by rw [Matrix.transpose_mul]
      _ = Bᵀ * (Aᵀ * minkowskiMetricReal * A) * B := by simp only [Matrix.mul_assoc]
      _ = Bᵀ * minkowskiMetricReal * B := by rw [ihA.1]
      _ = minkowskiMetricReal := ihB.1
  · rw [Matrix.det_mul, ihA.2.1, ihB.2.1, mul_one]
  · let A_GL : Matrix.GeneralLinearGroup (Fin 4) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [ihA.2.1]; exact one_ne_zero)
    let B_GL : Matrix.GeneralLinearGroup (Fin 4) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero B (by rw [ihB.2.1]; exact one_ne_zero)
    have hA_metric : A_GL.valᵀ * minkowskiMetricReal * A_GL.val = minkowskiMetricReal := ihA.1
    have hB_metric : B_GL.valᵀ * minkowskiMetricReal * B_GL.val = minkowskiMetricReal := ihB.1
    have hA_row := lorentz_row_eq A_GL hA_metric
    have ha_sq : A 0 0 ^ 2 = 1 + A 0 1 ^ 2 + A 0 2 ^ 2 + A 0 3 ^ 2 := lorentz_row_00_sq A_GL hA_row
    have hb_sq : B 0 0 ^ 2 = 1 + B 1 0 ^ 2 + B 2 0 ^ 2 + B 3 0 ^ 2 := lorentz_col_00_sq B_GL hB_metric
    have h_exp : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 0 2 * B 2 0 + A 0 3 * B 3 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_four]
    rw [h_exp]
    exact sq_sum_ineq (A 0 0) (A 0 1) (A 0 2) (A 0 3) (B 0 0) (B 1 0) (B 2 0) (B 3 0) ha_sq ihA.2.2 hb_sq ihB.2.2

lemma is_real_givens_proper (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : IsRealGivens G) :
    Gᵀ * minkowskiMetricReal * G = minkowskiMetricReal ∧ G.det = 1 ∧ G 0 0 > 0 := by
  induction hG with
  | xy c s h => exact is_real_givens_proper_xy c s h
  | zx c s h => exact is_real_givens_proper_zx c s h
  | tx c s h hpos => exact is_real_givens_proper_tx c s h hpos
  | one => exact is_real_givens_proper_one
  | mul hA hB ihA ihB => exact is_real_givens_proper_mul _ _ hA hB ihA ihB

noncomputable def real_givens_pol (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : IsRealGivens G) :
    ProperOrthochronousLorentzGroup :=
  have hP := is_real_givens_proper G hG
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G (by
     have hdet := hP.2.1
     rw [hdet]
     exact one_ne_zero),
   hP⟩


lemma continuous_matrix_4x4 {α : Type*} [TopologicalSpace α]
  (m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33 : α → ℝ)
  (h00 : Continuous m00) (h01 : Continuous m01) (h02 : Continuous m02) (h03 : Continuous m03)
  (h10 : Continuous m10) (h11 : Continuous m11) (h12 : Continuous m12) (h13 : Continuous m13)
  (h20 : Continuous m20) (h21 : Continuous m21) (h22 : Continuous m22) (h23 : Continuous m23)
  (h30 : Continuous m30) (h31 : Continuous m31) (h32 : Continuous m32) (h33 : Continuous m33) :
  Continuous (fun x => !![m00 x, m01 x, m02 x, m03 x;
                           m10 x, m11 x, m12 x, m13 x;
                           m20 x, m21 x, m22 x, m23 x;
                           m30 x, m31 x, m32 x, m33 x]) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h02
  · exact h03
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h30
  · exact h31
  · exact h32
  · exact h33


lemma continuous_circle_path (c s : ℝ) : Continuous (fun t => circle_path c s t) := by
  dsimp [circle_path]; continuity

lemma continuous_tx_path (s : ℝ) : Continuous (fun t => tx_path s t) := by
  dsimp [tx_path]; continuity

lemma continuous_givens_xy_path (c s : ℝ) :
    Continuous (fun t => RealGivens.givens_xy (circle_path c s t).1 (circle_path c s t).2) := by
  dsimp [RealGivens.givens_xy]
  apply continuous_matrix_4x4
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).fst
  · exact (continuous_circle_path c s).snd.neg
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).snd
  · exact (continuous_circle_path c s).fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

lemma continuous_givens_xy_inv_path (c s : ℝ) :
    Continuous (fun t => RealGivens.givens_xy (circle_path c s t).1 (-(circle_path c s t).2)) := by
  dsimp [RealGivens.givens_xy]
  apply continuous_matrix_4x4
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).fst
  · exact (continuous_circle_path c s).snd.neg.neg
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).snd.neg
  · exact (continuous_circle_path c s).fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

lemma RealGivens.givens_xy_mul_inv_eq_one (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    RealGivens.givens_xy c s * RealGivens.givens_xy c (-s) = 1 := by
  ext i j
  dsimp [Matrix.mul_apply, dotProduct]
  have H1 : c * c + s * s = 1 := by
    calc
      c * c + s * s = c ^ 2 + s ^ 2 := by ring
      _ = 1 := h
  have H2 : s * s + c * c = 1 := by
    calc
      s * s + c * c = c ^ 2 + s ^ 2 := by ring
      _ = 1 := h
  fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_xy, Fin.sum_univ_four]
  <;> (try exact H1)
  <;> (try exact H2)
  <;> ring

noncomputable def RealGivens.givens_xy_path (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ℝ → ProperOrthochronousLorentzGroup := fun t =>
  real_givens_pol (RealGivens.givens_xy (circle_path c s t).1 (circle_path c s t).2) (IsRealGivens.xy _ _ (circle_path_sq c s t))

lemma RealGivens.givens_xy_path_continuous (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Continuous (RealGivens.givens_xy_path c s h) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_givens_xy_path c s
  · have h_inv : Continuous (fun x => (RealGivens.givens_xy (circle_path c s x).1 (-(circle_path c s x).2))) :=
      continuous_givens_xy_inv_path c s
    have Heq : (fun x => ((RealGivens.givens_xy_path c s h x).val).inv) = (fun x => (RealGivens.givens_xy (circle_path c s x).1 (-(circle_path c s x).2))) := by
      funext x
      have h1 : ((RealGivens.givens_xy_path c s h x).val).val * RealGivens.givens_xy (circle_path c s x).1 (-(circle_path c s x).2) = 1 :=
        RealGivens.givens_xy_mul_inv_eq_one (circle_path c s x).1 (circle_path c s x).2 (circle_path_sq c s x)
      have h2 : ((RealGivens.givens_xy_path c s h x).val).inv * (((RealGivens.givens_xy_path c s h x).val).val * RealGivens.givens_xy (circle_path c s x).1 (-(circle_path c s x).2)) = ((RealGivens.givens_xy_path c s h x).val).inv * 1 := by rw [h1]
      rw [← Matrix.mul_assoc] at h2
      have h3 : ((RealGivens.givens_xy_path c s h x).val).inv * ((RealGivens.givens_xy_path c s h x).val).val = 1 := ((RealGivens.givens_xy_path c s h x).val).inv_val
      rw [h3, Matrix.one_mul, Matrix.mul_one] at h2
      exact h2.symm
    change Continuous (fun x => ((RealGivens.givens_xy_path c s h x).val).inv)
    rw [Heq]
    exact h_inv

lemma xy_joined (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Joined (real_givens_pol (RealGivens.givens_xy c s) (IsRealGivens.xy c s h)) 1 := by
  let p : Path (real_givens_pol (RealGivens.givens_xy c s) (IsRealGivens.xy c s h)) 1 := {
    toFun := fun t => RealGivens.givens_xy_path c s h (t : ℝ)
    continuous_toFun := Continuous.comp (RealGivens.givens_xy_path_continuous c s h) continuous_subtype_val
    source' := by
      ext i j
      change RealGivens.givens_xy (circle_path c s 0).1 (circle_path c s 0).2 i j = RealGivens.givens_xy c s i j
      have h0 := circle_path_0 c s h
      rw [h0]
    target' := by
      ext i j
      change RealGivens.givens_xy (circle_path c s 1).1 (circle_path c s 1).2 i j = (1 : Matrix (Fin 4) (Fin 4) ℝ) i j
      have h1 := circle_path_1 c s
      rw [h1]
      fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_xy]
  }
  exact ⟨p⟩


lemma continuous_givens_zx_path (c s : ℝ) :
    Continuous (fun t => RealGivens.givens_zx (circle_path c s t).1 (circle_path c s t).2) := by
  dsimp [RealGivens.givens_zx]
  apply continuous_matrix_4x4
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).fst
  · exact continuous_const
  · exact (continuous_circle_path c s).snd
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).snd.neg
  · exact continuous_const
  · exact (continuous_circle_path c s).fst

lemma continuous_givens_zx_inv_path (c s : ℝ) :
    Continuous (fun t => RealGivens.givens_zx (circle_path c s t).1 (-(circle_path c s t).2)) := by
  dsimp [RealGivens.givens_zx]
  apply continuous_matrix_4x4
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).fst
  · exact continuous_const
  · exact (continuous_circle_path c s).snd.neg
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_circle_path c s).snd.neg.neg
  · exact continuous_const
  · exact (continuous_circle_path c s).fst


lemma RealGivens.givens_zx_mul_inv_eq_one (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    RealGivens.givens_zx c s * RealGivens.givens_zx c (-s) = 1 := by
  ext i j
  dsimp [Matrix.mul_apply, dotProduct]
  have H1 : c * c + s * s = 1 := by
    calc
      c * c + s * s = c ^ 2 + s ^ 2 := by ring
      _ = 1 := h
  have H2 : s * s + c * c = 1 := by
    calc
      s * s + c * c = c ^ 2 + s ^ 2 := by ring
      _ = 1 := h
  fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_zx, Fin.sum_univ_four]
  <;> (try exact H1)
  <;> (try exact H2)
  <;> ring

noncomputable def RealGivens.givens_zx_path (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ℝ → ProperOrthochronousLorentzGroup := fun t =>
  real_givens_pol (RealGivens.givens_zx (circle_path c s t).1 (circle_path c s t).2) (IsRealGivens.zx _ _ (circle_path_sq c s t))

lemma RealGivens.givens_zx_path_continuous (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Continuous (RealGivens.givens_zx_path c s h) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_givens_zx_path c s
  · have h_inv : Continuous (fun x => (RealGivens.givens_zx (circle_path c s x).1 (-(circle_path c s x).2))) :=
      continuous_givens_zx_inv_path c s
    have Heq : (fun x => ((RealGivens.givens_zx_path c s h x).val).inv) = (fun x => (RealGivens.givens_zx (circle_path c s x).1 (-(circle_path c s x).2))) := by
      funext x
      have h1 : ((RealGivens.givens_zx_path c s h x).val).val * RealGivens.givens_zx (circle_path c s x).1 (-(circle_path c s x).2) = 1 :=
        RealGivens.givens_zx_mul_inv_eq_one (circle_path c s x).1 (circle_path c s x).2 (circle_path_sq c s x)
      have h2 : ((RealGivens.givens_zx_path c s h x).val).inv * (((RealGivens.givens_zx_path c s h x).val).val * RealGivens.givens_zx (circle_path c s x).1 (-(circle_path c s x).2)) = ((RealGivens.givens_zx_path c s h x).val).inv * 1 := by rw [h1]
      rw [← Matrix.mul_assoc] at h2
      have h3 : ((RealGivens.givens_zx_path c s h x).val).inv * ((RealGivens.givens_zx_path c s h x).val).val = 1 := ((RealGivens.givens_zx_path c s h x).val).inv_val
      rw [h3, Matrix.one_mul, Matrix.mul_one] at h2
      exact h2.symm
    change Continuous (fun x => ((RealGivens.givens_zx_path c s h x).val).inv)
    rw [Heq]
    exact h_inv

lemma zx_joined (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Joined (real_givens_pol (RealGivens.givens_zx c s) (IsRealGivens.zx c s h)) 1 := by
  let p : Path (real_givens_pol (RealGivens.givens_zx c s) (IsRealGivens.zx c s h)) 1 := {
    toFun := fun t => RealGivens.givens_zx_path c s h (t : ℝ)
    continuous_toFun := Continuous.comp (RealGivens.givens_zx_path_continuous c s h) continuous_subtype_val
    source' := by
      ext i j
      change RealGivens.givens_zx (circle_path c s 0).1 (circle_path c s 0).2 i j = RealGivens.givens_zx c s i j
      have h0 := circle_path_0 c s h
      rw [h0]
    target' := by
      ext i j
      change RealGivens.givens_zx (circle_path c s 1).1 (circle_path c s 1).2 i j = (1 : Matrix (Fin 4) (Fin 4) ℝ) i j
      have h1 := circle_path_1 c s
      rw [h1]
      fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_zx]
  }
  exact ⟨p⟩


lemma continuous_givens_t_x_path (s : ℝ) :
    Continuous (fun t => RealGivens.givens_t_x (tx_path s t).1 (tx_path s t).2) := by
  dsimp [RealGivens.givens_t_x]
  apply continuous_matrix_4x4
  · exact (continuous_tx_path s).fst
  · exact (continuous_tx_path s).snd.neg
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_tx_path s).snd.neg
  · exact (continuous_tx_path s).fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

lemma continuous_givens_t_x_inv_path (s : ℝ) :
    Continuous (fun t => RealGivens.givens_t_x (tx_path s t).1 (-(tx_path s t).2)) := by
  dsimp [RealGivens.givens_t_x]
  apply continuous_matrix_4x4
  · exact (continuous_tx_path s).fst
  · exact (continuous_tx_path s).snd.neg.neg
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_tx_path s).snd.neg.neg
  · exact (continuous_tx_path s).fst
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const


lemma RealGivens.givens_t_x_mul_inv_eq_one (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) :
    RealGivens.givens_t_x c s * RealGivens.givens_t_x c (-s) = 1 := by
  ext i j
  dsimp [Matrix.mul_apply, dotProduct]
  have H1 : c * c + -(s * s) = 1 := by
    calc
      c * c + -(s * s) = c ^ 2 - s ^ 2 := by ring
      _ = 1 := h
  have H2 : -(s * s) + c * c = 1 := by
    calc
      -(s * s) + c * c = c ^ 2 - s ^ 2 := by ring
      _ = 1 := h
  fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_t_x, Fin.sum_univ_four]
  <;> (try exact H1)
  <;> (try exact H2)
  <;> ring

noncomputable def givens_tx_path (s : ℝ) : ℝ → ProperOrthochronousLorentzGroup := fun t =>
  real_givens_pol (RealGivens.givens_t_x (tx_path s t).1 (tx_path s t).2) (IsRealGivens.tx _ _ (tx_path_sq s t) (tx_path_c_pos s t))

lemma givens_tx_path_continuous (s : ℝ) : Continuous (givens_tx_path s) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_givens_t_x_path s
  · have h_inv : Continuous (fun x => (RealGivens.givens_t_x (tx_path s x).1 (-(tx_path s x).2))) :=
      continuous_givens_t_x_inv_path s
    have Heq : (fun x => ((givens_tx_path s x).val).inv) = (fun x => (RealGivens.givens_t_x (tx_path s x).1 (-(tx_path s x).2))) := by
      funext x
      have h1 : ((givens_tx_path s x).val).val * RealGivens.givens_t_x (tx_path s x).1 (-(tx_path s x).2) = 1 :=
        RealGivens.givens_t_x_mul_inv_eq_one (tx_path s x).1 (tx_path s x).2 (tx_path_sq s x)
      have h2 : ((givens_tx_path s x).val).inv * (((givens_tx_path s x).val).val * RealGivens.givens_t_x (tx_path s x).1 (-(tx_path s x).2)) = ((givens_tx_path s x).val).inv * 1 := by rw [h1]
      rw [← Matrix.mul_assoc] at h2
      have h3 : ((givens_tx_path s x).val).inv * ((givens_tx_path s x).val).val = 1 := ((givens_tx_path s x).val).inv_val
      rw [h3, Matrix.one_mul, Matrix.mul_one] at h2
      exact h2.symm
    change Continuous (fun x => ((givens_tx_path s x).val).inv)
    rw [Heq]
    exact h_inv

lemma tx_joined (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (hpos : c > 0) :
    Joined (real_givens_pol (RealGivens.givens_t_x c s) (IsRealGivens.tx c s h hpos)) 1 := by
  let p : Path (real_givens_pol (RealGivens.givens_t_x c s) (IsRealGivens.tx c s h hpos)) 1 := {
    toFun := fun t => givens_tx_path s (t : ℝ)
    continuous_toFun := Continuous.comp (givens_tx_path_continuous s) continuous_subtype_val
    source' := by
      ext i j
      change RealGivens.givens_t_x (tx_path s 0).1 (tx_path s 0).2 i j = RealGivens.givens_t_x c s i j
      have h0 := tx_path_0 c s h hpos
      rw [h0]
    target' := by
      ext i j
      change RealGivens.givens_t_x (tx_path s 1).1 (tx_path s 1).2 i j = (1 : Matrix (Fin 4) (Fin 4) ℝ) i j
      have h1 := tx_path_1 s
      rw [h1]
      fin_cases i <;> fin_cases j <;> simp [RealGivens.givens_t_x]
  }
  exact ⟨p⟩

lemma joined_mul {a b c d : ProperOrthochronousLorentzGroup} (h1 : Joined a b) (h2 : Joined c d) : Joined (a * c) (b * d) := by
  rcases h1 with ⟨p1⟩
  rcases h2 with ⟨p2⟩
  let p3 : Path (a * c) (b * d) := {
    toFun := fun t => p1 t * p2 t
    continuous_toFun := Continuous.mul p1.continuous p2.continuous
    source' := by simp
    target' := by simp
  }
  exact ⟨p3⟩

lemma real_givens_joined_to_id (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : IsRealGivens G) :
    Joined (real_givens_pol G hG) 1 := by
  induction hG with
  | xy c s h => exact xy_joined c s h
  | zx c s h => exact zx_joined c s h
  | tx c s h hpos => exact tx_joined c s h hpos
  | one =>
    have h_one : real_givens_pol 1 IsRealGivens.one = 1 := by
      apply Subtype.ext; apply Units.ext; rfl
    rw [h_one]
  | mul hA hB ihA ihB =>
    have h_prod : real_givens_pol _ (IsRealGivens.mul hA hB) = real_givens_pol _ hA * real_givens_pol _ hB := by
      apply Subtype.ext; apply Units.ext; rfl
    rw [h_prod]
    have H := joined_mul ihA ihB
    rw [mul_one] at H
    exact H

lemma det_xy (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (RealGivens.givens_xy c s).det = 1 := by
  have H : (RealGivens.givens_xy c s).det = c ^ 2 + s ^ 2 := by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_xy, Fin.succAbove]
    ring
  rw [H, h]

lemma det_zx (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (RealGivens.givens_zx c s).det = 1 := by
  have H : (RealGivens.givens_zx c s).det = c ^ 2 + s ^ 2 := by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_zx, Fin.succAbove]
    ring
  rw [H, h]

lemma det_t_x (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) : (RealGivens.givens_t_x c s).det = 1 := by
  have H : (RealGivens.givens_t_x c s).det = c ^ 2 - s ^ 2 := by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, RealGivens.givens_t_x, Fin.succAbove]
    ring
  rw [H, h]

lemma IsRealGivens_det {G : Matrix (Fin 4) (Fin 4) ℝ} (h : IsRealGivens G) : Matrix.det G = 1 := by
  induction h with
  | xy c s hcs => exact det_xy c s hcs
  | zx c s hcs => exact det_zx c s hcs
  | tx c s hcs hpos => exact det_t_x c s hcs
  | one => exact Matrix.det_one
  | mul A B ihA ihB => simp [Matrix.det_mul, ihA, ihB]

lemma mul_lorentz_matrix {A B : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : Aᵀ * minkowskiMetricReal * A = minkowskiMetricReal)
    (hB : Bᵀ * minkowskiMetricReal * B = minkowskiMetricReal) :
    (A * B)ᵀ * minkowskiMetricReal * (A * B) = minkowskiMetricReal := by
  calc
    (A * B)ᵀ * minkowskiMetricReal * (A * B) = Bᵀ * (Aᵀ * minkowskiMetricReal * A) * B := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Bᵀ * minkowskiMetricReal * B := by rw [hA]
    _ = minkowskiMetricReal := hB

lemma givens_xy_lorentz (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (RealGivens.givens_xy c s)ᵀ * minkowskiMetricReal * RealGivens.givens_xy c s = minkowskiMetricReal :=
  RealGivens.givens_xy_is_lorentz c s hcs

lemma givens_zx_lorentz (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (RealGivens.givens_zx c s)ᵀ * minkowskiMetricReal * RealGivens.givens_zx c s = minkowskiMetricReal :=
  RealGivens.givens_zx_is_lorentz c s hcs

lemma givens_tx_lorentz (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (RealGivens.givens_t_x c s)ᵀ * minkowskiMetricReal * RealGivens.givens_t_x c s = minkowskiMetricReal :=
  RealGivens.givens_t_x_is_lorentz c s hcs

lemma IsRealGivens_lorentz_matrix {G : Matrix (Fin 4) (Fin 4) ℝ} (h : IsRealGivens G) :
    Gᵀ * minkowskiMetricReal * G = minkowskiMetricReal := by
  induction h with
  | xy c s hcs => exact givens_xy_lorentz c s hcs
  | zx c s hcs => exact givens_zx_lorentz c s hcs
  | tx c s hcs hpos => exact givens_tx_lorentz c s hcs
  | one => simp [Matrix.transpose_one]
  | mul A B ihA ihB => exact mul_lorentz_matrix ihA ihB


lemma isrealgivens_inv_exists_mul_left
    {A B A' B' : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A' * A = 1) (hB : B' * B = 1) :
    (B' * A') * (A * B) = 1 := by
  calc
    (B' * A') * (A * B) = B' * (A' * (A * B)) := Matrix.mul_assoc B' A' (A * B)
    _ = B' * ((A' * A) * B) := by rw [← Matrix.mul_assoc A' A B]
    _ = B' * (1 * B) := by rw [hA]
    _ = B' * B := by rw [Matrix.one_mul]
    _ = 1 := hB

lemma isrealgivens_inv_exists_mul_right
    {A B A' B' : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A * A' = 1) (hB : B * B' = 1) :
    (A * B) * (B' * A') = 1 := by
  calc
    (A * B) * (B' * A') = A * (B * (B' * A')) := Matrix.mul_assoc A B (B' * A')
    _ = A * ((B * B') * A') := by rw [← Matrix.mul_assoc B B' A']
    _ = A * (1 * A') := by rw [hB]
    _ = A * A' := by rw [Matrix.one_mul]
    _ = 1 := hA

lemma IsRealGivens_inv_exists {G : Matrix (Fin 4) (Fin 4) ℝ} (h : IsRealGivens G) :
    ∃ G', IsRealGivens G' ∧ G' * G = 1 ∧ G * G' = 1 := by
  induction h with
  | xy c s hcs =>
    use RealGivens.givens_xy c (-s)
    have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by
      calc
        c ^ 2 + (-s) ^ 2 = c ^ 2 + s ^ 2 := by ring
        _ = 1 := hcs
    refine ⟨IsRealGivens.xy c (-s) hcs', ?_, ?_⟩
    · have h1 : RealGivens.givens_xy c (-s) * RealGivens.givens_xy c (-(-s)) = 1 :=
        RealGivens.givens_xy_mul_inv_eq_one c (-s) hcs'
      have h2 : -(-s) = s := by ring
      rw [h2] at h1
      exact h1
    · exact RealGivens.givens_xy_mul_inv_eq_one c s hcs
  | zx c s hcs =>
    use RealGivens.givens_zx c (-s)
    have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by
      calc
        c ^ 2 + (-s) ^ 2 = c ^ 2 + s ^ 2 := by ring
        _ = 1 := hcs
    refine ⟨IsRealGivens.zx c (-s) hcs', ?_, ?_⟩
    · have h1 : RealGivens.givens_zx c (-s) * RealGivens.givens_zx c (-(-s)) = 1 :=
        RealGivens.givens_zx_mul_inv_eq_one c (-s) hcs'
      have h2 : -(-s) = s := by ring
      rw [h2] at h1
      exact h1
    · exact RealGivens.givens_zx_mul_inv_eq_one c s hcs
  | tx c s hcs hpos =>
    use RealGivens.givens_t_x c (-s)
    have hcs' : c ^ 2 - (-s) ^ 2 = 1 := by
      calc
        c ^ 2 - (-s) ^ 2 = c ^ 2 - s ^ 2 := by ring
        _ = 1 := hcs
    refine ⟨IsRealGivens.tx c (-s) hcs' hpos, ?_, ?_⟩
    · have h1 : RealGivens.givens_t_x c (-s) * RealGivens.givens_t_x c (-(-s)) = 1 :=
        RealGivens.givens_t_x_mul_inv_eq_one c (-s) hcs'
      have h2 : -(-s) = s := by ring
      rw [h2] at h1
      exact h1
    · exact RealGivens.givens_t_x_mul_inv_eq_one c s hcs
  | one =>
    use 1
    refine ⟨IsRealGivens.one, Matrix.mul_one 1, Matrix.one_mul 1⟩
  | mul A B ihA ihB =>
    rcases ihA with ⟨A', hA', hA'_mul, h_mul_A'⟩
    rcases ihB with ⟨B', hB', hB'_mul, h_mul_B'⟩
    use B' * A'
    refine ⟨IsRealGivens.mul hB' hA', ?_, ?_⟩
    · exact isrealgivens_inv_exists_mul_left hA'_mul hB'_mul
    · exact isrealgivens_inv_exists_mul_right h_mul_A' h_mul_B'


@[continuity] lemma continuous_real_to_complex_lorentz : Continuous real_to_complex_lorentz := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun R : ProperOrthochronousLorentzGroup => real_matrix_to_complex R.val.val)
    have hc_val : Continuous (fun R : ProperOrthochronousLorentzGroup => R.val.val) := Units.continuous_val.comp continuous_subtype_val
    exact continuous_rmc.comp hc_val
  · change Continuous (fun R : ProperOrthochronousLorentzGroup => real_matrix_to_complex R⁻¹.val.val)
    have hc_inv : Continuous (fun R : ProperOrthochronousLorentzGroup => R⁻¹.val.val) := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
    exact continuous_rmc.comp hc_inv






abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

noncomputable def su2ToSL2C (U : SU2) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨U.val, (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2⟩

lemma su2ToSL2C_injective : Function.Injective su2ToSL2C := by
  intro U V h
  apply Subtype.ext
  have h1 : (su2ToSL2C U).1 = (su2ToSL2C V).1 := by rw [h]
  exact h1

lemma su2ToSL2C_continuous : Continuous su2ToSL2C :=
  Continuous.subtype_mk continuous_subtype_val _





lemma diag_exp_det (w : ℂ) :
    (!![(Complex.exp w), (0:ℂ); 0, Complex.exp (-w)] :
      Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [det_fin_two]; simp [← Complex.exp_add]

noncomputable def diagExpSL2C (w : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![(Complex.exp w), (0:ℂ); 0, Complex.exp (-w)], diag_exp_det w⟩

@[simp]
lemma diagExpSL2C_zero : diagExpSL2C 0 = 1 := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagExpSL2C, Complex.exp_zero]

@[simp]
lemma diagExpSL2C_val (w : ℂ) :
    (diagExpSL2C w : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Complex.exp w), (0:ℂ); 0, Complex.exp (-w)] := rfl

lemma diagExpSL2C_continuous : Continuous diagExpSL2C := by
  apply Continuous.subtype_mk _ _
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply]
  · 
    exact Complex.continuous_exp.comp continuous_id
  · 
    exact continuous_const
  · 
    exact continuous_const
  · 
    exact Complex.continuous_exp.comp continuous_neg

lemma diagExpSL2C_joined_one (w : ℂ) :
    Joined (1 : Matrix.SpecialLinearGroup (Fin 2) ℂ) (diagExpSL2C w) :=
  sl2c_joined_one_diag w





noncomputable def boostHalfSL2C (θ : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  diagExpSL2C (-(Complex.I * (θ : ℂ) / 2))

@[simp]
lemma boostHalfSL2C_zero : boostHalfSL2C 0 = 1 := by
  dsimp [boostHalfSL2C]
  have h : -(Complex.I * (0 : ℂ) / 2) = 0 := by simp
  rw [h]
  exact diagExpSL2C_zero

lemma boostHalfSL2C_val (θ : ℝ) :
    (boostHalfSL2C θ : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.exp (-(Complex.I * θ / 2)), (0:ℂ); 0, Complex.exp (Complex.I * θ / 2)] := by
  simp [boostHalfSL2C, diagExpSL2C]

lemma boostHalfSL2C_continuous : Continuous boostHalfSL2C := by
  apply diagExpSL2C_continuous.comp
  continuity

lemma diag_mul_matrix_mul_diag_trans (a d : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
  !![a, (0:ℂ); 0, d] * X * !![a, 0; 0, d]ᵀ =
  !![a * X 0 0 * a, a * X 0 1 * d;
     d * X 1 0 * a, d * X 1 1 * d] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (!![a, 0; 0, d] * X * !![a, 0; 0, d]ᵀ) 0 0 = a * X 0 0 * a
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [Matrix.transpose_apply]
  · change (!![a, 0; 0, d] * X * !![a, 0; 0, d]ᵀ) 0 1 = a * X 0 1 * d
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [Matrix.transpose_apply]
  · change (!![a, 0; 0, d] * X * !![a, 0; 0, d]ᵀ) 1 0 = d * X 1 0 * a
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [Matrix.transpose_apply]
  · change (!![a, 0; 0, d] * X * !![a, 0; 0, d]ᵀ) 1 1 = d * X 1 1 * d
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [Matrix.transpose_apply]

lemma spinor_action_diag (a d : ℂ) (x : Fin 4 → ℂ) :
  spinor_action !![a, 0; 0, d] !![a, 0; 0, d] x =
  ![ (a^2 * (x 0 + x 3) + d^2 * (x 0 - x 3)) / 2,
     a * d * x 1,
     a * d * x 2,
     (a^2 * (x 0 + x 3) - d^2 * (x 0 - x 3)) / 2 ] := by
  ext k
  rw [spinor_action, diag_mul_matrix_mul_diag_trans]
  fin_cases k
  · dsimp [spinor_to_vec, vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
    ring
  · dsimp [spinor_to_vec, vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
    ring
  · dsimp [spinor_to_vec, vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
    ring_nf
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [hI]
    ring
  · dsimp [spinor_to_vec, vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
    ring

lemma complex_exp_identity_1 (θ : ℝ) :
    Complex.exp (-(Complex.I * ↑θ / 2)) ^ 2 = Complex.exp (-(Complex.I * ↑θ)) := by
  have : Complex.exp (-(Complex.I * ↑θ / 2)) ^ 2 = Complex.exp (-(Complex.I * ↑θ / 2)) * Complex.exp (-(Complex.I * ↑θ / 2)) := by ring
  rw [this, ← Complex.exp_add]; ring_nf

lemma complex_exp_identity_2 (θ : ℝ) :
    Complex.exp (Complex.I * ↑θ / 2) ^ 2 = Complex.exp (Complex.I * ↑θ) := by
  have : Complex.exp (Complex.I * ↑θ / 2) ^ 2 = Complex.exp (Complex.I * ↑θ / 2) * Complex.exp (Complex.I * ↑θ / 2) := by ring
  rw [this, ← Complex.exp_add]; ring_nf

lemma complex_exp_identity_3 (θ : ℝ) :
    Complex.exp (-(Complex.I * ↑θ / 2)) * Complex.exp (Complex.I * ↑θ / 2) = 1 := by
  rw [← Complex.exp_add]
  have : -(Complex.I * ↑θ / 2) + Complex.I * ↑θ / 2 = 0 := by ring
  rw [this]
  exact Complex.exp_zero

lemma complex_exp_identity_4 (θ : ℝ) :
    Complex.exp (Complex.I * ↑θ / 2) * Complex.exp (-(Complex.I * ↑θ / 2)) = 1 := by
  rw [← Complex.exp_add]
  have : Complex.I * ↑θ / 2 + -(Complex.I * ↑θ / 2) = 0 := by ring
  rw [this]
  exact Complex.exp_zero


lemma spinorPhi_boost_mulVec (θ : ℝ) (x : Fin 4 → ℂ) :
    mulVec (spinorPhi_matrix (boostHalfSL2C θ) (boostHalfSL2C θ)) x =
    ![↑(Real.cos θ) * x 0 + (-Complex.I * Real.sin θ) * x 3,
       x 1,
       x 2,
       (-Complex.I * Real.sin θ) * x 0 + ↑(Real.cos θ) * x 3] := by
  ext k
  rw [spinorPhi_matrix_mulVec]
  have hA : (boostHalfSL2C θ : Matrix (Fin 2) (Fin 2) ℂ) =
            !![Complex.exp (-(Complex.I * θ / 2)), (0:ℂ); 0, Complex.exp (Complex.I * θ / 2)] :=
    boostHalfSL2C_val θ

  rw [hA, spinor_action_diag]
  fin_cases k
  · dsimp
    rw [complex_exp_identity_1 θ, complex_exp_identity_2 θ]
    simp [Complex.cos, Complex.sin]
    ring_nf
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [hI2]
    ring
  · dsimp
    rw [complex_exp_identity_3 θ]
    ring
  · dsimp
    rw [complex_exp_identity_3 θ]
    ring
  · dsimp
    rw [complex_exp_identity_1 θ, complex_exp_identity_2 θ]
    simp [Complex.cos, Complex.sin]
    ring_nf
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [hI2]
    ring


lemma spinorPhi_boost_matrix (θ : ℝ) :
    spinorPhi_matrix (boostHalfSL2C θ) (boostHalfSL2C θ) = complex_boost_z θ := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_boost_mulVec]
  ext k
  rw [Matrix.mulVec_apply_eq_sum]
  fin_cases k
  · simp [complex_boost_z, Fin.sum_univ_four]
  · simp [complex_boost_z, Fin.sum_univ_four]
  · simp [complex_boost_z, Fin.sum_univ_four]
  · simp [complex_boost_z, Fin.sum_univ_four]






lemma spinorPhi_boost_val (θ : ℝ) :
    (spinorPhi (boostHalfSL2C θ, boostHalfSL2C θ)).val.val = complex_boost_z θ :=
  spinorPhi_boost_matrix θ


lemma spinorPhi_boost_continuous :
    Continuous (fun θ : ℝ => spinorPhi (boostHalfSL2C θ, boostHalfSL2C θ)) :=
  continuous_spinorPhi.comp (boostHalfSL2C_continuous.prodMk boostHalfSL2C_continuous)


@[simp]
lemma spinorPhi_boost_zero :
    spinorPhi (boostHalfSL2C (0:ℝ), boostHalfSL2C (0:ℝ)) = 1 := by
  have h : (boostHalfSL2C (0:ℝ), boostHalfSL2C (0:ℝ)) = (1, 1) := by
    simp [boostHalfSL2C_zero]
  rw [h]
  exact map_one spinorPhi


lemma spinorPhi_boost_joined (θ₀ : ℝ) :
    Joined (1 : SpecialSpecialComplexLorentzGroup)
           (spinorPhi (boostHalfSL2C θ₀, boostHalfSL2C θ₀)) := by
  refine ⟨⟨⟨fun t => spinorPhi (boostHalfSL2C ((t : ℝ) * θ₀),
                                  boostHalfSL2C ((t : ℝ) * θ₀)),
    spinorPhi_boost_continuous.comp (continuous_subtype_val.mul_const θ₀)⟩,
    ?_, ?_⟩⟩
  · change spinorPhi (boostHalfSL2C (0 * θ₀), boostHalfSL2C (0 * θ₀)) = 1
    simp
    exact map_one spinorPhi
  · change spinorPhi (boostHalfSL2C (1 * θ₀), boostHalfSL2C (1 * θ₀)) = _
    simp
lemma complex_lorentz_inv (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : Aᵀ * minkowskiMetric * A = minkowskiMetric) :
  A * (minkowskiMetric * Aᵀ * minkowskiMetric) = 1 ∧ (minkowskiMetric * Aᵀ * minkowskiMetric) * A = 1 := by
  have h_minkowskiMetric_sq : minkowskiMetric * (minkowskiMetric : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]
  have h_left : (minkowskiMetric * Aᵀ * minkowskiMetric) * A = 1 := by
    have h1 : (minkowskiMetric * Aᵀ * minkowskiMetric) * A = minkowskiMetric * (Aᵀ * minkowskiMetric * A) := by
      simp [Matrix.mul_assoc]
    rw [h1, hA, h_minkowskiMetric_sq]
  have h_right : A * (minkowskiMetric * Aᵀ * minkowskiMetric) = 1 := mul_eq_one_comm.mpr h_left
  exact ⟨h_right, h_left⟩

noncomputable def complex_boost_z_sscl (θ : ℝ) : SpecialSpecialComplexLorentzGroup :=
  let M := complex_boost_z θ
  have hL := complex_boost_z_is_lorentz θ
  have hd := complex_boost_z_det θ
  let Minv := minkowskiMetric * Mᵀ * minkowskiMetric
  ⟨{ val := M,
     inv := Minv,
     val_inv := (complex_lorentz_inv M hL).1,
     inv_val := (complex_lorentz_inv M hL).2 },
   hL, hd⟩



lemma lorentz_zero_y (R : Matrix (Fin 4) (Fin 4) ℝ) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1), (RealGivens.givens_xy c s * R) 2 0 = 0 := by
  let r_sq := R 1 0 ^ 2 + R 2 0 ^ 2
  by_cases hr : r_sq = 0
  · 
    use 1, 0
    refine ⟨by norm_num, ?_⟩
    have h_r20 : R 2 0 = 0 := by
      have h1 : 0 ≤ R 1 0 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ R 2 0 ^ 2 := sq_nonneg _
      have h3 : R 2 0 ^ 2 = 0 := by linarith
      exact sq_eq_zero_iff.mp h3
    simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h_r20]
  · 
    have hr_pos : 0 < r_sq := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
    let r := Real.sqrt r_sq
    have hr_nz : r ≠ 0 := Real.sqrt_ne_zero'.mpr hr_pos
    let c := R 1 0 / r
    let s := -(R 2 0) / r
    use c, s
    refine ⟨?_, ?_⟩
    · calc
        c ^ 2 + s ^ 2 = (R 1 0 ^ 2) / (r ^ 2) + (-(R 2 0)) ^ 2 / (r ^ 2) := by ring
        _ = (R 1 0 ^ 2) / r_sq + (R 2 0 ^ 2) / r_sq := by
          congr 1
          · rw [Real.sq_sqrt (le_of_lt hr_pos)]
          · congr 1
            · exact neg_sq _
            · rw [Real.sq_sqrt (le_of_lt hr_pos)]
        _ = (R 1 0 ^ 2 + R 2 0 ^ 2) / r_sq := by ring
        _ = 1 := div_self hr
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      calc
        -(R 2 0) / r * R 1 0 + R 1 0 / r * R 2 0 = (-(R 2 0 * R 1 0) + R 1 0 * R 2 0) / r := by ring
        _ = 0 := by ring

lemma lorentz_zero_z (R : Matrix (Fin 4) (Fin 4) ℝ) (hy : R 2 0 = 0) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1), (RealGivens.givens_zx c s * R) 3 0 = (0 : ℝ) ∧ (RealGivens.givens_zx c s * R) 2 0 = (0 : ℝ) := by
  let r_sq := R 1 0 ^ 2 + R 3 0 ^ 2
  by_cases hr : r_sq = 0
  · use 1, 0
    refine ⟨by norm_num, ?_, ?_⟩
    · have h_r30 : R 3 0 = 0 := by
        have h1 : 0 ≤ R 1 0 ^ 2 := sq_nonneg _
        have h2 : 0 ≤ R 3 0 ^ 2 := sq_nonneg _
        have h3 : R 3 0 ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp h3
      simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h_r30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, hy]
  · have hr_pos : 0 < r_sq := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
    let r := Real.sqrt r_sq
    have hr_nz : r ≠ 0 := Real.sqrt_ne_zero'.mpr hr_pos
    let c := R 1 0 / r
    let s := R 3 0 / r
    use c, s
    refine ⟨?_, ?_, ?_⟩
    · calc
        c ^ 2 + s ^ 2 = (R 1 0 ^ 2) / (r ^ 2) + (R 3 0) ^ 2 / (r ^ 2) := by ring
        _ = (R 1 0 ^ 2) / r_sq + (R 3 0 ^ 2) / r_sq := by
          congr 1
          · rw [Real.sq_sqrt (le_of_lt hr_pos)]
          · congr 1
            · rw [Real.sq_sqrt (le_of_lt hr_pos)]
        _ = (R 1 0 ^ 2 + R 3 0 ^ 2) / r_sq := by ring
        _ = 1 := div_self hr
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx]
      change -(s * R 1 0) + c * R 3 0 = 0
      dsimp [s, c]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, hy]

lemma lorentz_reduce_t (R : Matrix (Fin 4) (Fin 4) ℝ)
    (h_lorentz : Rᵀ * minkowskiMetricReal * R = minkowskiMetricReal)
    (h_ortho : R 0 0 > 0)
    (hy : R 2 0 = 0) (hz : R 3 0 = 0) :
    ∃ (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (hpos : c > 0),
    (RealGivens.givens_t_x c s * R) 1 0 = 0 ∧ (RealGivens.givens_t_x c s * R) 2 0 = 0 ∧ (RealGivens.givens_t_x c s * R) 3 0 = 0 ∧ (RealGivens.givens_t_x c s * R) 0 0 = 1 := by
  let c := R 0 0
  let s := R 1 0
  use c, s
  
  have h_M00 : (Rᵀ * minkowskiMetricReal * R) 0 0 = 1 := by rw [h_lorentz]; rfl
  have h_eq : (Rᵀ * minkowskiMetricReal * R) 0 0 = R 0 0 ^ 2 - R 1 0 ^ 2 - R 2 0 ^ 2 - R 3 0 ^ 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
    ring
  have h_eq2 : R 0 0 ^ 2 - R 1 0 ^ 2 = 1 := by
    calc
      R 0 0 ^ 2 - R 1 0 ^ 2 = R 0 0 ^ 2 - R 1 0 ^ 2 - R 2 0 ^ 2 - R 3 0 ^ 2 := by rw [hy, hz]; ring
      _ = (Rᵀ * minkowskiMetricReal * R) 0 0 := h_eq.symm
      _ = 1 := h_M00
  refine ⟨h_eq2, h_ortho, ?_, ?_, ?_, ?_⟩
  · simp [RealGivens.givens_t_x, Matrix.mul_apply, Fin.sum_univ_four]
    change -(s * c) + c * s = 0
    ring
  · simp [RealGivens.givens_t_x, Matrix.mul_apply, Fin.sum_univ_four, hy]
  · simp [RealGivens.givens_t_x, Matrix.mul_apply, Fin.sum_univ_four, hz]
  · simp [RealGivens.givens_t_x, Matrix.mul_apply, Fin.sum_univ_four]
    change c * c - s * s = 1
    calc
      c * c - s * s = c ^ 2 - s ^ 2 := by ring
      _ = 1 := h_eq2




lemma lorentz_row_zero (R : Matrix (Fin 4) (Fin 4) ℝ)
    (h_lorentz : Rᵀ * minkowskiMetricReal * R = minkowskiMetricReal)
    (h00 : R 0 0 = 1) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h30 : R 3 0 = 0) :
    R 0 1 = 0 ∧ R 0 2 = 0 ∧ R 0 3 = 0 := by
  have h_01 : (Rᵀ * minkowskiMetricReal * R) 0 1 = 0 := by rw [h_lorentz]; rfl
  have h_02 : (Rᵀ * minkowskiMetricReal * R) 0 2 = 0 := by rw [h_lorentz]; rfl
  have h_03 : (Rᵀ * minkowskiMetricReal * R) 0 3 = 0 := by rw [h_lorentz]; rfl
  have eq_01 : (Rᵀ * minkowskiMetricReal * R) 0 1 = R 0 0 * R 0 1 - R 1 0 * R 1 1 - R 2 0 * R 2 1 - R 3 0 * R 3 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
    ring
  have eq_02 : (Rᵀ * minkowskiMetricReal * R) 0 2 = R 0 0 * R 0 2 - R 1 0 * R 1 2 - R 2 0 * R 2 2 - R 3 0 * R 3 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
    ring
  have eq_03 : (Rᵀ * minkowskiMetricReal * R) 0 3 = R 0 0 * R 0 3 - R 1 0 * R 1 3 - R 2 0 * R 2 3 - R 3 0 * R 3 3 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
    ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      R 0 1 = R 0 0 * R 0 1 - R 1 0 * R 1 1 - R 2 0 * R 2 1 - R 3 0 * R 3 1 := by rw [h00, h10, h20, h30]; ring
      _ = (Rᵀ * minkowskiMetricReal * R) 0 1 := eq_01.symm
      _ = 0 := h_01
  · calc
      R 0 2 = R 0 0 * R 0 2 - R 1 0 * R 1 2 - R 2 0 * R 2 2 - R 3 0 * R 3 2 := by rw [h00, h10, h20, h30]; ring
      _ = (Rᵀ * minkowskiMetricReal * R) 0 2 := eq_02.symm
      _ = 0 := h_02
  · calc
      R 0 3 = R 0 0 * R 0 3 - R 1 0 * R 1 3 - R 2 0 * R 2 3 - R 3 0 * R 3 3 := by rw [h00, h10, h20, h30]; ring
      _ = (Rᵀ * minkowskiMetricReal * R) 0 3 := eq_03.symm
      _ = 0 := h_03




lemma lorentz_zero_y_col3 (R : Matrix (Fin 4) (Fin 4) ℝ)
    (h00 : R 0 0 = 1) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h30 : R 3 0 = 0)
    (h01 : R 0 1 = 0) (h02 : R 0 2 = 0) (h03 : R 0 3 = 0) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1), (RealGivens.givens_xy c s * R) 2 3 = 0 ∧
    (RealGivens.givens_xy c s * R) 1 0 = 0 ∧ (RealGivens.givens_xy c s * R) 2 0 = 0 ∧
    (RealGivens.givens_xy c s * R) 0 0 = 1 ∧ (RealGivens.givens_xy c s * R) 3 0 = 0 := by
  let r_sq := R 1 3 ^ 2 + R 2 3 ^ 2
  by_cases hr : r_sq = 0
  · use 1, 0
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · have h_r23 : R 2 3 = 0 := by
        have h1 : 0 ≤ R 1 3 ^ 2 := sq_nonneg _
        have h2 : 0 ≤ R 2 3 ^ 2 := sq_nonneg _
        have h3 : R 2 3 ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp h3
      simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h_r23]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h00, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h30]
  · have hr_pos : 0 < r_sq := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
    let r := Real.sqrt r_sq
    have hr_nz : r ≠ 0 := Real.sqrt_ne_zero'.mpr hr_pos
    let c := R 1 3 / r
    let s := -(R 2 3) / r
    use c, s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        c ^ 2 + s ^ 2 = (R 1 3 ^ 2) / (r ^ 2) + (R 2 3) ^ 2 / (r ^ 2) := by ring
        _ = (R 1 3 ^ 2) / r_sq + (R 2 3 ^ 2) / r_sq := by
          congr 1
          · rw [Real.sq_sqrt (le_of_lt hr_pos)]
          · congr 1
            · rw [Real.sq_sqrt (le_of_lt hr_pos)]
        _ = (R 1 3 ^ 2 + R 2 3 ^ 2) / r_sq := by ring
        _ = 1 := div_self hr
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      change s * R 1 3 + c * R 2 3 = 0
      dsimp [s, c]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h00, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h30]




lemma lorentz_zero_x_col3 (R : Matrix (Fin 4) (Fin 4) ℝ)
    (h_lorentz : Rᵀ * minkowskiMetricReal * R = minkowskiMetricReal)
    (h00 : R 0 0 = 1) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h30 : R 3 0 = 0)
    (h03 : R 0 3 = 0) (h23 : R 2 3 = 0) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1), (RealGivens.givens_zx c s * R) 1 3 = 0 ∧
    (RealGivens.givens_zx c s * R) 1 0 = 0 ∧ (RealGivens.givens_zx c s * R) 2 0 = 0 ∧
    (RealGivens.givens_zx c s * R) 0 0 = 1 ∧ (RealGivens.givens_zx c s * R) 3 0 = 0 ∧
    (RealGivens.givens_zx c s * R) 2 3 = 0 ∧ (RealGivens.givens_zx c s * R) 3 3 = 1 := by
  let r_sq := R 1 3 ^ 2 + R 3 3 ^ 2
  by_cases hr : r_sq = 0
  · use 1, 0
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h_r13 : R 1 3 = 0 := by
        have h1 : 0 ≤ R 1 3 ^ 2 := sq_nonneg _
        have h2 : 0 ≤ R 3 3 ^ 2 := sq_nonneg _
        have h3 : R 1 3 ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp h3
      simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h_r13]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h10, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h00]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h10, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h23]
    · have h_eq : (Rᵀ * minkowskiMetricReal * R) 3 3 = -1 := by rw [h_lorentz]; rfl
      have h_eq2 : (Rᵀ * minkowskiMetricReal * R) 3 3 = R 0 3 ^ 2 - R 1 3 ^ 2 - R 2 3 ^ 2 - R 3 3 ^ 2 := by
        simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
        ring
      have h_eq3 : R 1 3 ^ 2 + R 3 3 ^ 2 = 1 := by
        calc
          R 1 3 ^ 2 + R 3 3 ^ 2 = -(R 0 3 ^ 2 - R 1 3 ^ 2 - R 2 3 ^ 2 - R 3 3 ^ 2) := by rw [h03, h23]; ring
          _ = -((Rᵀ * minkowskiMetricReal * R) 3 3) := by rw [h_eq2]
          _ = -(-1) := by rw [h_eq]
          _ = 1 := by norm_num
      have h_contra : (0 : ℝ) = 1 := by
        calc
          0 = r_sq := hr.symm
          _ = R 1 3 ^ 2 + R 3 3 ^ 2 := rfl
          _ = 1 := h_eq3
      exact False.elim (by linarith)
  · have hr_pos : 0 < r_sq := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
    let r := Real.sqrt r_sq
    have hr_nz : r ≠ 0 := Real.sqrt_ne_zero'.mpr hr_pos
    let c := R 3 3 / r
    let s := -(R 1 3) / r
    use c, s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        c ^ 2 + s ^ 2 = (R 3 3 ^ 2) / (r ^ 2) + (R 1 3) ^ 2 / (r ^ 2) := by ring
        _ = (R 3 3 ^ 2) / r_sq + (R 1 3 ^ 2) / r_sq := by
          congr 1
          · rw [Real.sq_sqrt (le_of_lt hr_pos)]
          · congr 1
            · rw [Real.sq_sqrt (le_of_lt hr_pos)]
        _ = (R 1 3 ^ 2 + R 3 3 ^ 2) / r_sq := by ring
        _ = 1 := div_self hr
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx]
      change c * R 1 3 + s * R 3 3 = 0
      dsimp [s, c]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h10, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h00]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h10, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx, h23]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_zx]
      have h_eq : (Rᵀ * minkowskiMetricReal * R) 3 3 = -1 := by rw [h_lorentz]; rfl
      have h_eq2 : (Rᵀ * minkowskiMetricReal * R) 3 3 = R 0 3 ^ 2 - R 1 3 ^ 2 - R 2 3 ^ 2 - R 3 3 ^ 2 := by
        simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMetricReal]
        ring
      have h_eq3 : R 1 3 ^ 2 + R 3 3 ^ 2 = 1 := by
        calc
          R 1 3 ^ 2 + R 3 3 ^ 2 = -(R 0 3 ^ 2 - R 1 3 ^ 2 - R 2 3 ^ 2 - R 3 3 ^ 2) := by rw [h03, h23]; ring
          _ = -((Rᵀ * minkowskiMetricReal * R) 3 3) := by rw [h_eq2]
          _ = -(-1) := by rw [h_eq]
          _ = 1 := by norm_num
      have h_r_sq : r_sq = 1 := h_eq3
      have h_r_sq : r_sq = 1 := h_eq3
      have h_r : r = 1 := by
        dsimp [r]
        rw [h_r_sq, Real.sqrt_one]
      have h_s : -(-R 1 3 / r * R 1 3) + R 3 3 / r * R 3 3 = (R 1 3 ^ 2 + R 3 3 ^ 2) / r := by ring
      rw [h_s, h_eq3, h_r]
      norm_num




lemma lorentz_zero_y_col1 (R : Matrix (Fin 4) (Fin 4) ℝ)
    (h00 : R 0 0 = 1) (h10 : R 1 0 = 0) (h20 : R 2 0 = 0) (h30 : R 3 0 = 0)
    (h01 : R 0 1 = 0) :
    ∃ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1), (RealGivens.givens_xy c s * R) 2 1 = 0 ∧
    (RealGivens.givens_xy c s * R) 1 0 = 0 ∧ (RealGivens.givens_xy c s * R) 2 0 = 0 ∧
    (RealGivens.givens_xy c s * R) 0 0 = 1 ∧ (RealGivens.givens_xy c s * R) 3 0 = 0 ∧
    (RealGivens.givens_xy c s * R) 3 3 = R 3 3 ∧ (RealGivens.givens_xy c s * R) 1 3 = c * R 1 3 - s * R 2 3 ∧
    (RealGivens.givens_xy c s * R) 2 3 = s * R 1 3 + c * R 2 3 ∧
    0 ≤ (RealGivens.givens_xy c s * R) 1 1 := by
  let r_sq := R 1 1 ^ 2 + R 2 1 ^ 2
  by_cases hr : r_sq = 0
  · use 1, 0
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h_r21 : R 2 1 = 0 := by
        have h1 : 0 ≤ R 1 1 ^ 2 := sq_nonneg _
        have h2 : 0 ≤ R 2 1 ^ 2 := sq_nonneg _
        have h3 : R 2 1 ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp h3
      simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h_r21]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h00, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      have h11 : R 1 1 = 0 := by
        have h1 : 0 ≤ R 1 1 ^ 2 := sq_nonneg _
        have h2 : 0 ≤ R 2 1 ^ 2 := sq_nonneg _
        have h3 : R 1 1 ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp h3
      rw [h11]
  · have hr_pos : 0 < r_sq := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hr)
    let r := Real.sqrt r_sq
    have hr_nz : r ≠ 0 := Real.sqrt_ne_zero'.mpr hr_pos
    let c := R 1 1 / r
    let s := -(R 2 1) / r
    use c, s
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        c ^ 2 + s ^ 2 = (R 1 1 ^ 2) / (r ^ 2) + (R 2 1) ^ 2 / (r ^ 2) := by ring
        _ = (R 1 1 ^ 2) / r_sq + (R 2 1 ^ 2) / r_sq := by
          congr 1
          · rw [Real.sq_sqrt (le_of_lt hr_pos)]
          · congr 1
            · rw [Real.sq_sqrt (le_of_lt hr_pos)]
        _ = (R 1 1 ^ 2 + R 2 1 ^ 2) / r_sq := by ring
        _ = 1 := div_self hr
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      change s * R 1 1 + c * R 2 1 = 0
      dsimp [s, c]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h00, h10, h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy, h30]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
    · simp [Matrix.mul_apply, Fin.sum_univ_four, RealGivens.givens_xy]
      have h_r : c * R 1 1 - s * R 2 1 = r := by
        dsimp [s, c]
        calc
          (R 1 1 / r) * R 1 1 - (-(R 2 1) / r) * R 2 1 = (R 1 1 ^ 2 + R 2 1 ^ 2) / r := by ring
          _ = r_sq / r := by rfl
          _ = r_sq / Real.sqrt r_sq := by rfl
          _ = Real.sqrt r_sq := by rw [div_eq_iff hr_nz]; exact (Real.mul_self_sqrt (le_of_lt hr_pos)).symm
      have h_sqrt : 0 ≤ r := Real.sqrt_nonneg _
      linarith


lemma lorentz_M6_eq_one (M6 : Matrix (Fin 4) (Fin 4) ℝ)
    (hM6_lorentz : M6ᵀ * minkowskiMetricReal * M6 = minkowskiMetricReal)
    (h_det : Matrix.det M6 = 1)
    (h00 : M6 0 0 = 1) (h10 : M6 1 0 = 0) (h20 : M6 2 0 = 0) (h30 : M6 3 0 = 0)
    (h33 : M6 3 3 = 1) (h13 : M6 1 3 = 0) (h23 : M6 2 3 = 0) (h03 : M6 0 3 = 0)
    (h21 : M6 2 1 = 0)
    (h11_pos : 0 ≤ M6 1 1) : M6 = 1 := by
  have eq01 : (M6ᵀ * minkowskiMetricReal * M6) 0 1 = minkowskiMetricReal 0 1 := by rw [hM6_lorentz]
  have eq02 : (M6ᵀ * minkowskiMetricReal * M6) 0 2 = minkowskiMetricReal 0 2 := by rw [hM6_lorentz]
  have eq31 : (M6ᵀ * minkowskiMetricReal * M6) 3 1 = minkowskiMetricReal 3 1 := by rw [hM6_lorentz]
  have eq32 : (M6ᵀ * minkowskiMetricReal * M6) 3 2 = minkowskiMetricReal 3 2 := by rw [hM6_lorentz]
  have eq11 : (M6ᵀ * minkowskiMetricReal * M6) 1 1 = minkowskiMetricReal 1 1 := by rw [hM6_lorentz]
  have eq12 : (M6ᵀ * minkowskiMetricReal * M6) 1 2 = minkowskiMetricReal 1 2 := by rw [hM6_lorentz]

  simp [minkowskiMetricReal, Matrix.mul_apply, Fin.sum_univ_four, h00, h10, h20, h30, h33, h13, h23, h03, h21] at eq01 eq02 eq31 eq32 eq11 eq12

  have h01 : M6 0 1 = 0 := by linarith
  have h02 : M6 0 2 = 0 := by linarith
  have h31 : M6 3 1 = 0 := by linarith
  have h32 : M6 3 2 = 0 := by linarith

  have h11_sq : M6 1 1 ^ 2 = 1 := by
    calc
      M6 1 1 ^ 2 = M6 1 1 ^ 2 - M6 0 1 ^ 2 + M6 3 1 ^ 2 := by rw [h01, h31]; ring
      _ = 1 := by linarith

  have h11 : M6 1 1 = 1 := by nlinarith [h11_sq, h11_pos]

  have h12 : M6 1 2 = 0 := by
    calc
      M6 1 2 = M6 1 1 * M6 1 2 := by rw [h11]; ring
      _ = M6 1 1 * M6 1 2 - M6 0 1 * M6 0 2 + M6 3 1 * M6 3 2 := by rw [h01, h31, h02, h32]; ring
      _ = 0 := by linarith [eq12]

  have h_m6_diag : M6 = Matrix.diagonal ![1, 1, M6 2 2, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h23, h30, h31, h32, h33]

  have h22 : M6 2 2 = 1 := by
    have h_det_calc : Matrix.det M6 = M6 2 2 := by
      rw [h_m6_diag, det_diagonal]
      simp [Fin.prod_univ_four]
    rw [← h_det_calc]
    exact h_det

  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]


lemma givens_xy_row0 (c s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
  (RealGivens.givens_xy c s * M) 0 j = M 0 j := by
  simp [RealGivens.givens_xy, Matrix.mul_apply, Fin.sum_univ_four]

lemma givens_zx_row0 (c s : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
  (RealGivens.givens_zx c s * M) 0 j = M 0 j := by
  simp [RealGivens.givens_zx, Matrix.mul_apply, Fin.sum_univ_four]

lemma proper_lorentz_reduce_to_id (R : ProperOrthochronousLorentzGroup) :
    ∃ G, IsRealGivens G ∧ G * R.val.val = 1 := by
  let M := R.val.val
  have hM_lorentz : Mᵀ * minkowskiMetricReal * M = minkowskiMetricReal := R.property.1
  have hM_det : Matrix.det M = 1 := R.property.2.1
  have hM_00 : 0 < M 0 0 := R.property.2.2
  
  rcases lorentz_zero_y M with ⟨c1, s1, h1, h_y0⟩
  let G1 := RealGivens.givens_xy c1 s1
  let M1 := G1 * M
  have hG1 : IsRealGivens G1 := IsRealGivens.xy c1 s1 h1
  have hM1_lorentz : M1ᵀ * minkowskiMetricReal * M1 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG1) hM_lorentz
  
  rcases lorentz_zero_z M1 h_y0 with ⟨c2, s2, h2, h_z0, h_y0_2⟩
  let G2 := RealGivens.givens_zx c2 s2
  let M2 := G2 * M1
  have hG2 : IsRealGivens G2 := IsRealGivens.zx c2 s2 h2
  have hM2_lorentz : M2ᵀ * minkowskiMetricReal * M2 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG2) hM1_lorentz
  have hM1_00 : M1 0 0 = M 0 0 := givens_xy_row0 c1 s1 M 0
  have hM2_00 : M2 0 0 = M1 0 0 := givens_zx_row0 c2 s2 M1 0
  have hM2_00_pos : 0 < M2 0 0 := by
    rw [hM2_00, hM1_00]
    exact hM_00
  
  rcases lorentz_reduce_t M2 hM2_lorentz hM2_00_pos h_y0_2 h_z0 with ⟨c3, s3, h3, hpos3, h_x0⟩
  let G3 := RealGivens.givens_t_x c3 s3
  let M3 := G3 * M2
  have hG3 : IsRealGivens G3 := IsRealGivens.tx c3 s3 h3 hpos3
  have h_m3_10 : M3 1 0 = 0 := h_x0.1
  have h_m3_20 : M3 2 0 = 0 := h_x0.2.1
  have h_m3_30 : M3 3 0 = 0 := h_x0.2.2.1
  have h_m3_00 : M3 0 0 = 1 := h_x0.2.2.2
  have hM3_lorentz : M3ᵀ * minkowskiMetricReal * M3 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG3) hM2_lorentz
  
  rcases lorentz_row_zero M3 hM3_lorentz h_m3_00 h_m3_10 h_m3_20 h_m3_30 with ⟨h_m3_01, h_m3_02, h_m3_03⟩
  
  rcases lorentz_zero_y_col3 M3 h_m3_00 h_m3_10 h_m3_20 h_m3_30 h_m3_01 h_m3_02 h_m3_03 with ⟨c4, s4, h4, h_y3, h_m4_10, h_m4_20, h_m4_00, h_m4_30⟩
  let G4 := RealGivens.givens_xy c4 s4
  let M4 := G4 * M3
  have hG4 : IsRealGivens G4 := IsRealGivens.xy c4 s4 h4
  have hM4_lorentz : M4ᵀ * minkowskiMetricReal * M4 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG4) hM3_lorentz
  
  have h_m4_03 : M4 0 3 = 0 := by
    change (G4 * M3) 0 3 = 0
    rw [givens_xy_row0 c4 s4 M3 3, h_m3_03]
  rcases lorentz_zero_x_col3 M4 hM4_lorentz h_m4_00 h_m4_10 h_m4_20 h_m4_30 h_m4_03 h_y3 with ⟨c5, s5, h5, h_x3, h_m5_10, h_m5_20, h_m5_00, h_m5_30, h_m5_23, h_m5_33⟩
  let G5 := RealGivens.givens_zx c5 s5
  let M5 := G5 * M4
  have hG5 : IsRealGivens G5 := IsRealGivens.zx c5 s5 h5
  have hM5_lorentz : M5ᵀ * minkowskiMetricReal * M5 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG5) hM4_lorentz
  
  have h_m5_01 : M5 0 1 = 0 := by
    change (G5 * M4) 0 1 = 0
    rw [givens_zx_row0 c5 s5 M4 1]
    change (G4 * M3) 0 1 = 0
    rw [givens_xy_row0 c4 s4 M3 1, h_m3_01]
  rcases lorentz_zero_y_col1 M5 h_m5_00 h_m5_10 h_m5_20 h_m5_30 h_m5_01 with ⟨c6, s6, h6, h_y1, h_m6_10, h_m6_20, h_m6_00, h_m6_30, h_m6_33, h_m6_13, h_m6_23, h11_pos⟩
  let G6 := RealGivens.givens_xy c6 s6
  let M6 := G6 * M5
  have hG6 : IsRealGivens G6 := IsRealGivens.xy c6 s6 h6
  
  have h_m6_id : M6 = 1 := by
    have hM6_lorentz : M6ᵀ * minkowskiMetricReal * M6 = minkowskiMetricReal := mul_lorentz_matrix (IsRealGivens_lorentz_matrix hG6) hM5_lorentz
    have hM6_det : Matrix.det M6 = 1 := by
      have hM1_det : Matrix.det M1 = 1 := by rw [show M1 = G1 * M from rfl, Matrix.det_mul, det_xy c1 s1 h1, hM_det, mul_one]
      have hM2_det : Matrix.det M2 = 1 := by rw [show M2 = G2 * M1 from rfl, Matrix.det_mul, det_zx c2 s2 h2, hM1_det, mul_one]
      have hM3_det : Matrix.det M3 = 1 := by rw [show M3 = G3 * M2 from rfl, Matrix.det_mul, det_t_x c3 s3 h3, hM2_det, mul_one]
      have hM4_det : Matrix.det M4 = 1 := by rw [show M4 = G4 * M3 from rfl, Matrix.det_mul, det_xy c4 s4 h4, hM3_det, mul_one]
      have hM5_det : Matrix.det M5 = 1 := by rw [show M5 = G5 * M4 from rfl, Matrix.det_mul, det_zx c5 s5 h5, hM4_det, mul_one]
      rw [show M6 = G6 * M5 from rfl, Matrix.det_mul, det_xy c6 s6 h6, hM5_det, mul_one]
    have h_m5_03 : M5 0 3 = 0 := by
      change (G5 * M4) 0 3 = 0
      rw [givens_zx_row0 c5 s5 M4 3, h_m4_03]
    have h_m6_03 : M6 0 3 = 0 := by
      change (G6 * M5) 0 3 = 0
      rw [givens_xy_row0 c6 s6 M5 3, h_m5_03]
    have h_m6_33_eq : M6 3 3 = 1 := by
      have h1 : M6 3 3 = M5 3 3 := h_m6_33
      have h2 : M5 3 3 = 1 := h_m5_33
      rw [h1, h2]
    have h_m6_13_eq : M6 1 3 = 0 := by
      have h1 : M6 1 3 = c6 * M5 1 3 - s6 * M5 2 3 := h_m6_13
      have h2 : M5 1 3 = 0 := h_x3
      have h3 : M5 2 3 = 0 := h_m5_23
      rw [h1, h2, h3]
      ring
    have h_m6_23_eq : M6 2 3 = 0 := by
      have h1 : M6 2 3 = s6 * M5 1 3 + c6 * M5 2 3 := h_m6_23
      have h2 : M5 1 3 = 0 := h_x3
      have h3 : M5 2 3 = 0 := h_m5_23
      rw [h1, h2, h3]
      ring
    exact lorentz_M6_eq_one M6 hM6_lorentz hM6_det h_m6_00 h_m6_10 h_m6_20 h_m6_30 h_m6_33_eq h_m6_13_eq h_m6_23_eq h_m6_03 h_y1 h11_pos
  use G6 * (G5 * (G4 * (G3 * (G2 * G1))))
  refine ⟨?_, ?_⟩
  · exact IsRealGivens.mul hG6 (IsRealGivens.mul hG5 (IsRealGivens.mul hG4 (IsRealGivens.mul hG3 (IsRealGivens.mul hG2 hG1))))
  · calc
      (G6 * (G5 * (G4 * (G3 * (G2 * G1))))) * M = G6 * (G5 * (G4 * (G3 * (G2 * (G1 * M))))) := by
        simp [Matrix.mul_assoc]
      _ = M6 := rfl
      _ = 1 := h_m6_id

lemma real_lorentz_is_product_of_givens (R : ProperOrthochronousLorentzGroup) :
    ∃ (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : IsRealGivens G), R = real_givens_pol G hG := by
  rcases proper_lorentz_reduce_to_id R with ⟨G_prod, hG_prod, h_prod_eq⟩
  rcases IsRealGivens_inv_exists hG_prod with ⟨G_inv, hG_inv, h_inv_prod, h_prod_inv⟩
  use G_inv, hG_inv
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (R.val.val) i j = G_inv i j
  have h_eq : G_inv * (G_prod * R.val.val) = G_inv * 1 := by rw [h_prod_eq]
  rw [← Matrix.mul_assoc, h_inv_prod, Matrix.one_mul, Matrix.mul_one] at h_eq
  rw [h_eq]


lemma real_lorentz_joined_to_id (R : ProperOrthochronousLorentzGroup) :
    Joined R 1 := by
  rcases real_lorentz_is_product_of_givens R with ⟨G, hG, hR⟩
  rw [hR]
  exact real_givens_joined_to_id G hG


lemma real_to_complex_lorentz_joined_to_id (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (R : ProperOrthochronousLorentzGroup) :
    JoinedIn (orbit_domain n z) (real_to_complex_lorentz R) 1 := by
  have ⟨γ2⟩ := real_lorentz_joined_to_id R
  let γ_c := γ2.map continuous_real_to_complex_lorentz
  use γ_c.cast rfl real_to_complex_lorentz_one.symm
  intro t
  change (real_to_complex_lorentz (γ2 t)) • z ∈ forward_tube_n n
  apply real_lorentz_preserves_tube
  exact hz


lemma orbit_domain_path_connected (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    IsPathConnected (orbit_domain n z) := by
  by_cases hn : 2 ≤ n
  · use 1
    constructor
    · have h_one : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
      change (1 : SpecialSpecialComplexLorentzGroup) • z ∈ forward_tube_n n
      rw [h_one]
      exact hz
    · intro Λ hΛ
      have ⟨R, _, γ, hγ⟩ := orbit_domain_joined_to_real n hn Λ z hz hΛ
      have p1 : JoinedIn (orbit_domain n z) Λ (real_to_complex_lorentz R) := ⟨γ, hγ⟩
      have p2 := real_to_complex_lorentz_joined_to_id n z hz R
      exact JoinedIn.symm (JoinedIn.trans p1 p2)
  · have h_univ : orbit_domain n z = Set.univ := by
      ext Λ
      simp only [Set.mem_univ, iff_true]
      change Λ • z ∈ forward_tube_n n
      dsimp [forward_tube_n]
      intro i hi
      exfalso
      omega
    rw [h_univ]
    exact isPathConnected_univ

end Geometry.PolarDecomposition
