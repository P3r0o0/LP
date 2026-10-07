import Minkowski
import Givens
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic

namespace Geometry

open Complex
open Matrix






@[simp] def sigma_0 : Fin 2 → Fin 2 → ℂ
| 0, 0 => 1
| 0, 1 => 0
| 1, 0 => 0
| 1, 1 => 1


@[simp] def sigma_1 : Fin 2 → Fin 2 → ℂ
| 0, 0 => 0
| 0, 1 => 1
| 1, 0 => 1
| 1, 1 => 0


@[simp] def sigma_2 : Fin 2 → Fin 2 → ℂ
| 0, 0 => 0
| 0, 1 => -I
| 1, 0 => I
| 1, 1 => 0


@[simp] def sigma_3 : Fin 2 → Fin 2 → ℂ
| 0, 0 => 1
| 0, 1 => 0
| 1, 0 => 0
| 1, 1 => -1


@[simp] def vec_to_spinor (x : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => x 0 * sigma_0 i j + x 1 * sigma_1 i j + x 2 * sigma_2 i j + x 3 * sigma_3 i j

lemma vec_to_spinor_apply_00 (x : Fin 4 → ℂ) : vec_to_spinor x 0 0 = x 0 + x 3 := by
  dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]; ring

lemma vec_to_spinor_apply_01 (x : Fin 4 → ℂ) : vec_to_spinor x 0 1 = x 1 - x 2 * I := by
  dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]; ring

lemma vec_to_spinor_apply_10 (x : Fin 4 → ℂ) : vec_to_spinor x 1 0 = x 1 + x 2 * I := by
  dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]; ring

lemma vec_to_spinor_apply_11 (x : Fin 4 → ℂ) : vec_to_spinor x 1 1 = x 0 - x 3 := by
  dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]; ring


lemma vec_to_spinor_det (x : Fin 4 → ℂ) :
    (vec_to_spinor x).det = (x 0)^2 - (x 1)^2 - (x 2)^2 - (x 3)^2 := by
  rw [det_fin_two,
    vec_to_spinor_apply_00, vec_to_spinor_apply_01,
    vec_to_spinor_apply_10, vec_to_spinor_apply_11]
  have hI : I ^ 2 = -1 := I_sq
  calc (x 0 + x 3) * (x 0 - x 3) - (x 1 - x 2 * I) * (x 1 + x 2 * I)
      = x 0 ^ 2 - x 3 ^ 2 - (x 1 ^ 2 - x 2 ^ 2 * I ^ 2) := by ring
    _ = x 0 ^ 2 - x 3 ^ 2 - (x 1 ^ 2 - x 2 ^ 2 * (-1)) := by rw [hI]
    _ = x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by ring


lemma vec_to_spinor_det_eq_minkowski_form (x : Fin 4 → ℂ) :
    (vec_to_spinor x).det = dotProduct x (minkowskiMetric.mulVec x) := by
  rw [vec_to_spinor_det]
  simp [dotProduct, Matrix.mulVec, minkowskiMetric, Fin.sum_univ_four]
  ring






lemma spinor_action_det (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 1) (hB : B.det = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * X * Bᵀ).det = X.det := by
  rw [det_mul, det_mul, det_transpose, hA, hB]
  ring


lemma spinor_action_preserves_minkowski (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 1) (hB : B.det = 1) (x : Fin 4 → ℂ) :
    (A * vec_to_spinor x * Bᵀ).det = dotProduct x (minkowskiMetric.mulVec x) := by
  rw [spinor_action_det A B hA hB, vec_to_spinor_det_eq_minkowski_form]








noncomputable def sl2c_path_I_to_minus_I (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp (I * (Real.pi * t)), 0; 0, exp (- (I * (Real.pi * t)))]


lemma sl2c_path_I_to_minus_I_det (t : ℝ) :
  (sl2c_path_I_to_minus_I t).det = 1 := by
  dsimp [sl2c_path_I_to_minus_I]
  rw [det_fin_two]
  simp
  have h_add : I * (Real.pi * t) + -(I * (Real.pi * t)) = 0 := by ring
  rw [← Complex.exp_add, h_add, Complex.exp_zero]


lemma sl2c_path_I_to_minus_I_zero : sl2c_path_I_to_minus_I 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2c_path_I_to_minus_I]


lemma sl2c_path_I_to_minus_I_one : sl2c_path_I_to_minus_I 1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2c_path_I_to_minus_I]
  · have : I * ↑Real.pi = ↑Real.pi * I := by ring
    rw [this, Complex.exp_pi_mul_I]
  · have : -(I * ↑Real.pi) = -(↑Real.pi * I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num


lemma continuous_sl2c_path_I_to_minus_I : Continuous sl2c_path_I_to_minus_I := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [sl2c_path_I_to_minus_I]
  · apply Continuous.cexp
    continuity
  · exact continuous_const
  · exact continuous_const
  · apply Continuous.cexp
    continuity






@[simp] noncomputable def spinor_to_vec (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  fun i => match i with
  | 0 => (X 0 0 + X 1 1) / 2
  | 1 => (X 0 1 + X 1 0) / 2
  | 2 => (X 0 1 - X 1 0) * I / 2
  | 3 => (X 0 0 - X 1 1) / 2


lemma spinor_to_vec_left_inv (x : Fin 4 → ℂ) : spinor_to_vec (vec_to_spinor x) = x := by
  ext i
  fin_cases i <;> simp [spinor_to_vec,] <;> try ring
  rw [I_sq]; ring


lemma vec_to_spinor_right_inv (X : Matrix (Fin 2) (Fin 2) ℂ) : vec_to_spinor (spinor_to_vec X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3] <;> try ring
  · rw [I_sq]; ring
  · rw [I_sq]; ring


@[simp] noncomputable def spinor_action (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  spinor_to_vec (A * (vec_to_spinor x) * Bᵀ)


lemma spinor_action_mul (A₁ B₁ A₂ B₂ : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) :
  spinor_action A₁ B₁ (spinor_action A₂ B₂ x) = spinor_action (A₁ * A₂) (B₁ * B₂) x := by
  dsimp [spinor_action]
  rw [vec_to_spinor_right_inv]
  have h_transpose : (B₁ * B₂)ᵀ = B₂ᵀ * B₁ᵀ := transpose_mul B₁ B₂
  rw [h_transpose]
  simp [Matrix.mul_assoc]


lemma spinor_action_one (x : Fin 4 → ℂ) :
  spinor_action 1 1 x = x := by
  dsimp [spinor_action]
  simp [spinor_to_vec_left_inv]


lemma vec_to_spinor_add (x y : Fin 4 → ℂ) : vec_to_spinor (x + y) = vec_to_spinor x + vec_to_spinor y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.add_apply, Matrix.add_apply] <;> ring

lemma vec_to_spinor_smul (c : ℂ) (x : Fin 4 → ℂ) : vec_to_spinor (c • x) = c • vec_to_spinor x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ Pi.smul_apply, Matrix.smul_apply, smul_eq_mul] <;> ring


lemma spinor_to_vec_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : spinor_to_vec (X + Y) = spinor_to_vec X + spinor_to_vec Y := by
  ext i
  fin_cases i <;> simp [spinor_to_vec, Pi.add_apply, Matrix.add_apply] <;> ring

lemma spinor_to_vec_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : spinor_to_vec (c • X) = c • spinor_to_vec X := by
  ext i
  fin_cases i <;> simp [spinor_to_vec, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul] <;> ring


lemma spinor_action_add (A B : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 4 → ℂ) :
  spinor_action A B (x + y) = spinor_action A B x + spinor_action A B y := by
  dsimp [spinor_action]
  rw [vec_to_spinor_add]
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [spinor_to_vec_add]

lemma spinor_action_smul (A B : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (x : Fin 4 → ℂ) :
  spinor_action A B (c • x) = c • spinor_action A B x := by
  dsimp [spinor_action]
  rw [vec_to_spinor_smul]
  have h1 : A * (c • vec_to_spinor x) = c • (A * vec_to_spinor x) := Matrix.mul_smul A c (vec_to_spinor x)
  have h2 : (c • (A * vec_to_spinor x)) * Bᵀ = c • (A * vec_to_spinor x * Bᵀ) := Matrix.smul_mul c (A * vec_to_spinor x) Bᵀ
  rw [h1, h2, spinor_to_vec_smul]


lemma spinor_action_preserves_norm (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 1) (hB : B.det = 1) (x : Fin 4 → ℂ) :
    dotProduct (spinor_action A B x) (minkowskiMetric.mulVec (spinor_action A B x)) =
    dotProduct x (minkowskiMetric.mulVec x) := by
  dsimp [spinor_action]
  rw [← vec_to_spinor_det_eq_minkowski_form (spinor_to_vec (A * vec_to_spinor x * Bᵀ))]
  rw [vec_to_spinor_right_inv]
  exact spinor_action_preserves_minkowski A B hA hB x

noncomputable def spinor_action_linear (A B : Matrix (Fin 2) (Fin 2) ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun := spinor_action A B
  map_add' := spinor_action_add A B
  map_smul' := spinor_action_smul A B

noncomputable def spinorPhi_matrix (A B : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin 4)) (Pi.basisFun ℂ (Fin 4)) (spinor_action_linear A.1 B.1)

lemma spinorPhi_matrix_mulVec (A B : SpecialLinearGroup (Fin 2) ℂ) (x : Fin 4 → ℂ) :
  mulVec (spinorPhi_matrix A B) x = spinor_action A.1 B.1 x := by
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℂ (Fin 4)) (Pi.basisFun ℂ (Fin 4)) (spinor_action_linear A.1 B.1) x
  have h2 : (Pi.basisFun ℂ (Fin 4)).repr x = x := by rfl
  have h3 : (Pi.basisFun ℂ (Fin 4)).repr (spinor_action_linear A.1 B.1 x) = spinor_action_linear A.1 B.1 x := by rfl
  rw [h2, h3] at h
  exact h

lemma spinorPhi_matrix_im_zero (A B : SpecialLinearGroup (Fin 2) ℂ)
  (hB : (B.1 : Matrix (Fin 2) (Fin 2) ℂ) = (A.1 : Matrix (Fin 2) (Fin 2) ℂ).map star) (i j : Fin 4) :
  (spinorPhi_matrix A B i j).im = 0 := by
  dsimp [spinorPhi_matrix]
  dsimp [spinor_action_linear, Pi.basisFun, spinor_action, vec_to_spinor, spinor_to_vec, sigma_0, sigma_1, sigma_2, sigma_3]
  rw [hB]
  fin_cases i <;> fin_cases j
  all_goals {
    simp [Complex.add_im, Complex.add_re, Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re, Complex.neg_im, Complex.neg_re, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    ring
  }


lemma matrix_eq_of_mulVec_eq (M N : Matrix (Fin 4) (Fin 4) ℂ) (h : ∀ x, mulVec M x = mulVec N x) : M = N := by
  ext i j
  have h_basis := h (fun k => if k = j then 1 else 0)
  have hM : (mulVec M (fun k => if k = j then 1 else 0)) i = M i j := by
    simp [mulVec, dotProduct]
  have hN : (mulVec N (fun k => if k = j then 1 else 0)) i = N i j := by
    simp [mulVec, dotProduct]
  rw [← hM, ← hN]
  exact congrFun h_basis i

lemma spinorPhi_matrix_one : spinorPhi_matrix 1 1 = 1 := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).1 = 1 := rfl
  rw [h1]
  rw [spinor_action_one]
  rw [Matrix.one_mulVec]

lemma spinorPhi_matrix_mul (A₁ B₁ A₂ B₂ : SpecialLinearGroup (Fin 2) ℂ) :
  spinorPhi_matrix (A₁ * A₂) (B₁ * B₂) = spinorPhi_matrix A₁ B₁ * spinorPhi_matrix A₂ B₂ := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  have hA : (A₁ * A₂).1 = A₁.1 * A₂.1 := rfl
  have hB : (B₁ * B₂).1 = B₁.1 * B₂.1 := rfl
  rw [hA, hB]
  rw [← spinor_action_mul]
  rw [← spinorPhi_matrix_mulVec]
  rw [← spinorPhi_matrix_mulVec]
  rw [Matrix.mulVec_mulVec]

lemma spinorPhi_matrix_inv (A B : SpecialLinearGroup (Fin 2) ℂ) :
  spinorPhi_matrix A B * spinorPhi_matrix A⁻¹ B⁻¹ = 1 := by
  rw [← spinorPhi_matrix_mul]
  have hA : A * A⁻¹ = 1 := mul_inv_cancel A
  have hB : B * B⁻¹ = 1 := mul_inv_cancel B
  rw [hA, hB, spinorPhi_matrix_one]

lemma spinorPhi_matrix_inv' (A B : SpecialLinearGroup (Fin 2) ℂ) :
  spinorPhi_matrix A⁻¹ B⁻¹ * spinorPhi_matrix A B = 1 := by
  rw [← spinorPhi_matrix_mul]
  have hA : A⁻¹ * A = 1 := inv_mul_cancel A
  have hB : B⁻¹ * B = 1 := inv_mul_cancel B
  rw [hA, hB, spinorPhi_matrix_one]

lemma minkowskiMetric_symm : minkowskiMetricᵀ = minkowskiMetric := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma matrix_symm_eq_of_dotProduct_eq (M N : Matrix (Fin 4) (Fin 4) ℂ) (hM : Mᵀ = M) (hN : Nᵀ = N)
  (h : ∀ x : Fin 4 → ℂ, dotProduct x (mulVec M x) = dotProduct x (mulVec N x)) : M = N := by
  ext i j
  have hii : ∀ k : Fin 4, M k k = N k k := by
    intro k
    have hk := h (fun l => if l = k then 1 else 0)
    dsimp [dotProduct, mulVec] at hk
    repeat rw [Fin.sum_univ_four] at hk
    fin_cases k <;> { simp at hk; exact hk }
  have hij : ∀ k l : Fin 4, M k l + M l k = N k l + N l k := by
    intro k l
    have hkl := h (fun m => if m = k then 1 else if m = l then 1 else 0)
    dsimp [dotProduct, mulVec] at hkl
    repeat rw [Fin.sum_univ_four] at hkl
    fin_cases k <;> fin_cases l <;> {
      simp at hkl
      have hk1 : M 0 0 = N 0 0 := hii 0
      have hk2 : M 1 1 = N 1 1 := hii 1
      have hk3 : M 2 2 = N 2 2 := hii 2
      have hk4 : M 3 3 = N 3 3 := hii 3
      try simp at hkl ⊢
      simp only [hk1, hk2, hk3, hk4] at hkl ⊢
      try first | linear_combination hkl | ring
    }
  have hM_symm : ∀ k l : Fin 4, M k l = M l k := by
    intro k l
    have h_symm : Mᵀ l k = M l k := by rw [hM]
    exact h_symm
  have hN_symm : ∀ k l : Fin 4, N k l = N l k := by
    intro k l
    have h_symm : Nᵀ l k = N l k := by rw [hN]
    exact h_symm
  have heq : M i j + M i j = N i j + N i j := by
    calc M i j + M i j = M i j + M j i := by rw [hM_symm i j]
         _ = N i j + N j i := hij i j
         _ = N i j + N i j := by rw [hN_symm i j]
  have h2 : (2 : ℂ) * M i j = (2 : ℂ) * N i j := by
    calc (2 : ℂ) * M i j = M i j + M i j := by ring
         _ = N i j + N i j := heq
         _ = (2 : ℂ) * N i j := by ring
  have h3 : M i j = N i j := by
    calc M i j = (2 : ℂ) * M i j / 2 := by ring
         _ = (2 : ℂ) * N i j / 2 := by rw [h2]
         _ = N i j := by ring
  exact h3

lemma spinorPhi_is_lorentz (A B : SpecialLinearGroup (Fin 2) ℂ) :
  (spinorPhi_matrix A B)ᵀ * minkowskiMetric * (spinorPhi_matrix A B) = minkowskiMetric := by
  apply matrix_symm_eq_of_dotProduct_eq
  · rw [transpose_mul, transpose_mul, transpose_transpose, minkowskiMetric_symm]
    rw [← Matrix.mul_assoc]
  · exact minkowskiMetric_symm
  · intro x
    have h1 : mulVec ((spinorPhi_matrix A B)ᵀ * minkowskiMetric * (spinorPhi_matrix A B)) x =
              mulVec (spinorPhi_matrix A B)ᵀ (minkowskiMetric.mulVec (mulVec (spinorPhi_matrix A B) x)) := by
      rw [mulVec_mulVec, mulVec_mulVec]
    rw [h1]
    rw [dotProduct_mulVec]
    have h2 : vecMul x (spinorPhi_matrix A B)ᵀ = mulVec (spinorPhi_matrix A B) x := by
      ext i
      dsimp [vecMul, mulVec]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    rw [h2]
    have h3 : mulVec (spinorPhi_matrix A B) x = spinor_action A.1 B.1 x := spinorPhi_matrix_mulVec A B x
    rw [h3]
    exact spinor_action_preserves_norm A.1 B.1 A.2 B.2 x


lemma sl2c_lower_det_l (z : ℂ) : (!![1, (0:ℂ); z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by simp [det_fin_two]
lemma sl2c_upper_det_u (z : ℂ) : (!![1, z; (0:ℂ), 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by simp [det_fin_two]

inductive IsUpperOrLower : SpecialLinearGroup (Fin 2) ℂ → Prop
| upper (z : ℂ) : IsUpperOrLower ⟨!![1, z; 0, 1], sl2c_upper_det_u z⟩
| lower (z : ℂ) : IsUpperOrLower ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩
| one : IsUpperOrLower 1
| mul {A B} (hA : IsUpperOrLower A) (hB : IsUpperOrLower B) : IsUpperOrLower (A * B)
| inv {A} (hA : IsUpperOrLower A) : IsUpperOrLower A⁻¹

lemma sl2c_generated_by_upper_lower (A : SpecialLinearGroup (Fin 2) ℂ) : IsUpperOrLower A := by
  set a := (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have hdet : a * d - b * c = 1 := by
    have h := A.property; simp only [Matrix.det_fin_two] at h; exact h
  by_cases hc : c = 0
  · have ha : a ≠ 0 := by
      intro ha_eq
      simp only [hc, mul_zero, ha_eq, zero_mul, sub_zero] at hdet
      exact zero_ne_one hdet
    have had : a * d = 1 := by
      have hbc : b * c = 0 := by simp [hc]
      linear_combination hdet + hbc
    let L1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); 1, 1], sl2c_lower_det_l 1⟩
    let U1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (a-1)/a; (0:ℂ), 1], sl2c_upper_det_u _⟩
    let La : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); a, 1], sl2c_lower_det_l a⟩
    let U2 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (b+d-1)/a; (0:ℂ), 1], sl2c_upper_det_u _⟩
    have hA00 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a := rfl
    have hA01 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b := rfl
    have hA10 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c := rfl
    have hA11 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d := rfl
    have key : L1 * A = U1 * La * U2 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp [L1, U1, La, U2] <;> simp only [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Matrix.cons_val', Matrix.of_apply, hA00, hA01, hA10, hA11]
      · simp only [hc, mul_zero, add_zero, zero_add, mul_one, one_mul]
        have h1 : ((a - 1) / a) * a = a - 1 := div_mul_cancel₀ _ ha
        rw [h1]
        try ring
      · simp only [mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
        have h1 : ((a - 1) / a) * a = a - 1 := div_mul_cancel₀ _ ha
        have h2 : ((b + d - 1) / a) * a = b + d - 1 := div_mul_cancel₀ _ ha
        rw [h1]
        apply mul_right_cancel₀ ha
        rw [add_mul, mul_assoc, h2, h1]
        linear_combination -had
      · simp only [hc, mul_zero, add_zero, zero_add, mul_one, one_mul]
      · simp only [mul_zero, zero_add, mul_one, one_mul]
        have h2 : a * ((b + d - 1) / a) = b + d - 1 := by rw [mul_comm, div_mul_cancel₀ _ ha]
        rw [h2]
        try ring
    have hA_invL1 : A = L1⁻¹ * (U1 * La * U2) := by rw [←key, inv_mul_cancel_left]
    rw [hA_invL1]
    exact IsUpperOrLower.mul (IsUpperOrLower.inv (IsUpperOrLower.lower 1)) (IsUpperOrLower.mul (IsUpperOrLower.mul (IsUpperOrLower.upper _) (IsUpperOrLower.lower a)) (IsUpperOrLower.upper _))
  · let U1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (a-1)/c; (0:ℂ), 1], sl2c_upper_det_u _⟩
    let Lc : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); c, 1], sl2c_lower_det_l c⟩
    let U2 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (d-1)/c; (0:ℂ), 1], sl2c_upper_det_u _⟩
    have hA00 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a := rfl
    have hA01 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b := rfl
    have hA10 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c := rfl
    have hA11 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d := rfl
    have decomp_group : A = U1 * Lc * U2 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp [U1, Lc, U2] <;> simp only [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Matrix.cons_val', Matrix.of_apply, hA00, hA01, hA10, hA11]
      · simp only [mul_zero, add_zero, zero_add, mul_one]
        have h1 : ((a - 1) / c) * c = a - 1 := div_mul_cancel₀ _ hc
        rw [h1]
        try ring
      · simp only [mul_zero, zero_add, mul_one]
        have h1 : ((a - 1) / c) * c = a - 1 := div_mul_cancel₀ _ hc
        have h2 : ((d - 1) / c) * c = d - 1 := div_mul_cancel₀ _ hc
        rw [h1]
        apply mul_right_cancel₀ hc
        rw [add_mul, mul_assoc, h2, h1]
        linear_combination -hdet
      · simp only [mul_zero, add_zero, zero_add, mul_one, one_mul]
      · simp only [mul_zero, zero_add, mul_one, one_mul]
        have h2 : c * ((d - 1) / c) = d - 1 := by rw [mul_comm, div_mul_cancel₀ _ hc]
        rw [h2]
        try ring
    rw [decomp_group]
    exact IsUpperOrLower.mul (IsUpperOrLower.mul (IsUpperOrLower.upper _) (IsUpperOrLower.lower c)) (IsUpperOrLower.upper _)

lemma spinorPhi_matrix_U_det (z : ℂ) (B : SpecialLinearGroup (Fin 2) ℂ) :
  (spinorPhi_matrix ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ B).det = (spinorPhi_matrix 1 B).det := by
  have H : spinorPhi_matrix ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ 1 = !![
    1, z/2, I * z/2, 0;
    z/2, 1, 0, -z/2;
    I * z/2, 0, 1, -I * z/2;
    0, z/2, I * z/2, 1
  ] := by
    apply matrix_eq_of_mulVec_eq
    intro x
    rw [spinorPhi_matrix_mulVec]
    ext i
    have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).1 = 1 := rfl
    have hU : (⟨!![1, z; 0, 1], sl2c_upper_det_u z⟩ : SpecialLinearGroup (Fin 2) ℂ).1 = !![1, z; 0, 1] := rfl
    dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
    fin_cases i <;> { simp [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two]; try ring_nf; try simp only [Complex.I_sq, mul_neg_one, neg_neg]; try simp [I_sq]; ring }
  have H_det : (spinorPhi_matrix ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ 1).det = 1 := by
    rw [H, Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four]
    have H00 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, -z/2; I * z/2, 0, 1, -I * z/2; 0, z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 0) = !![(1:ℂ), 0, -z/2; 0, 1, -I * z/2; z/2, I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H01 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, -z/2; I * z/2, 0, 1, -I * z/2; 0, z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 1) = !![(z/2:ℂ), 0, -z/2; I * z/2, 1, -I * z/2; 0, I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H02 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, -z/2; I * z/2, 0, 1, -I * z/2; 0, z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 2) = !![(z/2:ℂ), 1, -z/2; I * z/2, 0, -I * z/2; 0, z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H03 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, -z/2; I * z/2, 0, 1, -I * z/2; 0, z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 3) = !![(z/2:ℂ), 1, 0; I * z/2, 0, 1; 0, z/2, I * z/2] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [H00, H01, H02, H03]
    simp [Matrix.det_fin_three]
    ring
  have H_mul := spinorPhi_matrix_mul ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ 1 1 B
  simp at H_mul
  have H_det_all : (spinorPhi_matrix ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ B).det = (spinorPhi_matrix ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det_u z⟩ 1).det * (spinorPhi_matrix 1 B).det := by
    rw [← det_mul, H_mul]
  rw [H_det, one_mul] at H_det_all
  exact H_det_all

lemma spinorPhi_matrix_L_det (z : ℂ) (B : SpecialLinearGroup (Fin 2) ℂ) :
  (spinorPhi_matrix ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ B).det = (spinorPhi_matrix 1 B).det := by
  have H : spinorPhi_matrix ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ 1 = !![
    1, z/2, -I * z/2, 0;
    z/2, 1, 0, z/2;
    -I * z/2, 0, 1, -I * z/2;
    0, -z/2, I * z/2, 1
  ] := by
    apply matrix_eq_of_mulVec_eq
    intro x
    rw [spinorPhi_matrix_mulVec]
    ext i
    have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).1 = 1 := rfl
    have hU : (⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ : SpecialLinearGroup (Fin 2) ℂ).1 = !![1, 0; z, 1] := rfl
    dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
    fin_cases i <;> { simp [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two]; try ring_nf; try simp only [Complex.I_sq, mul_neg_one, neg_neg]; try simp [I_sq]; ring }
  have H_det : (spinorPhi_matrix ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ 1).det = 1 := by
    rw [H, Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four]
    have H00 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, z/2; -I * z/2, 0, 1, -I * z/2; 0, -z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 0) = !![(1:ℂ), 0, z/2; 0, 1, -I * z/2; -z/2, I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H01 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, z/2; -I * z/2, 0, 1, -I * z/2; 0, -z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 1) = !![(z/2:ℂ), 0, z/2; -I * z/2, 1, -I * z/2; 0, I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H02 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, z/2; -I * z/2, 0, 1, -I * z/2; 0, -z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 2) = !![(z/2:ℂ), 1, z/2; -I * z/2, 0, -I * z/2; 0, -z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H03 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, z/2; -I * z/2, 0, 1, -I * z/2; 0, -z/2, I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 3) = !![(z/2:ℂ), 1, 0; -I * z/2, 0, 1; 0, -z/2, I * z/2] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [H00, H01, H02, H03]
    simp [Matrix.det_fin_three]
    ring
  have H_mul := spinorPhi_matrix_mul ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ 1 1 B
  simp at H_mul
  have H_det_all : (spinorPhi_matrix ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ B).det = (spinorPhi_matrix ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ 1).det * (spinorPhi_matrix 1 B).det := by
    rw [← det_mul, H_mul]
  rw [H_det, one_mul] at H_det_all
  exact H_det_all

lemma spinorPhi_matrix_det_A (A B : SpecialLinearGroup (Fin 2) ℂ) (hA : IsUpperOrLower A) :
  (spinorPhi_matrix A B).det = (spinorPhi_matrix 1 B).det := by
  induction hA generalizing B with
  | upper z => exact spinorPhi_matrix_U_det z B
  | lower z => exact spinorPhi_matrix_L_det z B
  | one => simp
  | @mul A1 A2 hA1 hA2 ihA1 ihA2 =>
    have H_mul := spinorPhi_matrix_mul A1 1 A2 B
    simp at H_mul
    rw [H_mul, Matrix.det_mul, ihA1 1, ihA2 B]
    have H_one := spinorPhi_matrix_one
    rw [H_one, Matrix.det_one, one_mul]
  | @inv A1 hA1 ihA1 =>
    have H_inv' := spinorPhi_matrix_inv' A1 1
    simp at H_inv'
    have H_inv_det : (spinorPhi_matrix A1⁻¹ 1).det * (spinorPhi_matrix A1 1).det = 1 := by
      rw [←Matrix.det_mul, H_inv', Matrix.det_one]
    have H_A1_1 : (spinorPhi_matrix A1 1).det = 1 := by
      have H_ihA1_1 := ihA1 1
      rw [spinorPhi_matrix_one, Matrix.det_one] at H_ihA1_1
      exact H_ihA1_1
    rw [H_A1_1, mul_one] at H_inv_det
    have H_mul := spinorPhi_matrix_mul A1⁻¹ 1 1 B
    simp at H_mul
    rw [H_mul, Matrix.det_mul, H_inv_det, one_mul]

lemma spinorPhi_matrix_det_B (B : SpecialLinearGroup (Fin 2) ℂ) (hB : IsUpperOrLower B) :
  (spinorPhi_matrix 1 B).det = 1 := by
  induction hB with
  | upper z =>
    have H : spinorPhi_matrix 1 ⟨!![1, z; 0, 1], sl2c_upper_det_u z⟩ = !![
      1, z/2, -I * z/2, 0;
      z/2, 1, 0, -z/2;
      -I * z/2, 0, 1, I * z/2;
      0, z/2, -I * z/2, 1
    ] := by
      apply matrix_eq_of_mulVec_eq
      intro x
      rw [spinorPhi_matrix_mulVec]
      ext i
      have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).1 = 1 := rfl
      have hU : (⟨!![1, z; 0, 1], sl2c_upper_det_u z⟩ : SpecialLinearGroup (Fin 2) ℂ).1 = !![1, z; 0, 1] := rfl
      dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
      fin_cases i <;> { simp [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two]; try ring_nf; try simp only [Complex.I_sq, mul_neg_one, neg_neg]; try simp [I_sq]; ring }
    rw [H, Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four]
    have H00 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, -z/2; -I * z/2, 0, 1, I * z/2; 0, z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 0) = !![(1:ℂ), 0, -z/2; 0, 1, I * z/2; z/2, -I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H01 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, -z/2; -I * z/2, 0, 1, I * z/2; 0, z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 1) = !![(z/2:ℂ), 0, -z/2; -I * z/2, 1, I * z/2; 0, -I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H02 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, -z/2; -I * z/2, 0, 1, I * z/2; 0, z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 2) = !![(z/2:ℂ), 1, -z/2; -I * z/2, 0, I * z/2; 0, z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H03 : (!![1, z/2, -I * z/2, 0; z/2, 1, 0, -z/2; -I * z/2, 0, 1, I * z/2; 0, z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 3) = !![(z/2:ℂ), 1, 0; -I * z/2, 0, 1; 0, z/2, -I * z/2] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [H00, H01, H02, H03]
    simp [Matrix.det_fin_three]
    ring
  | lower z =>
    have H : spinorPhi_matrix 1 ⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ = !![
      1, z/2, I * z/2, 0;
      z/2, 1, 0, z/2;
      I * z/2, 0, 1, I * z/2;
      0, -z/2, -I * z/2, 1
    ] := by
      apply matrix_eq_of_mulVec_eq
      intro x
      rw [spinorPhi_matrix_mulVec]
      ext i
      have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).1 = 1 := rfl
      have hU : (⟨!![1, 0; z, 1], sl2c_lower_det_l z⟩ : SpecialLinearGroup (Fin 2) ℂ).1 = !![1, 0; z, 1] := rfl
      dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
      fin_cases i <;> { simp [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two]; try ring_nf; try simp only [Complex.I_sq, mul_neg_one, sub_neg_eq_add]; try simp [I_sq]; ring }
    rw [H, Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four]
    have H00 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, z/2; I * z/2, 0, 1, I * z/2; 0, -z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 0) = !![(1:ℂ), 0, z/2; 0, 1, I * z/2; -z/2, -I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H01 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, z/2; I * z/2, 0, 1, I * z/2; 0, -z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 1) = !![(z/2:ℂ), 0, z/2; I * z/2, 1, I * z/2; 0, -I * z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H02 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, z/2; I * z/2, 0, 1, I * z/2; 0, -z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 2) = !![(z/2:ℂ), 1, z/2; I * z/2, 0, I * z/2; 0, -z/2, 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    have H03 : (!![1, z/2, I * z/2, 0; z/2, 1, 0, z/2; I * z/2, 0, 1, I * z/2; 0, -z/2, -I * z/2, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.succ (Fin.succAbove 3) = !![(z/2:ℂ), 1, 0; I * z/2, 0, 1; 0, -z/2, -I * z/2] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [H00, H01, H02, H03]
    simp [Matrix.det_fin_three]
    ring
  | one => rw [spinorPhi_matrix_one, det_one]
  | @mul B1 B2 hB1 hB2 ihB1 ihB2 =>
    have H_mul := spinorPhi_matrix_mul 1 B1 1 B2
    simp at H_mul
    rw [H_mul, Matrix.det_mul, ihB1, ihB2, mul_one]
  | @inv B1 hB1 ihB1 =>
    have H_inv' := spinorPhi_matrix_inv' 1 B1
    simp at H_inv'
    have H_inv_det : (spinorPhi_matrix 1 B1⁻¹).det * (spinorPhi_matrix 1 B1).det = 1 := by
      rw [←Matrix.det_mul, H_inv', Matrix.det_one]
    rw [ihB1, mul_one] at H_inv_det
    exact H_inv_det

lemma spinorPhi_matrix_det (A B : SpecialLinearGroup (Fin 2) ℂ) :
  (spinorPhi_matrix A B).det = 1 := by
  rw [spinorPhi_matrix_det_A A B (sl2c_generated_by_upper_lower A)]
  exact spinorPhi_matrix_det_B B (sl2c_generated_by_upper_lower B)



noncomputable def spinorPhi : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ →* SpecialSpecialComplexLorentzGroup where
  toFun p :=
    let A := p.1
    let B := p.2
    let M : Matrix.GeneralLinearGroup (Fin 4) ℂ :=
      { val := spinorPhi_matrix A B,
        inv := spinorPhi_matrix A⁻¹ B⁻¹,
        val_inv := spinorPhi_matrix_inv A B,
        inv_val := spinorPhi_matrix_inv' A B }
    ⟨M, spinorPhi_is_lorentz A B, spinorPhi_matrix_det A B⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact spinorPhi_matrix_one
  map_mul' p q := by
    apply Subtype.ext
    apply Units.ext
    exact spinorPhi_matrix_mul p.1 p.2 q.1 q.2


lemma givens_xy_surj (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_xy c s := by
  have ⟨w, hw⟩ := complex_exists_sq (c - I * s)
  let v := w * (c + I * s)
  have h_wv : w * v = 1 := by
    dsimp [v]
    calc w * (w * (c + I * s)) = w^2 * (c + I * s) := by ring
      _ = (c - I * s) * (c + I * s) := by rw [hw]
      _ = c^2 - I^2 * s^2 := by ring
      _ = c^2 + s^2 := by rw [I_sq]; ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![w, 0; 0, v]
  have hA_det : A_mat.det = 1 := by dsimp [A_mat]; rw [det_fin_two]; simp [h_wv]
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  let B_mat : Matrix (Fin 2) (Fin 2) ℂ := !![v, 0; 0, w]
  have hB_det : B_mat.det = 1 := by
    dsimp [B_mat]
    rw [det_fin_two]
    have h_vw : v * w = 1 := by rw [mul_comm, h_wv]
    calc v * w - 0 * 0 = v * w := by ring
      _ = 1 := h_vw
  let B : SpecialLinearGroup (Fin 2) ℂ := ⟨B_mat, hB_det⟩
  use A, B
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![w, 0; 0, v] := rfl
  have hB_val : B.1 = !![v, 0; 0, w] := rfl
  have hc : c = (w^2 + v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc c = (c - I * s + (c + I * s))/2 := by ring
      _ = (w^2 + v^2)/2 := by rw [←hw, ←hv]
  have hs : s = I*(w^2 - v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc s = -I^2 * s := by rw [I_sq]; ring
      _ = I*(c - I * s - (c + I * s))/2 := by ring
      _ = I*(w^2 - v^2)/2 := by rw [←hw, ←hv]
  have h_vw : v * w = 1 := by rw [mul_comm, h_wv]
  have hwv_1 : ∀ a : ℂ, w * v * a = a := fun a => by rw [h_wv, one_mul]
  have hvw_1 : ∀ a : ℂ, v * w * a = a := fun a => by rw [h_vw, one_mul]
  have hwv_2 : ∀ a : ℂ, w * a * v = a := fun a => by rw [mul_right_comm, h_wv, one_mul]
  have hvw_2 : ∀ a : ℂ, v * a * w = a := fun a => by rw [mul_right_comm, h_vw, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, hB_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_xy]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one]; try simp
    try ring_nf
    try simp only [hwv_2]
    try ring
  }

lemma givens_yz_surj (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_yz c s := by
  have ⟨w, hw⟩ := complex_exists_sq (c - I * s)
  let v := w * (c + I * s)
  have h_wv : w * v = 1 := by
    dsimp [v]
    calc w * (w * (c + I * s)) = w^2 * (c + I * s) := by ring
      _ = (c - I * s) * (c + I * s) := by rw [hw]
      _ = c^2 - I^2 * s^2 := by ring
      _ = c^2 + s^2 := by rw [I_sq]; ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(w+v)/2, (w-v)/2; (w-v)/2, (w+v)/2]
  have hA_det : A_mat.det = 1 := by
    dsimp [A_mat]
    rw [det_fin_two]
    have hwv : w * v = 1 := h_wv
    calc ((w+v)/2)*((w+v)/2) - ((w-v)/2)*((w-v)/2) = w * v := by ring
      _ = 1 := hwv
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  let B_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(w+v)/2, -(w-v)/2; -(w-v)/2, (w+v)/2]
  have hB_det : B_mat.det = 1 := by
    dsimp [B_mat]
    rw [det_fin_two]
    have hwv : w * v = 1 := h_wv
    calc ((w+v)/2)*((w+v)/2) - (-(w-v)/2)*(-(w-v)/2) = w * v := by ring
      _ = 1 := hwv
  let B : SpecialLinearGroup (Fin 2) ℂ := ⟨B_mat, hB_det⟩
  use A, B
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![(w+v)/2, (w-v)/2; (w-v)/2, (w+v)/2] := rfl
  have hB_val : B.1 = !![(w+v)/2, -(w-v)/2; -(w-v)/2, (w+v)/2] := rfl
  have hc : c = (w^2 + v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc c = (c - I * s + (c + I * s))/2 := by ring
      _ = (w^2 + v^2)/2 := by rw [←hw, ←hv]
  have hs : s = I*(w^2 - v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc s = -I^2 * s := by rw [I_sq]; ring
      _ = I*(c - I * s - (c + I * s))/2 := by ring
      _ = I*(w^2 - v^2)/2 := by rw [←hw, ←hv]
  have h_vw : v * w = 1 := by rw [mul_comm, h_wv]
  have hwv_1 : ∀ a : ℂ, w * v * a = a := fun a => by rw [h_wv, one_mul]
  have hvw_1 : ∀ a : ℂ, v * w * a = a := fun a => by rw [h_vw, one_mul]
  have hwv_2 : ∀ a : ℂ, w * a * v = a := fun a => by rw [mul_right_comm, h_wv, one_mul]
  have hvw_2 : ∀ a : ℂ, v * a * w = a := fun a => by rw [mul_right_comm, h_vw, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, hB_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_yz]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one]; try simp
    try ring_nf
    try simp only [hwv_1]
    try ring
  }

lemma givens_zx_surj (c s : ℂ) (h : c ^ 2 + s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_zx c s := by
  have ⟨w, hw⟩ := complex_exists_sq (c - I * s)
  let v := w * (c + I * s)
  have h_wv : w * v = 1 := by
    dsimp [v]
    calc w * (w * (c + I * s)) = w^2 * (c + I * s) := by ring
      _ = (c - I * s) * (c + I * s) := by rw [hw]
      _ = c^2 - I^2 * s^2 := by ring
      _ = c^2 + s^2 := by rw [I_sq]; ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(w+v)/2, -I*(w-v)/2; I*(w-v)/2, (w+v)/2]
  have hA_det : A_mat.det = 1 := by
    dsimp [A_mat]
    rw [det_fin_two]
    have hwv : w * v = 1 := h_wv
    calc ((w+v)/2)*((w+v)/2) - (-I*(w-v)/2)*(I*(w-v)/2) = (w^2+v^2+2*w*v)/4 - (-I^2)*(w^2+v^2-2*w*v)/4 := by ring
      _ = (w^2+v^2+2*w*v)/4 - (-(-1))*(w^2+v^2-2*w*v)/4 := by rw [I_sq]
      _ = w * v := by ring
      _ = 1 := hwv
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  let B_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(w+v)/2, -I*(w-v)/2; I*(w-v)/2, (w+v)/2]
  have hB_det : B_mat.det = 1 := by
    dsimp [B_mat]
    rw [det_fin_two]
    have hwv : w * v = 1 := h_wv
    calc ((w+v)/2)*((w+v)/2) - (-I*(w-v)/2)*(I*(w-v)/2) = (w^2+v^2+2*w*v)/4 - (-I^2)*(w^2+v^2-2*w*v)/4 := by ring
      _ = (w^2+v^2+2*w*v)/4 - (-(-1))*(w^2+v^2-2*w*v)/4 := by rw [I_sq]
      _ = w * v := by ring
      _ = 1 := hwv
  let B : SpecialLinearGroup (Fin 2) ℂ := ⟨B_mat, hB_det⟩
  use A, B
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![(w+v)/2, -I*(w-v)/2; I*(w-v)/2, (w+v)/2] := rfl
  have hB_val : B.1 = !![(w+v)/2, -I*(w-v)/2; I*(w-v)/2, (w+v)/2] := rfl
  have hc : c = (w^2 + v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc c = (c - I * s + (c + I * s))/2 := by ring
      _ = (w^2 + v^2)/2 := by rw [←hw, ←hv]
  have hs : s = I*(w^2 - v^2)/2 := by
    have hv : v^2 = c + I * s := by
      calc v^2 = w^2 * (c + I * s)^2 := by dsimp [v]; ring
        _ = (c - I * s) * (c + I * s)^2 := by rw [hw]
        _ = (c^2 - I^2 * s^2) * (c + I * s) := by ring
        _ = (c^2 + s^2) * (c + I * s) := by rw [I_sq]; ring
        _ = 1 * (c + I * s) := by rw [h]
        _ = c + I * s := by ring
    calc s = -I^2 * s := by rw [I_sq]; ring
      _ = I*(c - I * s - (c + I * s))/2 := by ring
      _ = I*(w^2 - v^2)/2 := by rw [←hw, ←hv]
  have h_vw : v * w = 1 := by rw [mul_comm, h_wv]
  have hwv_1 : ∀ a : ℂ, w * v * a = a := fun a => by rw [h_wv, one_mul]
  have hvw_1 : ∀ a : ℂ, v * w * a = a := fun a => by rw [h_vw, one_mul]
  have hwv_2 : ∀ a : ℂ, w * a * v = a := fun a => by rw [mul_right_comm, h_wv, one_mul]
  have hvw_2 : ∀ a : ℂ, v * a * w = a := fun a => by rw [mul_right_comm, h_vw, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, hB_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_zx]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one]; try simp
    try ring_nf
    try simp only [hwv_1]
    try ring
  }

lemma givens_t_x_surj (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_t_x c s := by
  have ⟨z, hz⟩ := complex_exists_sq (c + s)
  let y := z * (c - s)
  have h_zy : z * y = 1 := by
    dsimp [y]
    calc z * (z * (c - s)) = z^2 * (c - s) := by ring
      _ = (c + s) * (c - s) := by rw [hz]
      _ = c^2 - s^2 := by ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(z+y)/2, -(z-y)/2; -(z-y)/2, (z+y)/2]
  have hA_det : A_mat.det = 1 := by
    dsimp [A_mat]
    rw [det_fin_two]
    have hzy : z * y = 1 := h_zy
    calc ((z+y)/2)*((z+y)/2) - (-(z-y)/2)*(-(z-y)/2) = (z^2+y^2+2*z*y)/4 - (z^2+y^2-2*z*y)/4 := by ring
      _ = z * y := by ring
      _ = 1 := hzy
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  use A, A
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![(z+y)/2, -(z-y)/2; -(z-y)/2, (z+y)/2] := rfl
  have hc : c = (z^2 + y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc c = (c + s + (c - s))/2 := by ring
      _ = (z^2 + y^2)/2 := by rw [←hz, ←hy]
  have hs : s = (z^2 - y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc s = (c + s - (c - s))/2 := by ring
      _ = (z^2 - y^2)/2 := by rw [←hz, ←hy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have hzy_1 : ∀ a : ℂ, z * y * a = a := fun a => by rw [h_zy, one_mul]
  have hyz_1 : ∀ a : ℂ, y * z * a = a := fun a => by rw [h_yz, one_mul]
  have hzy_2 : ∀ a : ℂ, z * a * y = a := fun a => by rw [mul_right_comm, h_zy, one_mul]
  have hyz_2 : ∀ a : ℂ, y * a * z = a := fun a => by rw [mul_right_comm, h_yz, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_t_x]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one, neg_neg]; try simp [I_sq]
    try ring_nf
    try simp only [hzy_1]
    try ring
  }

lemma givens_t_y_surj (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_t_y c s := by
  have ⟨z, hz⟩ := complex_exists_sq (c + s)
  let y := z * (c - s)
  have h_zy : z * y = 1 := by
    dsimp [y]
    calc z * (z * (c - s)) = z^2 * (c - s) := by ring
      _ = (c + s) * (c - s) := by rw [hz]
      _ = c^2 - s^2 := by ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(z+y)/2, I*(z-y)/2; -I*(z-y)/2, (z+y)/2]
  have hA_det : A_mat.det = 1 := by
    dsimp [A_mat]
    rw [det_fin_two]
    have hzy : z * y = 1 := h_zy
    calc ((z+y)/2)*((z+y)/2) - (I*(z-y)/2)*(-I*(z-y)/2) = (z^2+y^2+2*z*y)/4 - (-I^2)*(z^2+y^2-2*z*y)/4 := by ring
      _ = z * y := by rw [I_sq]; ring
      _ = 1 := hzy
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  let B_mat : Matrix (Fin 2) (Fin 2) ℂ := !![(z+y)/2, -I*(z-y)/2; I*(z-y)/2, (z+y)/2]
  have hB_det : B_mat.det = 1 := by
    dsimp [B_mat]
    rw [det_fin_two]
    have hzy : z * y = 1 := h_zy
    calc ((z+y)/2)*((z+y)/2) - (-I*(z-y)/2)*(I*(z-y)/2) = (z^2+y^2+2*z*y)/4 - (-I^2)*(z^2+y^2-2*z*y)/4 := by ring
      _ = z * y := by rw [I_sq]; ring
      _ = 1 := hzy
  let B : SpecialLinearGroup (Fin 2) ℂ := ⟨B_mat, hB_det⟩
  use A, B
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![(z+y)/2, I*(z-y)/2; -I*(z-y)/2, (z+y)/2] := rfl
  have hB_val : B.1 = !![(z+y)/2, -I*(z-y)/2; I*(z-y)/2, (z+y)/2] := rfl
  have hc : c = (z^2 + y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc c = (c + s + (c - s))/2 := by ring
      _ = (z^2 + y^2)/2 := by rw [←hz, ←hy]
  have hs : s = (z^2 - y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc s = (c + s - (c - s))/2 := by ring
      _ = (z^2 - y^2)/2 := by rw [←hz, ←hy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have hzy_1 : ∀ a : ℂ, z * y * a = a := fun a => by rw [h_zy, one_mul]
  have hyz_1 : ∀ a : ℂ, y * z * a = a := fun a => by rw [h_yz, one_mul]
  have hzy_2 : ∀ a : ℂ, z * a * y = a := fun a => by rw [mul_right_comm, h_zy, one_mul]
  have hyz_2 : ∀ a : ℂ, y * a * z = a := fun a => by rw [mul_right_comm, h_yz, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, hB_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_t_y]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one]; try simp
    try ring_nf
    try simp only [hzy_1]
    try ring
  }

lemma givens_t_z_surj (c s : ℂ) (h : c ^ 2 - s ^ 2 = 1) :
  ∃ A B, spinorPhi_matrix A B = givens_t_z c s := by
  have ⟨z, hz⟩ := complex_exists_sq (c + s)
  let y := z * (c - s)
  have h_zy : z * y = 1 := by
    dsimp [y]
    calc z * (z * (c - s)) = z^2 * (c - s) := by ring
      _ = (c + s) * (c - s) := by rw [hz]
      _ = c^2 - s^2 := by ring
      _ = 1 := h
  let A_mat : Matrix (Fin 2) (Fin 2) ℂ := !![y, 0; 0, z]
  have hA_det : A_mat.det = 1 := by
    dsimp [A_mat]
    rw [det_fin_two]
    calc y * z - 0 * 0 = z * y := by ring
      _ = 1 := h_zy
  let A : SpecialLinearGroup (Fin 2) ℂ := ⟨A_mat, hA_det⟩
  use A, A
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  ext i
  have hA_val : A.1 = !![y, 0; 0, z] := rfl
  have hc : c = (z^2 + y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc c = (c + s + (c - s))/2 := by ring
      _ = (z^2 + y^2)/2 := by rw [←hz, ←hy]
  have hs : s = (z^2 - y^2)/2 := by
    have hy : y^2 = c - s := by
      calc y^2 = z^2 * (c - s)^2 := by dsimp [y]; ring
        _ = (c + s) * (c - s)^2 := by rw [hz]
        _ = (c^2 - s^2) * (c - s) := by ring
        _ = 1 * (c - s) := by rw [h]
        _ = c - s := by ring
    calc s = (c + s - (c - s))/2 := by ring
      _ = (z^2 - y^2)/2 := by rw [←hz, ←hy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have h_yz : y * z = 1 := by rw [mul_comm, h_zy]
  have hzy_1 : ∀ a : ℂ, z * y * a = a := fun a => by rw [h_zy, one_mul]
  have hyz_1 : ∀ a : ℂ, y * z * a = a := fun a => by rw [h_yz, one_mul]
  have hzy_2 : ∀ a : ℂ, z * a * y = a := fun a => by rw [mul_right_comm, h_zy, one_mul]
  have hyz_2 : ∀ a : ℂ, y * a * z = a := fun a => by rw [mul_right_comm, h_yz, one_mul]
  dsimp [spinor_action, spinor_to_vec, vec_to_spinor, Matrix.mul_apply]
  fin_cases i <;> {
    simp [hc, hs, hA_val, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four, givens_t_z]
    try ring_nf
    try simp only [Complex.I_sq, mul_neg_one]; try simp
    try ring_nf
    try simp only [hyz_2]
    try ring
  }




lemma spinorPhi_surjective : Function.Surjective spinorPhi := by
  intro M
  have hDet : (M.1.1).det = 1 := M.2.2
  have hM : (M.1.1)ᵀ * minkowskiMetric * (M.1.1) = minkowskiMetric := M.2.1
  have hGivensEx := so4c_generated_by_givens M.1.1 hM hDet
  rcases hGivensEx with ⟨G, hGivens, hEqG⟩
  have hEqM : ∃ a, (spinorPhi a).1.1 = G := by
    clear hEqG
    induction hGivens with
    | xy c s h =>
      rcases givens_xy_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | yz c s h =>
      rcases givens_yz_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | zx c s h =>
      rcases givens_zx_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | tx c s h =>
      rcases givens_t_x_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | ty c s h =>
      rcases givens_t_y_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | tz c s h =>
      rcases givens_t_z_surj c s h with ⟨A, B, hEq⟩; use (A, B); exact hEq
    | one =>
      use (1, 1); exact spinorPhi_matrix_one
    | mul hA hB ihA ihB =>
      rcases ihA with ⟨pA, hpA⟩
      rcases ihB with ⟨pB, hpB⟩
      use pA * pB
      have h_mul := MonoidHom.map_mul spinorPhi pA pB
      have h_mul2 : (spinorPhi (pA * pB)).1.1 = (spinorPhi pA).1.1 * (spinorPhi pB).1.1 := by
        rw [h_mul]; rfl
      rw [h_mul2, hpA, hpB]
  rw [←hEqG] at hEqM
  rcases hEqM with ⟨a, ha⟩
  use a
  apply Subtype.ext
  apply Units.ext
  exact ha

lemma spinorPhi_matrix_apply (A B : SpecialLinearGroup (Fin 2) ℂ) (i j : Fin 4) :
    spinorPhi_matrix A B i j = spinor_action A.1 B.1 (fun k => if k = j then 1 else 0) i := by
  have h := spinorPhi_matrix_mulVec A B (fun k => if k = j then 1 else 0)
  have h2 : mulVec (spinorPhi_matrix A B) (fun k => if k = j then 1 else 0) i = spinorPhi_matrix A B i j := by
    rw [mulVec, dotProduct, Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; simp at h
  rw [←h2, h]

@[continuity]
lemma continuous_matrix_elem_fst (i j : Fin 2) :
  Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.1.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))

@[continuity]
lemma continuous_matrix_elem_snd (i j : Fin 2) :
  Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))

@[continuity]
lemma continuous_spinor_to_vec : Continuous spinor_to_vec := by
  apply continuous_pi
  intro i
  dsimp [spinor_to_vec]
  fin_cases i
  · change Continuous (fun (X : Matrix (Fin 2) (Fin 2) ℂ) => (X 0 0 + X 1 1) / 2)
    apply Continuous.div_const
    apply Continuous.add
    · exact (continuous_apply 0).comp (continuous_apply 0)
    · exact (continuous_apply 1).comp (continuous_apply 1)
  · change Continuous (fun (X : Matrix (Fin 2) (Fin 2) ℂ) => (X 0 1 + X 1 0) / 2)
    apply Continuous.div_const
    apply Continuous.add
    · exact (continuous_apply 1).comp (continuous_apply 0)
    · exact (continuous_apply 0).comp (continuous_apply 1)
  · change Continuous (fun (X : Matrix (Fin 2) (Fin 2) ℂ) => (X 0 1 - X 1 0) * Complex.I / 2)
    apply Continuous.div_const
    apply Continuous.mul
    · apply Continuous.sub
      · exact (continuous_apply 1).comp (continuous_apply 0)
      · exact (continuous_apply 0).comp (continuous_apply 1)
    · exact continuous_const
  · change Continuous (fun (X : Matrix (Fin 2) (Fin 2) ℂ) => (X 0 0 - X 1 1) / 2)
    apply Continuous.div_const
    apply Continuous.sub
    · exact (continuous_apply 0).comp (continuous_apply 0)
    · exact (continuous_apply 1).comp (continuous_apply 1)

lemma continuous_spinorPhi_matrix : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => spinorPhi_matrix p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h_eq : (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => spinorPhi_matrix p.1 p.2 i j) =
    (fun p => spinor_action p.1.1 p.2.1 (fun k => if k = j then 1 else 0) i) := by
    ext p
    exact spinorPhi_matrix_apply p.1 p.2 i j
  rw [h_eq]
  have h_A : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.1.1 : Matrix (Fin 2) (Fin 2) ℂ)) := continuous_subtype_val.comp continuous_fst
  have h_B : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) := continuous_subtype_val.comp continuous_snd
  have h_Bt : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) := Continuous.matrix_transpose h_B
  have h_X : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => vec_to_spinor (fun k => if k = j then (1:ℂ) else 0)) := continuous_const

  have h_mul1 : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => (p.1.1 : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor (fun k => if k = j then 1 else 0)) := Continuous.matrix_mul h_A h_X
  have h_mul2 : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => ((p.1.1 : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor (fun k => if k = j then 1 else 0)) * p.2.1ᵀ) := Continuous.matrix_mul h_mul1 h_Bt

  
  have h_eq2 : (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => spinor_action p.1.1 p.2.1 (fun k => if k = j then 1 else 0) i) =
    (fun p => spinor_to_vec (p.1.1 * vec_to_spinor (fun k => if k = j then 1 else 0) * p.2.1ᵀ) i) := rfl
  rw [h_eq2]
  exact (continuous_apply i).comp (continuous_spinor_to_vec.comp h_mul2)

noncomputable def spinorPhi_raw (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) : Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  { val := spinorPhi_matrix p.1 p.2,
    inv := spinorPhi_matrix p.1⁻¹ p.2⁻¹,
    val_inv := spinorPhi_matrix_inv p.1 p.2,
    inv_val := spinorPhi_matrix_inv' p.1 p.2 }

lemma continuous_spinorPhi_matrix_inv : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => spinorPhi_matrix p.1⁻¹ p.2⁻¹) := by
  have h_inv_fst : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => p.1⁻¹) := continuous_inv.comp continuous_fst
  have h_inv_snd : Continuous (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => p.2⁻¹) := continuous_inv.comp continuous_snd
  have h_eq : (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => spinorPhi_matrix p.1⁻¹ p.2⁻¹) =
              (fun p => spinorPhi_matrix p.1 p.2) ∘ (fun p => (p.1⁻¹, p.2⁻¹)) := by rfl
  rw [h_eq]
  exact continuous_spinorPhi_matrix.comp (Continuous.prodMk h_inv_fst h_inv_snd)

lemma continuous_spinorPhi_raw : Continuous spinorPhi_raw := by
  rw [Units.continuous_iff]
  constructor
  · have h1 : (Units.val ∘ spinorPhi_raw) = (fun p => spinorPhi_matrix p.1 p.2) := by
      ext p
      dsimp [spinorPhi_raw]
    rw [h1]
    exact continuous_spinorPhi_matrix
  · have h2 : (fun (p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ) => ↑(spinorPhi_raw p)⁻¹) = (fun p => spinorPhi_matrix p.1⁻¹ p.2⁻¹) := by
      funext p
      change (spinorPhi_raw p).inv = _
      rfl
    rw [h2]
    exact continuous_spinorPhi_matrix_inv

lemma continuous_spinorPhi : Continuous spinorPhi := by
  apply continuous_induced_rng.mpr
  have h : (Subtype.val ∘ ⇑spinorPhi) = spinorPhi_raw := by
    ext p i j
    dsimp [spinorPhi, spinorPhi_raw]
  rw [h]
  exact continuous_spinorPhi_raw


end Geometry







namespace Geometry.SpinorTopology

open Matrix Set Complex Topology Matrix.SpecialLinearGroup

private lemma sl2c_lower_det (z : ℂ) : (!![1, (0:ℂ); z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  simp [det_fin_two]

private lemma sl2c_upper_det (z : ℂ) : (!![1, z; (0:ℂ), 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  simp [det_fin_two]


lemma sl2c_joined_one_lower (z : ℂ) :
    Joined (1 : SpecialLinearGroup (Fin 2) ℂ)
           ⟨!![1, (0:ℂ); z, 1], sl2c_lower_det z⟩ := by
  refine ⟨⟨⟨fun t => ⟨!![1, (0:ℂ); (t:ℂ)*z, 1], by simp [det_fin_two]⟩, ?_⟩, ?_, ?_⟩⟩
  · apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · have h : (fun t : unitInterval => !![1, (0:ℂ); (t:ℂ)*z, 1] ⟨1, by norm_num⟩ ⟨0, by norm_num⟩) =
               (fun t : unitInterval => (t : ℂ) * z) := by ext t; simp [Matrix.of_apply]
      rw [h]
      exact (continuous_mul_const z).comp (Complex.continuous_ofReal.comp continuous_subtype_val)
    · exact continuous_const
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp


lemma sl2c_joined_one_upper (z : ℂ) :
    Joined (1 : SpecialLinearGroup (Fin 2) ℂ)
           ⟨!![1, z; (0:ℂ), 1], sl2c_upper_det z⟩ := by
  refine ⟨⟨⟨fun t => ⟨!![1, (t:ℂ)*z; (0:ℂ), 1], by simp [det_fin_two]⟩, ?_⟩, ?_, ?_⟩⟩
  · apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · have h : (fun t : unitInterval => !![1, (t:ℂ)*z; (0:ℂ), 1] ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) =
               (fun t : unitInterval => (t : ℂ) * z) := by ext t; simp [Matrix.of_apply]
      rw [h]
      exact (continuous_mul_const z).comp (Complex.continuous_ofReal.comp continuous_subtype_val)
    · exact continuous_const
    · exact continuous_const
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp


lemma sl2c_joined_one_diag (w : ℂ) :
    Joined (1 : SpecialLinearGroup (Fin 2) ℂ)
           ⟨!![(Complex.exp w), (0:ℂ); 0, Complex.exp (-w)],
            by simp [det_fin_two, ← Complex.exp_add]⟩ := by
  refine ⟨⟨⟨fun t => ⟨!![(Complex.exp ((t:ℂ)*w)), (0:ℂ); 0, Complex.exp (-(↑t*w))],
    by simp [det_fin_two]
       rw [← Complex.exp_add]; try ring_nf; simp [Complex.exp_zero]⟩, ?_⟩, ?_, ?_⟩⟩
  · apply Continuous.subtype_mk
    apply continuous_pi; intro i; apply continuous_pi; intro j
    fin_cases i <;> fin_cases j
    · have h : (fun t : unitInterval =>
          !![(Complex.exp ((t:ℂ)*w)), (0:ℂ); 0, Complex.exp (-(↑t*w))]
          ⟨0, by norm_num⟩ ⟨0, by norm_num⟩) =
          (fun t : unitInterval => Complex.exp ((t:ℂ)*w)) := by ext t; simp [Matrix.of_apply]
      rw [h]
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul_const w)
    · exact continuous_const
    · exact continuous_const
    · have h : (fun t : unitInterval =>
          !![(Complex.exp ((t:ℂ)*w)), (0:ℂ); 0, Complex.exp (-(↑t*w))]
          ⟨1, by norm_num⟩ ⟨1, by norm_num⟩) =
          (fun t : unitInterval => Complex.exp (-(↑t*w))) := by ext t; simp [Matrix.of_apply]
      rw [h]
      exact Complex.continuous_exp.comp
        (Continuous.neg ((Complex.continuous_ofReal.comp continuous_subtype_val).mul_const w))
  · 
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · 
    ext i j; fin_cases i <;> fin_cases j <;> simp


lemma sl2c_joined_to_identity (A : SpecialLinearGroup (Fin 2) ℂ) :
    Joined (1 : SpecialLinearGroup (Fin 2) ℂ) A := by
  set a := (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have hdet : a * d - b * c = 1 := by
    have h := A.property; simp only [Matrix.det_fin_two] at h; exact h
  by_cases hc : c = 0
  · 
    have ha : a ≠ 0 := by
      intro ha_eq
      simp only [hc, mul_zero, ha_eq, zero_mul, sub_zero] at hdet
      exact zero_ne_one hdet
    have had : a * d = 1 := by
      have hbc : b * c = 0 := by simp [hc]
      linear_combination hdet + hbc
    let L1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); 1, 1], sl2c_lower_det 1⟩
    let U1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (a-1)/a; (0:ℂ), 1], sl2c_upper_det _⟩
    let La : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); a, 1], sl2c_lower_det a⟩
    let U2 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (b+d-1)/a; (0:ℂ), 1], sl2c_upper_det _⟩
    have hA00 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a := rfl
    have hA01 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b := rfl
    have hA10 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c := rfl
    have hA11 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d := rfl
    have key : L1 * A = U1 * La * U2 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp [L1, U1, La, U2] <;> simp only [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Matrix.cons_val', Matrix.of_apply, hA00, hA01, hA10, hA11]
      · simp only [hc, mul_zero, add_zero, zero_add, mul_one, one_mul]
        have h1 : ((a - 1) / a) * a = a - 1 := div_mul_cancel₀ _ ha
        rw [h1]
        try ring
      · simp only [mul_zero, add_zero, zero_add, zero_mul, mul_one, one_mul]
        have h1 : ((a - 1) / a) * a = a - 1 := div_mul_cancel₀ _ ha
        have h2 : ((b + d - 1) / a) * a = b + d - 1 := div_mul_cancel₀ _ ha
        rw [h1]
        apply mul_right_cancel₀ ha
        rw [add_mul, mul_assoc, h2, h1]
        linear_combination -had
      · simp only [hc, mul_zero, add_zero, zero_add, mul_one, one_mul]
      · simp only [mul_zero, zero_add, mul_one, one_mul]
        have h2 : a * ((b + d - 1) / a) = b + d - 1 := by rw [mul_comm, div_mul_cancel₀ _ ha]
        rw [h2]
        try ring
    have j_l1 : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) L1 := sl2c_joined_one_lower 1
    have j_u1 : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) U1 := sl2c_joined_one_upper _
    have j_la : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) La := sl2c_joined_one_lower a
    have j_u2 : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) U2 := sl2c_joined_one_upper _
    have j_rhs' := (j_u1.mul j_la).mul j_u2
    have h111 : (1 : SpecialLinearGroup (Fin 2) ℂ) * 1 * 1 = 1 := by simp
    have j_rhs : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) (U1 * La * U2) := by
      have h : Joined ((1 : SpecialLinearGroup (Fin 2) ℂ) * 1 * 1) (U1 * La * U2) := j_rhs'
      rw [h111] at h
      exact h
    have j_L1A : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) (L1 * A) := by rw [key]; exact j_rhs
    have j_inv' := j_l1.inv
    have h1inv : (1 : SpecialLinearGroup (Fin 2) ℂ)⁻¹ = 1 := inv_one
    have j_inv : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) L1⁻¹ := by
      rw [h1inv] at j_inv'
      exact j_inv'
    have j_final' := j_inv.mul j_L1A
    have h11 : (1 : SpecialLinearGroup (Fin 2) ℂ) * 1 = 1 := mul_one 1
    have j_final : Joined (1 : SpecialLinearGroup (Fin 2) ℂ) (L1⁻¹ * (L1 * A)) := by
      have h : Joined ((1 : SpecialLinearGroup (Fin 2) ℂ) * 1) (L1⁻¹ * (L1 * A)) := j_final'
      rw [h11] at h
      exact h
    have cancel : L1⁻¹ * (L1 * A) = A := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [cancel] at j_final
    exact j_final
  · 
    let U1 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (a-1)/c; (0:ℂ), 1], sl2c_upper_det _⟩
    let Lc : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (0:ℂ); c, 1], sl2c_lower_det c⟩
    let U2 : SpecialLinearGroup (Fin 2) ℂ := ⟨!![1, (d-1)/c; (0:ℂ), 1], sl2c_upper_det _⟩
    have hA00 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a := rfl
    have hA01 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b := rfl
    have hA10 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c := rfl
    have hA11 : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d := rfl
    have decomp_group : A = U1 * Lc * U2 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp [U1, Lc, U2] <;> simp only [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, Matrix.cons_val', Matrix.of_apply, hA00, hA01, hA10, hA11]
      · simp only [mul_zero, add_zero, zero_add, mul_one]
        have h1 : ((a - 1) / c) * c = a - 1 := div_mul_cancel₀ _ hc
        rw [h1]
        try ring
      · simp only [mul_zero, zero_add, mul_one]
        have h1 : ((a - 1) / c) * c = a - 1 := div_mul_cancel₀ _ hc
        have h2 : ((d - 1) / c) * c = d - 1 := div_mul_cancel₀ _ hc
        rw [h1]
        apply mul_right_cancel₀ hc
        rw [add_mul, mul_assoc, h2, h1]
        linear_combination -hdet
      · simp only [mul_zero, add_zero, zero_add, mul_one, one_mul]
      · simp only [mul_zero, zero_add, mul_one, one_mul]
        have h2 : c * ((d - 1) / c) = d - 1 := by rw [mul_comm, div_mul_cancel₀ _ hc]
        rw [h2]
        try ring
    rw [decomp_group]
    have j1 := sl2c_joined_one_upper ((a - 1) / c)
    have j2 := sl2c_joined_one_lower c
    have j3 := sl2c_joined_one_upper ((d - 1) / c)
    have h12 := j1.mul j2
    have h123 := h12.mul j3
    simpa [mul_one, one_mul] using h123


instance : PathConnectedSpace (SpecialLinearGroup (Fin 2) ℂ) where
  nonempty := ⟨1⟩
  joined := fun x y => (sl2c_joined_to_identity x).symm.trans (sl2c_joined_to_identity y)


lemma sl2c_isConnected : IsConnected (Set.univ : Set (SpecialLinearGroup (Fin 2) ℂ)) :=
  isPathConnected_univ.isConnected


instance : PathConnectedSpace SpecialSpecialComplexLorentzGroup where
  nonempty := ⟨1⟩
  joined := fun x y => by
    obtain ⟨⟨A, B⟩, hAB⟩ := spinorPhi_surjective x
    obtain ⟨⟨C, D⟩, hCD⟩ := spinorPhi_surjective y
    have hj : Joined (A, B) (C, D) := PathConnectedSpace.joined _ _
    obtain ⟨γ⟩ := hj
    exact ⟨(γ.map continuous_spinorPhi).cast hAB.symm hCD.symm⟩

end Geometry.SpinorTopology
