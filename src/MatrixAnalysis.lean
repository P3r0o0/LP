import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Minkowski
import Spinor


open Matrix
open scoped ComplexOrder Norms.Operator

namespace Geometry.MatrixAnalysis


lemma posDef_isUnit {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef) : IsUnit A :=
  PosDef.isUnit hA

lemma posDef_one {n : Type*} [Fintype n] [DecidableEq n] : (1 : Matrix n n ℂ).PosDef := by
  rw [← diagonal_one]
  rw [posDef_diagonal_iff]
  intro i
  exact zero_lt_one


lemma posDef_star_mul_self_of_isUnit {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : IsUnit A) :
    (star A * A).PosDef := by
  have h_one : (1 : Matrix n n ℂ).PosDef := posDef_one
  have h_conj := hA.posDef_star_left_conjugate_iff.mpr h_one
  simp only [Matrix.mul_one] at h_conj
  exact h_conj


noncomputable def posDefSqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) : Matrix n n ℂ :=
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  let D_sqrt : Matrix n n ℂ := diagonal (fun i => (RCLike.ofReal (Real.sqrt (hA.1.eigenvalues i)) : ℂ))
  U * D_sqrt * star U


lemma posDefSqrt_D_mul_D {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    let D_sqrt : Matrix n n ℂ := diagonal (fun i => (RCLike.ofReal (Real.sqrt (hA.1.eigenvalues i)) : ℂ))
    D_sqrt * D_sqrt = diagonal (fun i => (RCLike.ofReal (hA.1.eigenvalues i) : ℂ)) := by
  intro D_sqrt
  congr 1
  rw [diagonal_mul_diagonal]
  congr
  ext i
  dsimp [D_sqrt]
  have h_mul : ((Real.sqrt (hA.1.eigenvalues i) : ℂ) * (Real.sqrt (hA.1.eigenvalues i) : ℂ)) =
    ((Real.sqrt (hA.1.eigenvalues i) * Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ) := by norm_cast
  rw [h_mul]
  have heig : 0 ≤ hA.1.eigenvalues i := Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg hA.1 |>.mp hA.posSemidef i
  rw [Real.mul_self_sqrt heig]


lemma posDefSqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    posDefSqrt A hA * posDefSqrt A hA = A := by
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  let D_sqrt : Matrix n n ℂ := diagonal (fun i => (RCLike.ofReal (Real.sqrt (hA.1.eigenvalues i)) : ℂ))
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hA.1.eigenvectorUnitary
  have hDD : D_sqrt * D_sqrt = diagonal (fun i => (RCLike.ofReal (hA.1.eigenvalues i) : ℂ)) := posDefSqrt_D_mul_D A hA

  calc posDefSqrt A hA * posDefSqrt A hA
    _ = (U * D_sqrt * star U) * (U * D_sqrt * star U) := rfl
    _ = U * D_sqrt * (star U * U) * D_sqrt * star U := by simp only [Matrix.mul_assoc]
    _ = U * D_sqrt * 1 * D_sqrt * star U := by rw [hUU]
    _ = U * (D_sqrt * D_sqrt) * star U := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = U * diagonal (fun i => (RCLike.ofReal (hA.1.eigenvalues i) : ℂ)) * star U := by rw [hDD]
    _ = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.1.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)) := by
      rw [Unitary.conjStarAlgAut_apply]
      rfl
    _ = A := hA.1.spectral_theorem.symm


lemma posDefSqrt_isPosDef {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    (posDefSqrt A hA).PosDef := by
  let U : Matrix n n ℂ := hA.1.eigenvectorUnitary
  let D_sqrt : Matrix n n ℂ := diagonal (fun i => (RCLike.ofReal (Real.sqrt (hA.1.eigenvalues i)) : ℂ))
  have hU_unit : IsUnit U := (Unitary.toUnits hA.1.eigenvectorUnitary).isUnit
  have hd_posdef : D_sqrt.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    have heig : 0 < hA.1.eigenvalues i := hA.eigenvalues_pos i
    have hsqrt : 0 < Real.sqrt (hA.1.eigenvalues i) := Real.sqrt_pos.mpr heig
    exact RCLike.ofReal_pos.mpr hsqrt
  exact hU_unit.posDef_star_right_conjugate_iff.mpr hd_posdef


lemma exists_posDef_sqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ (S : Matrix n n ℂ), S.PosDef ∧ S * S = A :=
  ⟨posDefSqrt A hA, posDefSqrt_isPosDef A hA, posDefSqrt_mul_self A hA⟩


lemma matrix_polar_decomp {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : IsUnit A) :
    ∃ (U P : Matrix n n ℂ),
      U ∈ unitaryGroup n ℂ ∧
      P.PosDef ∧
      A = U * P := by
  have h_posdef : (star A * A).PosDef := posDef_star_mul_self_of_isUnit A hA
  let P := posDefSqrt (star A * A) h_posdef
  have hP_posdef : P.PosDef := posDefSqrt_isPosDef (star A * A) h_posdef
  have hP_sq : P * P = star A * A := posDefSqrt_mul_self (star A * A) h_posdef
  have hP_unit : IsUnit P := posDef_isUnit hP_posdef
  let U := A * P⁻¹
  use U, P
  constructor
  · 
    have hP_det : IsUnit P.det := Iff.mp (Matrix.isUnit_iff_isUnit_det P) hP_unit
    have hP_inv_herm : (P⁻¹).IsHermitian := Matrix.IsHermitian.inv hP_posdef.1
    have h_star_U : star U = P⁻¹ * star A := by
      calc star U
        _ = star (A * P⁻¹) := rfl
        _ = star P⁻¹ * star A := star_mul A P⁻¹
        _ = P⁻¹ * star A := by
          have h_star_P_inv : star (P⁻¹) = P⁻¹ := hP_inv_herm.eq
          rw [h_star_P_inv]

    rw [Matrix.mem_unitaryGroup_iff']
    calc star U * U
      _ = (P⁻¹ * star A) * (A * P⁻¹) := by rw [h_star_U]
      _ = P⁻¹ * (star A * A) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hP_sq]
      _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 * 1 := by rw [Matrix.nonsing_inv_mul P hP_det, Matrix.mul_nonsing_inv P hP_det]
      _ = 1 := by simp
  · constructor
    · exact hP_posdef
    · 
      have hP_det : IsUnit P.det := Iff.mp (Matrix.isUnit_iff_isUnit_det P) hP_unit
      calc A
        _ = A * 1 := by rw [Matrix.mul_one]
        _ = A * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul P hP_det]
        _ = (A * P⁻¹) * P := by rw [← Matrix.mul_assoc]
        _ = U * P := rfl





noncomputable def sl2c_conj (A : SpecialLinearGroup (Fin 2) ℂ) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨Matrix.map A.1 star, by
    have h := A.2
    change _ = 1 at h
    simp only [det_fin_two] at h ⊢
    calc
      star (A.1 0 0) * star (A.1 1 1) - star (A.1 0 1) * star (A.1 1 0)
        = star (A.1 0 0) * star (A.1 1 1) - star (A.1 0 1) * star (A.1 1 0) := rfl
      _ = star (A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0) := by
        simp [star_sub, star_mul]
        ring
      _ = star (1 : ℂ) := by rw [h]
      _ = 1 := star_one ℂ⟩

lemma star_spinor_to_vec (Y : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) :
  star (spinor_to_vec Y i) = spinor_to_vec (Matrix.map Y star)ᵀ i := by
  have h2 : (starRingEnd ℂ) 2 = 2 := by
    have : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [this, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by rw [starRingEnd_apply, Complex.star_def, Complex.conj_I]
  fin_cases i
  · dsimp [spinor_to_vec]
    rw [map_div₀, map_add, starRingEnd_apply, starRingEnd_apply, h2]
  · dsimp [spinor_to_vec]
    rw [map_div₀, map_add, starRingEnd_apply, starRingEnd_apply, h2]
    ring
  · dsimp [spinor_to_vec]
    rw [map_div₀, map_mul, map_sub, hI, h2, starRingEnd_apply, starRingEnd_apply]
    ring
  · dsimp [spinor_to_vec]
    rw [map_div₀, map_sub, h2, starRingEnd_apply, starRingEnd_apply]

lemma map_star_vec_to_spinor_ej (j : Fin 4) :
  Matrix.map (vec_to_spinor (fun k => if k = j then (1 : ℂ) else 0)) star = (vec_to_spinor (fun k => if k = j then (1 : ℂ) else 0))ᵀ := by
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]

lemma map_star_mul {l m n : Type*} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    Matrix.map (A * B) star = Matrix.map A star * Matrix.map B star := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply]
  change (starRingEnd ℂ) (∑ x, A a x * B x b) = ∑ x, (starRingEnd ℂ) (A a x) * (starRingEnd ℂ) (B x b)
  rw [map_sum]
  congr 1
  ext x
  rw [map_mul]

lemma map_star_transpose {n m : Type*} (A : Matrix n m ℂ) :
    Matrix.map (Aᵀ) star = (Matrix.map A star)ᵀ := rfl


lemma spinorPhi_conj (A B : SpecialLinearGroup (Fin 2) ℂ) :
    Matrix.map (spinorPhi (A, B)).val.val star = (spinorPhi (sl2c_conj B, sl2c_conj A)).val.val := by
  ext i j
  change star (spinorPhi_matrix A B i j) = spinorPhi_matrix (sl2c_conj B) (sl2c_conj A) i j
  rw [spinorPhi_matrix_apply, spinorPhi_matrix_apply]
  dsimp only [spinor_action, sl2c_conj]
  rw [star_spinor_to_vec]
  congr 1
  rw [map_star_mul, map_star_mul]
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  rw [map_star_transpose]
  rw [Matrix.transpose_transpose]
  rw [map_star_vec_to_spinor_ej]
  rw [Matrix.transpose_transpose]
  rw [Matrix.mul_assoc]

lemma sl2c_conj_mul (A B : SpecialLinearGroup (Fin 2) ℂ) :
    sl2c_conj (A * B) = sl2c_conj A * sl2c_conj B := by
  apply Subtype.ext
  dsimp [sl2c_conj]
  change Matrix.map (A.1 * B.1) star = Matrix.map A.1 star * Matrix.map B.1 star
  exact map_star_mul A.1 B.1

lemma sl2c_conj_one : sl2c_conj 1 = 1 := by
  apply Subtype.ext
  ext i j
  dsimp [sl2c_conj]
  fin_cases i <;> fin_cases j <;> simp

lemma sl2c_conj_inv (A : SpecialLinearGroup (Fin 2) ℂ) :
    sl2c_conj (A⁻¹) = (sl2c_conj A)⁻¹ := by
  calc sl2c_conj (A⁻¹)
    _ = 1 * sl2c_conj (A⁻¹) := by rw [one_mul]
    _ = (sl2c_conj A)⁻¹ * sl2c_conj A * sl2c_conj (A⁻¹) := by rw [inv_mul_cancel]
    _ = (sl2c_conj A)⁻¹ * (sl2c_conj A * sl2c_conj (A⁻¹)) := by rw [mul_assoc]
    _ = (sl2c_conj A)⁻¹ * sl2c_conj (A * A⁻¹) := by rw [← sl2c_conj_mul]
    _ = (sl2c_conj A)⁻¹ * sl2c_conj 1 := by rw [mul_inv_cancel]
    _ = (sl2c_conj A)⁻¹ * 1 := by rw [sl2c_conj_one]
    _ = (sl2c_conj A)⁻¹ := by rw [mul_one]

lemma sl2c_conj_sl2c_conj (A : SpecialLinearGroup (Fin 2) ℂ) :
    sl2c_conj (sl2c_conj A) = A := by
  apply Subtype.ext
  ext i j
  dsimp [sl2c_conj]
  change star (star (A.1 i j)) = A.1 i j
  rw [star_star]

lemma spinorPhi_matrix_inv_eq (A B : SpecialLinearGroup (Fin 2) ℂ) :
    (spinorPhi_matrix A B)⁻¹ = spinorPhi_matrix A⁻¹ B⁻¹ := by
  exact Matrix.inv_eq_right_inv (spinorPhi_matrix_inv A B)


lemma spinorPhi_S_matrix (A B : SpecialLinearGroup (Fin 2) ℂ) :
    ∃ (C : SpecialLinearGroup (Fin 2) ℂ),
      (spinorPhi (A, B)).val.val * (Matrix.map (spinorPhi (A, B)).val.val star)⁻¹ =
      (spinorPhi (C, (sl2c_conj C)⁻¹)).val.val := by
  use A * (sl2c_conj B)⁻¹
  have h_conj : Matrix.map (spinorPhi (A, B)).val.val star = (spinorPhi (sl2c_conj B, sl2c_conj A)).val.val := spinorPhi_conj A B
  rw [h_conj]
  change spinorPhi_matrix A B * (spinorPhi_matrix (sl2c_conj B) (sl2c_conj A))⁻¹ = _
  rw [spinorPhi_matrix_inv_eq]
  rw [← spinorPhi_matrix_mul]
  congr 1
  rw [sl2c_conj_mul, sl2c_conj_inv, sl2c_conj_sl2c_conj, _root_.mul_inv_rev, inv_inv]

lemma exp_supp_subset_3 {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) (hN : N ^ 3 = 0) :
    ∀ k ∉ ({0, 1, 2} : Finset ℕ), ((k.factorial : ℚ)⁻¹ : ℚ) • (N ^ k) = 0 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hk3 : 3 ≤ k := by omega
  have hNk : N ^ k = 0 := by
    calc N ^ k = N ^ 3 * N ^ (k - 3) := by rw [← pow_add, Nat.add_sub_of_le hk3]
      _ = 0 * N ^ (k - 3) := by rw [hN]
      _ = 0 := zero_mul _
  rw [hNk, smul_zero]

lemma exp_of_nilpotent3 {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ) (hN : N ^ 3 = 0) :
    NormedSpace.exp N = 1 + N + (1 / 2 : ℂ) • (N ^ 2) := by
  let f : ℕ → Matrix n n ℂ := fun k => ((k.factorial : ℚ)⁻¹ : ℚ) • (N ^ k)
  have h_exp_N : NormedSpace.exp N = ∑' (k : ℕ), f k := by
    have h_exp := NormedSpace.exp_eq_tsum_rat (𝔸 := Matrix n n ℂ)
    exact congrFun h_exp N
  rw [h_exp_N]
  have h_supp : ∀ k ∉ ({0, 1, 2} : Finset ℕ), f k = 0 := exp_supp_subset_3 N hN
  have h_sum : ∑' (k : ℕ), f k = ∑ k ∈ ({0, 1, 2} : Finset ℕ), f k := by
    apply tsum_eq_sum h_supp
  rw [h_sum]
  dsimp [f]
  conv_lhs => simp [Finset.sum_insert, Finset.sum_singleton]
  have c2 : ((2⁻¹ : ℚ) • N ^ 2) = (1 / 2 : ℂ) • N ^ 2 := by
    ext i j
    have : ((2⁻¹ : ℚ) : ℂ) = 1 / 2 := by norm_num
    calc ((2⁻¹ : ℚ) • N ^ 2) i j = (2⁻¹ : ℚ) * (N ^ 2) i j := rfl
      _ = ((2⁻¹ : ℚ) : ℂ) * (N ^ 2) i j := by simp
      _ = (1 / 2 : ℂ) * (N ^ 2) i j := by rw [this]
      _ = ((1 / 2 : ℂ) • N ^ 2) i j := rfl
  rw [c2]
  abel
noncomputable def M_D (a : ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let u := (Complex.log a).re
  let v := (Complex.log a).im
  of ![![0, 0, 0, v],
       ![0, 0, -u, 0],
       ![0, u, 0, 0],
       ![v, 0, 0, 0]]

lemma M_D_lorentz (a : ℂ) :
    (M_D a)ᵀ * minkowskiMetricReal + minkowskiMetricReal * M_D a = 0 := by
  dsimp [M_D, minkowskiMetricReal, vec_to_spinor, spinor_to_vec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

noncomputable def J_mat (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  of ![![1, c], ![0, 1]]

lemma J_mat_det (c : ℂ) : (J_mat c).det = 1 := by
  dsimp [J_mat]
  simp [Matrix.det_fin_two]

noncomputable def jordan_matrix (c : ℂ) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨J_mat c, J_mat_det c⟩

noncomputable def M_J (c : ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let c1 := c.re
  let c2 := c.im
  (1 / 2 : ℝ) • of ![![0, c2, c1, 0],
                     ![c2, 0, 0, -c2],
                     ![c1, 0, 0, -c1],
                     ![0, c2, c1, 0]]

lemma M_J_lorentz (c : ℂ) :
    (M_J c)ᵀ * minkowskiMetricReal + minkowskiMetricReal * M_J c = 0 := by
  dsimp [M_J, minkowskiMetricReal, vec_to_spinor, spinor_to_vec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

noncomputable def N_mat (c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((2 * Complex.I) : ℂ) • Matrix.map (M_J c) (fun x => (x : ℂ))

lemma N_mat_eq (c : ℂ) :
    N_mat c = of ![![0, Complex.I * (c.im : ℂ), Complex.I * (c.re : ℂ), 0],
                   ![Complex.I * (c.im : ℂ), 0, 0, -Complex.I * (c.im : ℂ)],
                   ![Complex.I * (c.re : ℂ), 0, 0, -Complex.I * (c.re : ℂ)],
                   ![0, Complex.I * (c.im : ℂ), Complex.I * (c.re : ℂ), 0]] := by
  dsimp [N_mat, M_J]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

lemma N_mat_sq_eq (c : ℂ) :
    N_mat c * N_mat c = of ![![-((c.im : ℂ) * (c.im : ℂ)) - ((c.re : ℂ) * (c.re : ℂ)), 0, 0, ((c.im : ℂ) * (c.im : ℂ)) + ((c.re : ℂ) * (c.re : ℂ))],
                             ![0, 0, 0, 0],
                             ![0, 0, 0, 0],
                             ![-((c.im : ℂ) * (c.im : ℂ)) - ((c.re : ℂ) * (c.re : ℂ)), 0, 0, ((c.im : ℂ) * (c.im : ℂ)) + ((c.re : ℂ) * (c.re : ℂ))]] := by
  rw [N_mat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals {
    try ring_nf
    try simp only [Complex.I_sq]
    try ring
  }

lemma N_mat_cube_eq (c : ℂ) :
    (N_mat c * N_mat c) * N_mat c = 0 := by
  rw [N_mat_sq_eq, N_mat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals {
    try ring_nf
    try simp only [Complex.I_sq]
    try ring
  }


@[simp] lemma vec_to_spinor_single_0 : vec_to_spinor (Pi.single 0 1 : Fin 4 → ℂ) = sigma_0 := by
  ext i j; dsimp [vec_to_spinor, Pi.single, Function.update, sigma_0, sigma_1, sigma_2, sigma_3]; fin_cases i <;> fin_cases j <;> simp

@[simp] lemma vec_to_spinor_single_1 : vec_to_spinor (Pi.single 1 1 : Fin 4 → ℂ) = sigma_1 := by
  ext i j; dsimp [vec_to_spinor, Pi.single, Function.update, sigma_0, sigma_1, sigma_2, sigma_3]; fin_cases i <;> fin_cases j <;> simp

@[simp] lemma vec_to_spinor_single_2 : vec_to_spinor (Pi.single 2 1 : Fin 4 → ℂ) = sigma_2 := by
  ext i j; dsimp [vec_to_spinor, Pi.single, Function.update, sigma_0, sigma_1, sigma_2, sigma_3]; fin_cases i <;> fin_cases j <;> simp

@[simp] lemma vec_to_spinor_single_3 : vec_to_spinor (Pi.single 3 1 : Fin 4 → ℂ) = sigma_3 := by
  ext i j; dsimp [vec_to_spinor, Pi.single, Function.update, sigma_0, sigma_1, sigma_2, sigma_3]; fin_cases i <;> fin_cases j <;> simp

lemma spinorPhi_S_matrix_to_M_jordan_eq_0_0 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 0 0 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 0 0 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 0 0
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_0, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two,]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_0_1 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 0 1 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 0 1 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 0 1
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_1, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_0_2 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 0 2 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 0 2 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 0 2
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_2, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_0_3 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 0 3 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 0 3 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 0 3
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_3, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_1_0 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 1 0 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 1 0 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 1 0
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_0, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_1_1 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 1 1 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 1 1 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 1 1
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_1, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_1_2 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 1 2 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 1 2 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 1 2
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_2, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_1_3 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 1 3 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 1 3 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 1 3
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_3, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_2_0 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 2 0 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 2 0 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 2 0
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_0, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_2_1 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 2 1 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 2 1 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 2 1
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_1, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_2_2 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 2 2 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 2 2 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 2 2
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_2, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_2_3 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 2 3 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 2 3 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 2 3
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_3, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_3_0 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 3 0 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 3 0 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 3 0
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_0, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_3_1 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 3 1 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 3 1 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 3 1
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_1, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_3_2 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 3 2 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 3 2 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 3 2
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_2, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq_3_3 (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val 3 3 = (1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c)) 3 3 := by
  dsimp [jordan_matrix, spinorPhi, spinorPhi_matrix, spinor_action_linear, spinor_action, vec_to_spinor, spinor_to_vec, sl2c_conj]
  rcases c with ⟨c_re, c_im⟩
  change _ = (1 + N_mat { re := c_re, im := c_im } + (1 / 2 : ℂ) • (N_mat { re := c_re, im := c_im } * N_mat { re := c_re, im := c_im })) 3 3
  rw [N_mat_sq_eq, N_mat_eq]
  simp [J_mat, sigma_3, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two]
  try {
    apply Complex.ext
    all_goals {
      push_cast
      simp
      try ring
    }
  }

lemma spinorPhi_S_matrix_to_M_jordan_eq (c : ℂ) :
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val = 1 + N_mat c + (1 / 2 : ℂ) • (N_mat c * N_mat c) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact spinorPhi_S_matrix_to_M_jordan_eq_0_0 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_0_1 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_0_2 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_0_3 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_1_0 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_1_1 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_1_2 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_1_3 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_2_0 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_2_1 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_2_2 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_2_3 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_3_0 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_3_1 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_3_2 c
  · exact spinorPhi_S_matrix_to_M_jordan_eq_3_3 c




lemma N_mat_nilpotent (c : ℂ) : (N_mat c) ^ 3 = 0 := by
  calc (N_mat c) ^ 3 = (N_mat c) ^ 2 * N_mat c := by rw [pow_succ]
    _ = (N_mat c * N_mat c) * N_mat c := by rw [pow_two]
    _ = 0 := N_mat_cube_eq c

lemma spinorPhi_S_matrix_to_M_jordan (c : ℂ) :
    ∃ (M : Matrix (Fin 4) (Fin 4) ℝ),
      Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0 ∧
      (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map M (fun x => (x : ℂ))) := by
  use M_J c
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [M_J, minkowskiMetricReal, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · have h_nilp : (((2 * Complex.I) : ℂ) • Matrix.map (M_J c) (fun x => (x : ℂ))) ^ 3 = 0 := N_mat_nilpotent c
    rw [exp_of_nilpotent3 _ h_nilp]
    have h_pow2 : (((2 * Complex.I) : ℂ) • Matrix.map (M_J c) (fun x => (x : ℂ))) ^ 2 = N_mat c * N_mat c := by
      change N_mat c ^ 2 = N_mat c * N_mat c
      rw [pow_two]
    rw [h_pow2]
    exact spinorPhi_S_matrix_to_M_jordan_eq c


noncomputable def diag_matrix (a : ℂ) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨of ![![a, 0], ![0, a⁻¹]], by
    simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_inv_cancel₀ ha⟩

noncomputable def P_mat : Matrix (Fin 4) (Fin 4) ℂ :=
  of ![![1, 1, 0, 0],
       ![0, 0, 1, 1],
       ![0, 0, Complex.I, -Complex.I],
       ![1, -1, 0, 0]]

noncomputable def P_inv : Matrix (Fin 4) (Fin 4) ℂ :=
  of ![![1/2, 0, 0, 1/2],
       ![1/2, 0, 0, -1/2],
       ![0, 1/2, -Complex.I/2, 0],
       ![0, 1/2, Complex.I/2, 0]]

lemma P_inv_P : P_inv * P_mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_mat, P_inv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try ring_nf <;> try simp only [Complex.I_sq] <;> norm_num <;> try ring

lemma P_P_inv : P_mat * P_inv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_mat, P_inv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try ring_nf <;> try simp only [Complex.I_sq] <;> norm_num <;> try ring

lemma P_isUnit : IsUnit P_mat :=
  ⟨⟨P_mat, P_inv, P_P_inv, P_inv_P⟩, rfl⟩

noncomputable def D_mat (η θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diagonal ![(2 * Complex.I * θ : ℂ), -2 * Complex.I * θ, 2 * η, -2 * η]

lemma P_mat_mul_diagonal (a b c d : ℂ) :
    P_mat * diagonal ![a, b, c, d] =
    of ![![a, b, 0, 0],
         ![0, 0, c, d],
         ![0, 0, c * Complex.I, d * -Complex.I],
         ![a, -b, 0, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [P_mat, diagonal, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring_nf; try simp only [Complex.I_sq]; try ring
  }

lemma P_mat_mul_diagonal_mul_P_inv (a b c d : ℂ) :
    P_mat * diagonal ![a, b, c, d] * P_inv =
    of ![![a * (1/2 : ℂ) + b * (1/2 : ℂ), 0, 0, a * (1/2 : ℂ) + b * (-1/2 : ℂ)],
         ![0, c * (1/2 : ℂ) + d * (1/2 : ℂ), c * (-Complex.I / 2 : ℂ) + d * (Complex.I / 2 : ℂ), 0],
         ![0, c * (Complex.I / 2 : ℂ) + d * (-Complex.I / 2 : ℂ), c * (1/2 : ℂ) + d * (1/2 : ℂ), 0],
         ![a * (1/2 : ℂ) + b * (-1/2 : ℂ), 0, 0, a * (1/2 : ℂ) + b * (1/2 : ℂ)]] := by
  rw [P_mat_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [P_inv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Complex.I_sq, Complex.I_mul_I]
    try ring_nf; try simp only [Complex.I_sq]; try ring
  }

lemma P_D_P_inv_eq_0_0 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 0 0 = (a * (1/2 : ℂ)) + (b * (1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_0_1 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 0 1 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_0_2 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 0 2 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_0_3 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 0 3 = (a * (1/2 : ℂ)) + (b * (-1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_1_0 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 1 0 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_1_1 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 1 1 = (c * (1/2 : ℂ)) + (d * (1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_1_2 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 1 2 = (c * (-Complex.I / 2 : ℂ)) + (d * (Complex.I / 2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_1_3 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 1 3 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_2_0 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 2 0 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_2_1 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 2 1 = (c * (Complex.I / 2 : ℂ)) + (d * (-Complex.I / 2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_2_2 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 2 2 = (c * (1/2 : ℂ)) + (d * (1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_2_3 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 2 3 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_3_0 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 3 0 = (a * (1/2 : ℂ)) + (b * (-1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_3_1 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 3 1 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_3_2 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 3 2 = 0 := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl

lemma P_D_P_inv_eq_3_3 (a b c d : ℂ) :
    (P_mat * diagonal ![a, b, c, d] * P_inv) 3 3 = (a * (1/2 : ℂ)) + (b * (1/2 : ℂ)) := by
  rw [P_mat_mul_diagonal_mul_P_inv]; rfl


lemma P_D_P_inv_D_mat (η θ : ℝ) :
    P_mat * D_mat η θ * P_inv =
    of ![![(2 * Complex.I * θ : ℂ) * (1/2 : ℂ) + (-2 * Complex.I * θ : ℂ) * (1/2 : ℂ), 0, 0, (2 * Complex.I * θ : ℂ) * (1/2 : ℂ) + (-2 * Complex.I * θ : ℂ) * (-1/2 : ℂ)],
         ![0, (2 * η : ℂ) * (1/2 : ℂ) + (-2 * η : ℂ) * (1/2 : ℂ), (2 * η : ℂ) * (-Complex.I / 2 : ℂ) + (-2 * η : ℂ) * (Complex.I / 2 : ℂ), 0],
         ![0, (2 * η : ℂ) * (Complex.I / 2 : ℂ) + (-2 * η : ℂ) * (-Complex.I / 2 : ℂ), (2 * η : ℂ) * (1/2 : ℂ) + (-2 * η : ℂ) * (1/2 : ℂ), 0],
         ![(2 * Complex.I * θ : ℂ) * (1/2 : ℂ) + (-2 * Complex.I * θ : ℂ) * (-1/2 : ℂ), 0, 0, (2 * Complex.I * θ : ℂ) * (1/2 : ℂ) + (-2 * Complex.I * θ : ℂ) * (1/2 : ℂ)]] := by
  unfold D_mat
  exact P_mat_mul_diagonal_mul_P_inv _ _ _ _

lemma M_D_entry_eq (η θ : ℝ) (i j : Fin 4) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) i j = (P_mat * D_mat η θ * P_inv) i j := by
  rw [P_D_P_inv_D_mat]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply] <;> ring

lemma M_D_eq_P_D_P_inv_eq_0_0 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 0 0 = (P_mat * D_mat η θ * P_inv) 0 0 :=
  M_D_entry_eq η θ 0 0

lemma M_D_eq_P_D_P_inv_eq_0_1 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 0 1 = (P_mat * D_mat η θ * P_inv) 0 1 :=
  M_D_entry_eq η θ 0 1

lemma M_D_eq_P_D_P_inv_eq_0_2 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 0 2 = (P_mat * D_mat η θ * P_inv) 0 2 :=
  M_D_entry_eq η θ 0 2

lemma M_D_eq_P_D_P_inv_eq_0_3 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 0 3 = (P_mat * D_mat η θ * P_inv) 0 3 :=
  M_D_entry_eq η θ 0 3

lemma M_D_eq_P_D_P_inv_eq_1_0 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 1 0 = (P_mat * D_mat η θ * P_inv) 1 0 :=
  M_D_entry_eq η θ 1 0

lemma M_D_eq_P_D_P_inv_eq_1_1 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 1 1 = (P_mat * D_mat η θ * P_inv) 1 1 :=
  M_D_entry_eq η θ 1 1

lemma M_D_eq_P_D_P_inv_eq_1_2 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 1 2 = (P_mat * D_mat η θ * P_inv) 1 2 :=
  M_D_entry_eq η θ 1 2

lemma M_D_eq_P_D_P_inv_eq_1_3 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 1 3 = (P_mat * D_mat η θ * P_inv) 1 3 :=
  M_D_entry_eq η θ 1 3

lemma M_D_eq_P_D_P_inv_eq_2_0 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 2 0 = (P_mat * D_mat η θ * P_inv) 2 0 :=
  M_D_entry_eq η θ 2 0

lemma M_D_eq_P_D_P_inv_eq_2_1 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 2 1 = (P_mat * D_mat η θ * P_inv) 2 1 :=
  M_D_entry_eq η θ 2 1

lemma M_D_eq_P_D_P_inv_eq_2_2 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 2 2 = (P_mat * D_mat η θ * P_inv) 2 2 :=
  M_D_entry_eq η θ 2 2

lemma M_D_eq_P_D_P_inv_eq_2_3 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 2 3 = (P_mat * D_mat η θ * P_inv) 2 3 :=
  M_D_entry_eq η θ 2 3

lemma M_D_eq_P_D_P_inv_eq_3_0 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 3 0 = (P_mat * D_mat η θ * P_inv) 3 0 :=
  M_D_entry_eq η θ 3 0

lemma M_D_eq_P_D_P_inv_eq_3_1 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 3 1 = (P_mat * D_mat η θ * P_inv) 3 1 :=
  M_D_entry_eq η θ 3 1

lemma M_D_eq_P_D_P_inv_eq_3_2 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 3 2 = (P_mat * D_mat η θ * P_inv) 3 2 :=
  M_D_entry_eq η θ 3 2

lemma M_D_eq_P_D_P_inv_eq_3_3 (η θ : ℝ) :
    ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) 3 3 = (P_mat * D_mat η θ * P_inv) 3 3 :=
  M_D_entry_eq η θ 3 3


lemma M_D_eq_P_D_P_inv (η θ : ℝ) :
    (2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ)) = P_mat * D_mat η θ * P_inv := by
  ext i j; fin_cases i <;> fin_cases j
  · exact M_D_eq_P_D_P_inv_eq_0_0 η θ
  · exact M_D_eq_P_D_P_inv_eq_0_1 η θ
  · exact M_D_eq_P_D_P_inv_eq_0_2 η θ
  · exact M_D_eq_P_D_P_inv_eq_0_3 η θ
  · exact M_D_eq_P_D_P_inv_eq_1_0 η θ
  · exact M_D_eq_P_D_P_inv_eq_1_1 η θ
  · exact M_D_eq_P_D_P_inv_eq_1_2 η θ
  · exact M_D_eq_P_D_P_inv_eq_1_3 η θ
  · exact M_D_eq_P_D_P_inv_eq_2_0 η θ
  · exact M_D_eq_P_D_P_inv_eq_2_1 η θ
  · exact M_D_eq_P_D_P_inv_eq_2_2 η θ
  · exact M_D_eq_P_D_P_inv_eq_2_3 η θ
  · exact M_D_eq_P_D_P_inv_eq_3_0 η θ
  · exact M_D_eq_P_D_P_inv_eq_3_1 η θ
  · exact M_D_eq_P_D_P_inv_eq_3_2 η θ
  · exact M_D_eq_P_D_P_inv_eq_3_3 η θ

lemma exp_conj_matrix {n : Type*} [Fintype n] [DecidableEq n] (P D P_inv : Matrix n n ℂ) (h1 : P * P_inv = 1) (h2 : P_inv * P = 1) :
    NormedSpace.exp (P * D * P_inv) = P * NormedSpace.exp D * P_inv := by
  let U : (Matrix n n ℂ)ˣ := ⟨P, P_inv, h1, h2⟩
  have h_conj := NormedSpace.exp_units_conj U D
  have h_U_val : (U : Matrix n n ℂ) = P := rfl
  have h_U_inv : (↑U⁻¹ : Matrix n n ℂ) = P_inv := rfl
  rw [h_U_val, h_U_inv] at h_conj
  exact h_conj

lemma exp_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) :
    NormedSpace.exp (diagonal d) = diagonal (NormedSpace.exp d) := by
  have h_cont : Continuous (Matrix.diagonalRingHom (n := n) (α := ℂ)) := continuous_pi (fun i => continuous_pi (fun j => by
    by_cases h : i = j
    · rw [h]; simpa using continuous_apply _
    · simpa [h] using continuous_const
  ))
  have := (NormedSpace.map_exp (Matrix.diagonalRingHom (n := n) (α := ℂ)) h_cont d).symm
  exact this

lemma exp_pi_apply {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) (i : n) :
    (NormedSpace.exp d) i = NormedSpace.exp (d i) := by
  have := (NormedSpace.map_exp (Pi.evalRingHom (fun _ => ℂ) i) (continuous_apply i) d)
  exact this

lemma exp_M_D (η θ : ℝ) :
    NormedSpace.exp ((2 * Complex.I : ℂ) • Matrix.map (of ![![0, 0, 0, θ], ![0, 0, -η, 0], ![0, η, 0, 0], ![θ, 0, 0, 0]]) (fun x => (x : ℂ))) =
    P_mat * diagonal ![NormedSpace.exp (2 * Complex.I * θ : ℂ), NormedSpace.exp (-2 * Complex.I * θ : ℂ), NormedSpace.exp (2 * η : ℂ), NormedSpace.exp (-2 * η : ℂ)] * P_inv := by
  rw [M_D_eq_P_D_P_inv η θ]
  have h_conj : NormedSpace.exp (P_mat * D_mat η θ * P_inv) = P_mat * NormedSpace.exp (D_mat η θ) * P_inv := exp_conj_matrix P_mat (D_mat η θ) P_inv P_P_inv P_inv_P
  rw [h_conj]
  have h_diag : NormedSpace.exp (D_mat η θ) = diagonal ![NormedSpace.exp (2 * Complex.I * θ : ℂ), NormedSpace.exp (-2 * Complex.I * θ : ℂ), NormedSpace.exp (2 * η : ℂ), NormedSpace.exp (-2 * η : ℂ)] := by
    rw [D_mat]
    rw [exp_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h_diag]



lemma vec_to_spinor_basis_0 : vec_to_spinor (fun k : Fin 4 => if k = 0 then (1:ℂ) else 0) = of sigma_0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.of_apply]

lemma vec_to_spinor_basis_1 : vec_to_spinor (fun k : Fin 4 => if k = 1 then (1:ℂ) else 0) = of sigma_1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.of_apply]

lemma vec_to_spinor_basis_2 : vec_to_spinor (fun k : Fin 4 => if k = 2 then (1:ℂ) else 0) = of sigma_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.of_apply]

lemma vec_to_spinor_basis_3 : vec_to_spinor (fun k : Fin 4 => if k = 3 then (1:ℂ) else 0) = of sigma_3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.of_apply]


lemma diag_matrix_mul_sigma_0 (a : ℂ) (ha : a ≠ 0) :
  (diag_matrix a ha : Matrix (Fin 2) (Fin 2) ℂ) * of sigma_0 * (sl2c_conj (diag_matrix a ha) : Matrix (Fin 2) (Fin 2) ℂ).adjugateᵀ =
  of ![![a * (star a)⁻¹, 0], ![0, a⁻¹ * star a]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix, sl2c_conj, sigma_0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two, Matrix.vecHead, Matrix.vecTail, Subtype.coe_mk] <;> ring

lemma diag_matrix_mul_sigma_1 (a : ℂ) (ha : a ≠ 0) :
  (diag_matrix a ha : Matrix (Fin 2) (Fin 2) ℂ) * of sigma_1 * (sl2c_conj (diag_matrix a ha) : Matrix (Fin 2) (Fin 2) ℂ).adjugateᵀ =
  of ![![0, a * star a], ![a⁻¹ * (star a)⁻¹, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix, sl2c_conj, sigma_1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two, Matrix.vecHead, Matrix.vecTail, Subtype.coe_mk] <;> ring

lemma diag_matrix_mul_sigma_2 (a : ℂ) (ha : a ≠ 0) :
  (diag_matrix a ha : Matrix (Fin 2) (Fin 2) ℂ) * of sigma_2 * (sl2c_conj (diag_matrix a ha) : Matrix (Fin 2) (Fin 2) ℂ).adjugateᵀ =
  of ![![0, a * star a * -Complex.I], ![a⁻¹ * (star a)⁻¹ * Complex.I, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix, sl2c_conj, sigma_2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two, Matrix.vecHead, Matrix.vecTail, Subtype.coe_mk] <;> ring

lemma diag_matrix_mul_sigma_3 (a : ℂ) (ha : a ≠ 0) :
  (diag_matrix a ha : Matrix (Fin 2) (Fin 2) ℂ) * of sigma_3 * (sl2c_conj (diag_matrix a ha) : Matrix (Fin 2) (Fin 2) ℂ).adjugateᵀ =
  of ![![a * (star a)⁻¹, 0], ![0, -(a⁻¹ * star a)]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag_matrix, sl2c_conj, sigma_3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.adjugate_fin_two, Matrix.vecHead, Matrix.vecTail, Subtype.coe_mk] <;> ring


lemma spinorPhi_matrix_diag_col_0 (a : ℂ) (ha : a ≠ 0) (i : Fin 4) :
  spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 0 =
  spinor_to_vec (of ![![a * (star a)⁻¹, 0], ![0, a⁻¹ * star a]]) i := by
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 0 = _
  rw [spinorPhi_matrix_apply]
  simp [spinor_action, vec_to_spinor_basis_0, diag_matrix_mul_sigma_0 a ha]

lemma spinorPhi_matrix_diag_col_1 (a : ℂ) (ha : a ≠ 0) (i : Fin 4) :
  spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 1 =
  spinor_to_vec (of ![![0, a * star a], ![a⁻¹ * (star a)⁻¹, 0]]) i := by
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 1 = _
  rw [spinorPhi_matrix_apply]
  simp [spinor_action, vec_to_spinor_basis_1, diag_matrix_mul_sigma_1 a ha]

lemma spinorPhi_matrix_diag_col_2 (a : ℂ) (ha : a ≠ 0) (i : Fin 4) :
  spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 2 =
  spinor_to_vec (of ![![0, a * star a * -Complex.I], ![a⁻¹ * (star a)⁻¹ * Complex.I, 0]]) i := by
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 2 = _
  rw [spinorPhi_matrix_apply]
  simp [spinor_action, vec_to_spinor_basis_2, diag_matrix_mul_sigma_2 a ha]

lemma spinorPhi_matrix_diag_col_3 (a : ℂ) (ha : a ≠ 0) (i : Fin 4) :
  spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 3 =
  spinor_to_vec (of ![![a * (star a)⁻¹, 0], ![0, -(a⁻¹ * star a)]]) i := by
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) i 3 = _
  rw [spinorPhi_matrix_apply]
  simp [spinor_action, vec_to_spinor_basis_3, diag_matrix_mul_sigma_3 a ha]


lemma exp_two_re_log (a : ℂ) (ha : a ≠ 0) :
    NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := by
  rw [← Complex.exp_eq_exp_ℂ]
  have H1 : 2 * ((Complex.log a).re : ℂ) = ((Complex.log a).re : ℂ) + ((Complex.log a).re : ℂ) := by ring
  rw [H1, Complex.exp_add]
  have H2 : ((Complex.log a).re : ℂ) = (Real.log ‖a‖ : ℂ) := by rw [Complex.log_re a]
  rw [H2, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr ha)]
  have H4 : (‖a‖ : ℂ) * (‖a‖ : ℂ) = (Complex.normSq a : ℂ) := calc
    (‖a‖ : ℂ) * (‖a‖ : ℂ) = (‖a‖ : ℂ) ^ 2 := by ring
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    _ = (Complex.normSq a : ℂ) := by rw [Complex.sq_norm a]
  rw [H4]
  exact (Complex.mul_conj a).symm

lemma exp_two_re_log_neg (a : ℂ) (ha : a ≠ 0) :
    NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := by
  rw [← Complex.exp_eq_exp_ℂ, neg_mul, Complex.exp_neg]
  have : Complex.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := by
    have : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
    rwa [← Complex.exp_eq_exp_ℂ] at this
  rw [this]

lemma exp_two_im_log (a : ℂ) (ha : a ≠ 0) :
    NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := by
  rw [← Complex.exp_eq_exp_ℂ]
  have H1 : 2 * Complex.I * ((Complex.log a).im : ℂ) = (Complex.I * ((Complex.log a).im : ℂ)) + (Complex.I * ((Complex.log a).im : ℂ)) := by ring
  rw [H1, Complex.exp_add]
  have H2 : Complex.exp (Complex.I * ((Complex.log a).im : ℂ)) = a * (‖a‖ : ℂ)⁻¹ := by
    have h_log : Complex.exp (Complex.log a) = a := Complex.exp_log ha
    have h_re_im : ((Complex.log a).re : ℂ) + ((Complex.log a).im : ℂ) * Complex.I = Complex.log a := Complex.re_add_im (Complex.log a)
    rw [← h_re_im] at h_log
    rw [Complex.exp_add] at h_log
    have h_re : Complex.exp ((Complex.log a).re : ℂ) = (‖a‖ : ℂ) := by
      have : ((Complex.log a).re : ℂ) = (Real.log ‖a‖ : ℂ) := by rw [Complex.log_re a]
      rw [this, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr ha)]
    rw [h_re] at h_log
    have h_comm : ((Complex.log a).im : ℂ) * Complex.I = Complex.I * ((Complex.log a).im : ℂ) := by ring
    rw [h_comm] at h_log
    calc
      Complex.exp (Complex.I * ↑(Complex.log a).im) = (‖a‖ : ℂ)⁻¹ * ((‖a‖ : ℂ) * Complex.exp (Complex.I * ↑(Complex.log a).im)) := by
        rw [← mul_assoc, inv_mul_cancel₀, one_mul]
        intro h_zero
        have : ‖a‖ = 0 := by exact_mod_cast h_zero
        exact ha (norm_eq_zero.mp this)
      _ = (‖a‖ : ℂ)⁻¹ * a := by rw [h_log]
      _ = a * (‖a‖ : ℂ)⁻¹ := by ring
  rw [H2]
  have H3 : (a * (‖a‖ : ℂ)⁻¹) * (a * (‖a‖ : ℂ)⁻¹) = a * (star a)⁻¹ := calc
    (a * (‖a‖ : ℂ)⁻¹) * (a * (‖a‖ : ℂ)⁻¹) = a * a * ((‖a‖ : ℂ)⁻¹ * (‖a‖ : ℂ)⁻¹) := by ring
    _ = a * a * ((‖a‖ : ℂ) * (‖a‖ : ℂ))⁻¹ := by rw [mul_inv]
    _ = a * a * (Complex.normSq a : ℂ)⁻¹ := by
      have : (‖a‖ : ℂ) * (‖a‖ : ℂ) = (Complex.normSq a : ℂ) := calc
        (‖a‖ : ℂ) * (‖a‖ : ℂ) = (‖a‖ : ℂ) ^ 2 := by ring
        _ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by norm_cast
        _ = (Complex.normSq a : ℂ) := by rw [Complex.sq_norm a]
      rw [this]
    _ = a * a * (a * star a)⁻¹ := by
      have : (Complex.normSq a : ℂ) = a * star a := Complex.mul_conj a |>.symm
      rw [this]
    _ = a * a * (a⁻¹ * (star a)⁻¹) := by rw [mul_inv]
    _ = a * (a * a⁻¹) * (star a)⁻¹ := by ring
    _ = a * 1 * (star a)⁻¹ := by rw [mul_inv_cancel₀ ha]
    _ = a * (star a)⁻¹ := by ring
  exact H3

lemma exp_two_im_log_neg (a : ℂ) (ha : a ≠ 0) :
    NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := by
  rw [← Complex.exp_eq_exp_ℂ, neg_mul, neg_mul, Complex.exp_neg]
  have : Complex.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := by
    have : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
    rwa [← Complex.exp_eq_exp_ℂ] at this
  rw [this, mul_inv, inv_inv]

lemma spinorPhi_S_matrix_to_M_diag_eq_0_0 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 0 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 0 0 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_0]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 0 0 = _
  rw [spinorPhi_matrix_diag_col_0 a ha 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_0_1 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 0 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 0 1 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_1]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 0 1 = _
  rw [spinorPhi_matrix_diag_col_1 a ha 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_0_2 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 0 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 0 2 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_2]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 0 2 = _
  rw [spinorPhi_matrix_diag_col_2 a ha 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_0_3 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 0 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 0 3 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_3]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 0 3 = _
  rw [spinorPhi_matrix_diag_col_3 a ha 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_1_0 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 1 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 1 0 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_0]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 1 0 = _
  rw [spinorPhi_matrix_diag_col_0 a ha 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_1_1 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 1 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 1 1 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_1]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 1 1 = _
  rw [spinorPhi_matrix_diag_col_1 a ha 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_1_2 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 1 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 1 2 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_2]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 1 2 = _
  rw [spinorPhi_matrix_diag_col_2 a ha 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_1_3 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 1 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 1 3 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_3]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 1 3 = _
  rw [spinorPhi_matrix_diag_col_3 a ha 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_2_0 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 2 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 2 0 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_0]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 2 0 = _
  rw [spinorPhi_matrix_diag_col_0 a ha 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_2_1 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 2 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 2 1 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_1]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 2 1 = _
  rw [spinorPhi_matrix_diag_col_1 a ha 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_2_2 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 2 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 2 2 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_2]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 2 2 = _
  rw [spinorPhi_matrix_diag_col_2 a ha 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_2_3 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 2 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 2 3 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_3]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 2 3 = _
  rw [spinorPhi_matrix_diag_col_3 a ha 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_3_0 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 3 0 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 3 0 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_0]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 3 0 = _
  rw [spinorPhi_matrix_diag_col_0 a ha 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_3_1 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 3 1 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 3 1 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_1]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 3 1 = _
  rw [spinorPhi_matrix_diag_col_1 a ha 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_3_2 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 3 2 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 3 2 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_2]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 3 2 = _
  rw [spinorPhi_matrix_diag_col_2 a ha 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_eq_3_3 (a : ℂ) (ha : a ≠ 0) :
    (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val 3 3 = (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (M_D a) (fun x => (x : ℂ)))) 3 3 := by
  have h_exp_re : NormedSpace.exp (2 * ((Complex.log a).re : ℂ)) = a * star a := exp_two_re_log a ha
  have h_exp_re_neg : NormedSpace.exp (-2 * ((Complex.log a).re : ℂ)) = (a * star a)⁻¹ := exp_two_re_log_neg a ha
  have h_exp_im : NormedSpace.exp (2 * Complex.I * ((Complex.log a).im : ℂ)) = a * (star a)⁻¹ := exp_two_im_log a ha
  have h_exp_im_neg : NormedSpace.exp (-2 * Complex.I * ((Complex.log a).im : ℂ)) = a⁻¹ * star a := exp_two_im_log_neg a ha
  dsimp [M_D]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_3]
  change spinorPhi_matrix (diag_matrix a ha) ((sl2c_conj (diag_matrix a ha))⁻¹) 3 3 = _
  rw [spinorPhi_matrix_diag_col_3 a ha 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try rw [show Complex.I * ↑(Complex.log a).im * 2 = 2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show -(Complex.I * ↑(Complex.log a).im * 2) = -2 * Complex.I * ↑(Complex.log a).im by ring]
  try rw [show ↑(Complex.log a).re * 2 = 2 * ↑(Complex.log a).re by ring]
  try rw [show -(↑(Complex.log a).re * 2) = -2 * ↑(Complex.log a).re by ring]
  try rw [h_exp_re]
  try rw [h_exp_re_neg]
  try rw [h_exp_im]
  try rw [h_exp_im_neg]
  try push_cast
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag (a : ℂ) (ha : a ≠ 0) :
    ∃ (M : Matrix (Fin 4) (Fin 4) ℝ),
      Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0 ∧
      (spinorPhi (diag_matrix a ha, (sl2c_conj (diag_matrix a ha))⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map M (fun x => (x : ℂ))) := by
  use M_D a
  constructor
  · exact M_D_lorentz a
  · ext i j
    fin_cases i <;> fin_cases j
    · exact spinorPhi_S_matrix_to_M_diag_eq_0_0 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_0_1 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_0_2 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_0_3 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_1_0 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_1_1 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_1_2 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_1_3 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_2_0 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_2_1 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_2_2 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_2_3 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_3_0 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_3_1 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_3_2 a ha
    · exact spinorPhi_S_matrix_to_M_diag_eq_3_3 a ha

lemma spinorPhi_is_real (P : SpecialLinearGroup (Fin 2) ℂ) :
  ∃ L : Matrix (Fin 4) (Fin 4) ℝ, (spinorPhi (P, sl2c_conj P)).val.val = Matrix.map L (fun x => (x : ℂ)) := by
  let L : Matrix (Fin 4) (Fin 4) ℝ := fun i j => ((spinorPhi (P, sl2c_conj P)).val.val i j).re
  use L
  ext i j
  change ((spinorPhi (P, sl2c_conj P)).val.val i j) = (L i j : ℂ)
  have h_im : ((spinorPhi (P, sl2c_conj P)).val.val i j).im = 0 := by
    change (spinorPhi_matrix P (sl2c_conj P) i j).im = 0
    apply spinorPhi_matrix_im_zero P (sl2c_conj P)
    rfl
  have h_re : ((spinorPhi (P, sl2c_conj P)).val.val i j).re = L i j := rfl
  exact Complex.ext h_re.symm h_im


lemma exp_conj_complex (L M : Matrix (Fin 4) (Fin 4) ℝ) (L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L * L_inv = 1) (hL2 : L_inv * L = 1) :
    NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (L * M * L_inv) (fun x => (x : ℂ))) =
    Matrix.map L (fun x => (x : ℂ)) * NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map M (fun x => (x : ℂ))) * Matrix.map L_inv (fun x => (x : ℂ)) := by
  let f : ℝ →+* ℂ := algebraMap ℝ ℂ
  let L_C : Matrix (Fin 4) (Fin 4) ℂ := Matrix.map L f
  let M_C : Matrix (Fin 4) (Fin 4) ℂ := Matrix.map M f
  let L_inv_C : Matrix (Fin 4) (Fin 4) ℂ := Matrix.map L_inv f
  have h1 : L_C * L_inv_C = 1 := by
    calc
      L_C * L_inv_C = Matrix.map (L * L_inv) f := (Matrix.map_mul (f := f)).symm
      _ = Matrix.map 1 f := by rw [hL]
      _ = 1 := Matrix.map_one f (map_zero _) (map_one _)
  have h2 : L_inv_C * L_C = 1 := by
    calc
      L_inv_C * L_C = Matrix.map (L_inv * L) f := (Matrix.map_mul (f := f)).symm
      _ = Matrix.map 1 f := by rw [hL2]
      _ = 1 := Matrix.map_one f (map_zero _) (map_one _)
  have h_inv : L_C⁻¹ = L_inv_C := Matrix.inv_eq_right_inv h1
  have h_unit : IsUnit L_C := ⟨⟨L_C, L_inv_C, h1, h2⟩, rfl⟩
  have h_map : Matrix.map (L * M * L_inv) (fun x => (x : ℂ)) = L_C * M_C * L_inv_C := by
    change Matrix.map ((L * M) * L_inv) f = L_C * M_C * L_inv_C
    calc
      Matrix.map ((L * M) * L_inv) f = Matrix.map (L * M) f * L_inv_C := Matrix.map_mul (f := f)
      _ = (L_C * M_C) * L_inv_C := by rw [Matrix.map_mul (f := f)]
      _ = L_C * M_C * L_inv_C := by rfl
  have h_smul : ((2 * Complex.I) : ℂ) • (L_C * M_C * L_inv_C) = L_C * (((2 * Complex.I) : ℂ) • M_C) * L_inv_C := by
    have h_assoc1 : ((2 * Complex.I) : ℂ) • ((L_C * M_C) * L_inv_C) = (((2 * Complex.I) : ℂ) • (L_C * M_C)) * L_inv_C := (smul_mul_assoc _ _ _).symm
    change ((2 * Complex.I) : ℂ) • ((L_C * M_C) * L_inv_C) = (L_C * (((2 * Complex.I) : ℂ) • M_C)) * L_inv_C
    rw [h_assoc1]
    have h_comm : ((2 * Complex.I) : ℂ) • (L_C * M_C) = L_C * ((2 * Complex.I) : ℂ) • M_C := (mul_smul_comm _ _ _).symm
    rw [h_comm]
  rw [h_map, h_smul]
  have h_exp := exp_conj_matrix L_C (((2 * Complex.I) : ℂ) • M_C) L_inv_C h1 h2
  change NormedSpace.exp (L_C * ((2 * Complex.I) • M_C) * L_inv_C) = L_C * NormedSpace.exp ((2 * Complex.I) • M_C) * L_inv_C
  exact h_exp

lemma spinorPhi_one : (spinorPhi (1, 1)).val.val = 1 := by
  have h := MonoidHom.map_one spinorPhi
  change (spinorPhi 1).val.val = 1
  rw [h]
  rfl

lemma spinorPhi_neg_one (ε : ℂ) (hε : ε = -1) :
    (spinorPhi (diag_matrix ε (by simp [hε]), (sl2c_conj (diag_matrix ε (by simp [hε])))⁻¹)).val.val = 1 := by
  subst hε
  have h_left : (diag_matrix (-1) (by norm_num), (sl2c_conj (diag_matrix (-1) (by norm_num)))⁻¹) = (diag_matrix (-1) (by norm_num), diag_matrix (-1) (by norm_num)) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i j
      have h_mul : diag_matrix (-1) (by norm_num) * diag_matrix (-1) (by norm_num) = (1 : SpecialLinearGroup (Fin 2) ℂ) := by
        apply Subtype.ext
        ext a b
        fin_cases a <;> fin_cases b <;> simp [diag_matrix, Matrix.mul_apply, Fin.sum_univ_two]
      have h_inv2 : (diag_matrix (-1) (by norm_num))⁻¹ = diag_matrix (-1) (by norm_num) := by
        exact inv_eq_of_mul_eq_one_right h_mul
      have h_conj : sl2c_conj (diag_matrix (-1) (by norm_num)) = diag_matrix (-1) (by norm_num) := by
        apply Subtype.ext
        ext a b
        fin_cases a <;> fin_cases b <;> simp [sl2c_conj, diag_matrix]
      rw [h_conj, h_inv2]
  rw [h_left]
  have h_eq : spinor_action_linear (diag_matrix (-1) (by norm_num)) (diag_matrix (-1) (by norm_num)) = spinor_action_linear 1 1 := by
    ext X i j
    have hd : (diag_matrix (-1) (by norm_num) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [diag_matrix]
    simp [spinor_action_linear, spinor_action, hd, Matrix.transpose_neg, Matrix.transpose_one]
  change spinorPhi_matrix _ _ = 1
  unfold spinorPhi_matrix
  rw [h_eq]
  change (spinorPhi (1, 1)).val.val = 1
  exact spinorPhi_one

lemma spinorPhi_S_matrix_to_M_aux_a :
    minkowskiMetric = Matrix.map minkowskiMetricReal (fun x => (x : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiMetric, minkowskiMetricReal]

lemma ofReal_inj_matrix {n m : Type*} [Fintype n] [Fintype m] {A B : Matrix n m ℝ}
    (h : Matrix.map A (fun x => (x : ℂ)) = Matrix.map B (fun x => (x : ℂ))) : A = B := by
  ext i j
  have hij := congr_fun (congr_fun h i) j
  exact Complex.ofReal_inj.mp hij

lemma spinorPhi_S_matrix_to_M_aux_b (P : SpecialLinearGroup (Fin 2) ℂ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P, sl2c_conj P)).val.val = Matrix.map L (fun x => (x : ℂ))) :
    Lᵀ * minkowskiMetricReal * L = minkowskiMetricReal := by
  have h_lorentz := (spinorPhi (P, sl2c_conj P)).2.1
  rw [hL, spinorPhi_S_matrix_to_M_aux_a] at h_lorentz
  have h_map1 : (Matrix.map L (fun x => (x : ℂ)))ᵀ = Matrix.map Lᵀ (fun x => (x : ℂ)) := rfl
  rw [h_map1] at h_lorentz
  have h_map2 : Matrix.map Lᵀ (fun x => (x : ℂ)) * Matrix.map minkowskiMetricReal (fun x => (x : ℂ)) =
                Matrix.map (Lᵀ * minkowskiMetricReal) (fun x => (x : ℂ)) := by
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm
  rw [h_map2] at h_lorentz
  have h_map3 : Matrix.map (Lᵀ * minkowskiMetricReal) (fun x => (x : ℂ)) * Matrix.map L (fun x => (x : ℂ)) =
                Matrix.map (Lᵀ * minkowskiMetricReal * L) (fun x => (x : ℂ)) := by
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm
  rw [h_map3] at h_lorentz
  exact ofReal_inj_matrix h_lorentz

lemma spinorPhi_S_matrix_to_M_aux_c (P : SpecialLinearGroup (Fin 2) ℂ)
    (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : (spinorPhi (P, sl2c_conj P)).val.val = Matrix.map L (fun x => (x : ℂ)))
    (L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL_inv : (spinorPhi (P⁻¹, sl2c_conj P⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ))) :
    L * L_inv = 1 ∧ L_inv * L = 1 := by
  have h_mul := spinorPhi_matrix_mul P (sl2c_conj P) P⁻¹ (sl2c_conj P⁻¹)
  have h_P_mul : P * P⁻¹ = 1 := mul_inv_cancel P
  have h_conj_mul : sl2c_conj P * sl2c_conj (P⁻¹) = 1 := by
    rw [← sl2c_conj_mul, h_P_mul, sl2c_conj_one]
  rw [h_P_mul, h_conj_mul] at h_mul
  have h_one : (spinorPhi (1, 1)).val.val = 1 := spinorPhi_one
  change (spinorPhi (1, 1)).val.val = _ at h_mul
  rw [h_one] at h_mul
  change 1 = spinorPhi_matrix P (sl2c_conj P) * spinorPhi_matrix (P⁻¹) (sl2c_conj (P⁻¹)) at h_mul
  have hs1 : spinorPhi_matrix P (sl2c_conj P) = Matrix.map L (fun x => (x : ℂ)) := hL
  have hs2 : spinorPhi_matrix (P⁻¹) (sl2c_conj (P⁻¹)) = Matrix.map L_inv (fun x => (x : ℂ)) := hL_inv
  rw [hs1, hs2] at h_mul
  have h_map : Matrix.map L (fun x => (x : ℂ)) * Matrix.map L_inv (fun x => (x : ℂ)) = Matrix.map (L * L_inv) (fun x => (x : ℂ)) := by
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm
  rw [h_map] at h_mul
  have h_one_map : (1 : Matrix (Fin 4) (Fin 4) ℂ) = Matrix.map (1 : Matrix (Fin 4) (Fin 4) ℝ) (fun x => (x : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h_one_map] at h_mul
  have h1 := ofReal_inj_matrix h_mul

  have h_mul2 := spinorPhi_matrix_mul P⁻¹ (sl2c_conj P⁻¹) P (sl2c_conj P)
  have h_P_mul2 : P⁻¹ * P = 1 := inv_mul_cancel P
  have h_conj_mul2 : sl2c_conj (P⁻¹) * sl2c_conj P = 1 := by
    rw [← sl2c_conj_mul, h_P_mul2, sl2c_conj_one]
  rw [h_P_mul2, h_conj_mul2] at h_mul2
  change (spinorPhi (1, 1)).val.val = _ at h_mul2
  rw [h_one] at h_mul2
  change 1 = spinorPhi_matrix (P⁻¹) (sl2c_conj (P⁻¹)) * spinorPhi_matrix P (sl2c_conj P) at h_mul2
  rw [hs2, hs1] at h_mul2
  have h_map2 : Matrix.map L_inv (fun x => (x : ℂ)) * Matrix.map L (fun x => (x : ℂ)) = Matrix.map (L_inv * L) (fun x => (x : ℂ)) := by
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ)).symm
  rw [h_map2] at h_mul2
  rw [h_one_map] at h_mul2
  have h2 := ofReal_inj_matrix h_mul2
  exact ⟨h1.symm, h2.symm⟩

lemma spinorPhi_S_matrix_to_M_aux_d (M L L_inv : Matrix (Fin 4) (Fin 4) ℝ)
    (hL_lorentz : Lᵀ * minkowskiMetricReal * L = minkowskiMetricReal)
    (hL1 : L * L_inv = 1) (hL2 : L_inv * L = 1)
    (hM : Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0) :
    (L * M * L_inv)ᵀ * minkowskiMetricReal + minkowskiMetricReal * (L * M * L_inv) = 0 := by
  have H1 : (L * M * L_inv)ᵀ = L_invᵀ * Mᵀ * Lᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [H1]
  have h_eta_L : minkowskiMetricReal * L = (L_inv)ᵀ * minkowskiMetricReal := by
    calc minkowskiMetricReal * L = (L_inv)ᵀ * Lᵀ * minkowskiMetricReal * L := by
          have h_inv_T : L_invᵀ * Lᵀ = 1 := by
            rw [← Matrix.transpose_mul, hL1, Matrix.transpose_one]
          rw [h_inv_T, Matrix.one_mul]
      _ = (L_inv)ᵀ * (Lᵀ * minkowskiMetricReal * L) := by
          repeat rw [Matrix.mul_assoc]
      _ = (L_inv)ᵀ * minkowskiMetricReal := by
          rw [hL_lorentz]
  have h_eta_L_inv : minkowskiMetricReal * L_inv = Lᵀ * minkowskiMetricReal := by
    calc minkowskiMetricReal * L_inv = Lᵀ * minkowskiMetricReal * L * L_inv := by
          rw [hL_lorentz]
      _ = Lᵀ * minkowskiMetricReal * (L * L_inv) := by
          repeat rw [Matrix.mul_assoc]
      _ = Lᵀ * minkowskiMetricReal := by
          rw [hL1, Matrix.mul_one]
  have h_L_T_eta : Lᵀ * minkowskiMetricReal = minkowskiMetricReal * L_inv := h_eta_L_inv.symm
  calc L_invᵀ * Mᵀ * Lᵀ * minkowskiMetricReal + minkowskiMetricReal * (L * M * L_inv)
    _ = L_invᵀ * Mᵀ * (Lᵀ * minkowskiMetricReal) + minkowskiMetricReal * L * M * L_inv := by
        repeat rw [Matrix.mul_assoc]
    _ = L_invᵀ * Mᵀ * (minkowskiMetricReal * L_inv) + (L_invᵀ * minkowskiMetricReal) * M * L_inv := by
        rw [h_L_T_eta, h_eta_L]
    _ = L_invᵀ * (Mᵀ * minkowskiMetricReal) * L_inv + L_invᵀ * (minkowskiMetricReal * M) * L_inv := by
        repeat rw [Matrix.mul_assoc]
    _ = L_invᵀ * (Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M) * L_inv := by
        rw [← Matrix.add_mul, ← Matrix.mul_add]
    _ = L_invᵀ * 0 * L_inv := by rw [hM]
    _ = 0 := by simp

lemma spinorPhi_S_matrix_to_M_aux_e (C P D : SpecialLinearGroup (Fin 2) ℂ)
    (hC : C = P * D * P⁻¹) :
    (spinorPhi (C, (sl2c_conj C)⁻¹)).val.val =
    (spinorPhi (P, sl2c_conj P)).val.val *
    (spinorPhi (D, (sl2c_conj D)⁻¹)).val.val *
    (spinorPhi (P⁻¹, sl2c_conj (P⁻¹))).val.val := by
  have hc1 : (sl2c_conj C)⁻¹ = sl2c_conj P * (sl2c_conj D)⁻¹ * sl2c_conj (P⁻¹) := by
    rw [hC]
    repeat rw [sl2c_conj_mul]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, sl2c_conj_inv, inv_inv]
    rw [mul_assoc]
  have h_left : (C, (sl2c_conj C)⁻¹) =
                (P * D * P⁻¹, sl2c_conj P * (sl2c_conj D)⁻¹ * sl2c_conj (P⁻¹)) := by
    rw [hc1, hC]
  rw [h_left]
  have h_mul1 := spinorPhi_matrix_mul (P * D) (sl2c_conj P * (sl2c_conj D)⁻¹) P⁻¹ (sl2c_conj P⁻¹)
  have h_mul2 := spinorPhi_matrix_mul P (sl2c_conj P) D (sl2c_conj D)⁻¹
  have h_mul3 : (spinorPhi (P * D * P⁻¹, sl2c_conj P * (sl2c_conj D)⁻¹ * sl2c_conj (P⁻¹))).val.val =
      (spinorPhi (P * D, sl2c_conj P * (sl2c_conj D)⁻¹)).val.val * (spinorPhi (P⁻¹, sl2c_conj P⁻¹)).val.val := h_mul1
  rw [h_mul3]
  have h_mul4 : (spinorPhi (P * D, sl2c_conj P * (sl2c_conj D)⁻¹)).val.val =
      (spinorPhi (P, sl2c_conj P)).val.val * (spinorPhi (D, (sl2c_conj D)⁻¹)).val.val := h_mul2
  rw [h_mul4]
  repeat rw [Matrix.mul_assoc]

lemma spinorPhi_S_matrix_to_M_aux_f (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    (spinorPhi (diag_matrix ε (by rcases hε with h | h <;> simp [h]),
     (sl2c_conj (diag_matrix ε (by rcases hε with h | h <;> simp [h])))⁻¹)).val.val = 1 := by
  rcases hε with rfl | rfl
  · have h2 : (sl2c_conj (diag_matrix 1 (by norm_num)))⁻¹ = 1 := by
      apply Subtype.ext
      have h_conj : sl2c_conj (diag_matrix 1 (by norm_num)) = 1 := by
        apply Subtype.ext
        ext a b
        fin_cases a <;> fin_cases b <;> simp [sl2c_conj, diag_matrix]
      rw [h_conj, inv_one]
    have h_left : (diag_matrix 1 (by norm_num), (sl2c_conj (diag_matrix 1 (by norm_num)))⁻¹) = (1, 1) := by
      apply Prod.ext
      · apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diag_matrix]
      · exact h2
    rw [h_left]
    exact spinorPhi_one
  · exact spinorPhi_neg_one (-1) rfl



lemma matrix_mul_two_two (a b c d l m n o : ℂ) :
  Matrix.of ![![a, b], ![c, d]] * Matrix.of ![![l, m], ![n, o]] =
  Matrix.of ![![a * l + b * n, a * m + b * o], ![c * l + d * n, c * m + d * o]] := by
  ext i j
  match i, j with
  | 0, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero]
  | 0, 1 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  | 1, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  | 1, 1 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma c_ne_zero_jordan_mul_00 (a b c d l : ℂ) (h_tr : a + d - 2 * l = 0) (h_det : a * d - b * c - 1 = 0) (h_l : l * l - 1 = 0) :
  a * (l - d) + b * c = (l - d) * l + 1 * 0 := by linear_combination l * h_tr - h_det + h_l

lemma c_ne_zero_jordan_mul_01 (a b c d l : ℂ) (h_tr : a + d - 2 * l = 0) :
  a * 1 + b * 0 = (l - d) * 1 + 1 * l := by linear_combination h_tr

lemma c_ne_zero_jordan_mul_10 (a b c d l : ℂ) :
  c * (l - d) + d * c = c * l + 0 * 0 := by ring

lemma c_ne_zero_jordan_mul_11 (a b c d l : ℂ) :
  c * 1 + d * 0 = c * 1 + 0 * l := by ring

lemma c_ne_zero_jordan_mul (a b c d l : ℂ) (h_tr : a + d - 2 * l = 0) (h_det : a * d - b * c - 1 = 0) (h_l : l * l - 1 = 0) :
  Matrix.of ![![a, b], ![c, d]] * Matrix.of ![![l - d, 1], ![c, 0]] =
  Matrix.of ![![l - d, 1], ![c, 0]] * Matrix.of ![![l, 1], ![0, l]] := by
  rw [matrix_mul_two_two, matrix_mul_two_two]
  ext i j
  match i, j with
  | 0, 0 => exact c_ne_zero_jordan_mul_00 a b c d l h_tr h_det h_l
  | 0, 1 => exact c_ne_zero_jordan_mul_01 a b c d l h_tr
  | 1, 0 => exact c_ne_zero_jordan_mul_10 a b c d l
  | 1, 1 => exact c_ne_zero_jordan_mul_11 a b c d l

lemma c_ne_zero_diag_mul_00 (a b c d l m : ℂ) (h_tr : a + d - (l + m) = 0) (h_det : a * d - b * c - 1 = 0) (h_lm : l * m - 1 = 0) :
  a * (l - d) + b * c = (l - d) * l + (m - d) * 0 := by linear_combination l * h_tr - h_det + h_lm

lemma c_ne_zero_diag_mul_01 (a b c d l m : ℂ) (h_tr : a + d - (l + m) = 0) (h_det : a * d - b * c - 1 = 0) (h_lm : l * m - 1 = 0) :
  a * (m - d) + b * c = (l - d) * 0 + (m - d) * m := by linear_combination m * h_tr - h_det + h_lm

lemma c_ne_zero_diag_mul_10 (a b c d l m : ℂ) :
  c * (l - d) + d * c = c * l + c * 0 := by ring

lemma c_ne_zero_diag_mul_11 (a b c d l m : ℂ) :
  c * (m - d) + d * c = c * 0 + c * m := by ring

lemma c_ne_zero_diag_mul (a b c d l m : ℂ) (h_tr : a + d - (l + m) = 0) (h_det : a * d - b * c - 1 = 0) (h_lm : l * m - 1 = 0) :
  Matrix.of ![![a, b], ![c, d]] * Matrix.of ![![l - d, m - d], ![c, c]] =
  Matrix.of ![![l - d, m - d], ![c, c]] * Matrix.of ![![l, 0], ![0, m]] := by
  rw [matrix_mul_two_two, matrix_mul_two_two]
  ext i j
  match i, j with
  | 0, 0 => exact c_ne_zero_diag_mul_00 a b c d l m h_tr h_det h_lm
  | 0, 1 => exact c_ne_zero_diag_mul_01 a b c d l m h_tr h_det h_lm
  | 1, 0 => exact c_ne_zero_diag_mul_10 a b c d l m
  | 1, 1 => exact c_ne_zero_diag_mul_11 a b c d l m

lemma c_eq_zero_jordan_mul_00 (a b l : ℂ) (h_tr : a + a - 2 * l = 0) :
  a * 1 + b * 0 = 1 * l + 0 * 0 := by linear_combination h_tr / 2

lemma c_eq_zero_jordan_mul_01 (a b l : ℂ) (h_tr : a + a - 2 * l = 0) (h_l : l * l - 1 = 0) :
  a * 0 + b * 1 = 1 * (b * (l / a)) + 0 * l := by
  have ha : a = l := by linear_combination h_tr / 2
  rw [ha, div_self, mul_one]
  ring
  intro hl
  rw [hl] at h_l
  revert h_l
  norm_num

lemma c_eq_zero_jordan_mul_10 (a b l : ℂ) :
  0 * 1 + a * 0 = 0 * l + 1 * 0 := by ring

lemma c_eq_zero_jordan_mul_11 (a b l : ℂ) (h_tr : a + a - 2 * l = 0) :
  0 * 0 + a * 1 = 0 * (b * (l / a)) + 1 * l := by linear_combination h_tr / 2

lemma c_eq_zero_jordan_mul (a b l : ℂ) (h_tr : a + a - 2 * l = 0) (h_l : l * l - 1 = 0) :
  Matrix.of ![![a, b], ![0, a]] * Matrix.of ![![1, 0], ![0, 1]] =
  Matrix.of ![![1, 0], ![0, 1]] * Matrix.of ![![l, b * (l / a)], ![0, l]] := by
  rw [matrix_mul_two_two, matrix_mul_two_two]
  ext i j
  match i, j with
  | 0, 0 => exact c_eq_zero_jordan_mul_00 a b l h_tr
  | 0, 1 => exact c_eq_zero_jordan_mul_01 a b l h_tr h_l
  | 1, 0 => exact c_eq_zero_jordan_mul_10 a b l
  | 1, 1 => exact c_eq_zero_jordan_mul_11 a b l h_tr

lemma c_eq_zero_diag_mul_00 (a b d : ℂ) :
  a * 1 + b * 0 = 1 * a + (-b / (a - d)) * 0 := by ring

lemma c_eq_zero_diag_mul_01 (a b d : ℂ) (h_ad : a ≠ d) :
  a * (-b / (a - d)) + b * 1 = 1 * 0 + (-b / (a - d)) * d := by
  have had2 : a - d ≠ 0 := sub_ne_zero.mpr h_ad
  apply mul_left_cancel₀ had2
  calc
    (a - d) * (a * (-b / (a - d)) + b * 1) = a * (-b / (a - d) * (a - d)) + b * (a - d) := by ring
    _ = a * -b + b * (a - d) := by rw [div_mul_cancel₀ _ had2]
    _ = -b * d := by ring
    _ = (-b / (a - d) * (a - d)) * d := by rw [div_mul_cancel₀ _ had2]
    _ = (a - d) * (1 * 0 + (-b / (a - d)) * d) := by ring

lemma c_eq_zero_diag_mul_10 (a b d : ℂ) :
  0 * 1 + d * 0 = 0 * a + 1 * 0 := by ring

lemma c_eq_zero_diag_mul_11 (a b d : ℂ) :
  0 * (-b / (a - d)) + d * 1 = 0 * 0 + 1 * d := by ring

lemma c_eq_zero_diag_mul (a b d : ℂ) (h_det : a * d - 1 = 0) (h_ad : a ≠ d) :
  Matrix.of ![![a, b], ![0, d]] * Matrix.of ![![1, -b / (a - d)], ![0, 1]] =
  Matrix.of ![![1, -b / (a - d)], ![0, 1]] * Matrix.of ![![a, 0], ![0, d]] := by
  rw [matrix_mul_two_two, matrix_mul_two_two]
  ext i j
  match i, j with
  | 0, 0 => exact c_eq_zero_diag_mul_00 a b d
  | 0, 1 => exact c_eq_zero_diag_mul_01 a b d h_ad
  | 1, 0 => exact c_eq_zero_diag_mul_10 a b d
  | 1, 1 => exact c_eq_zero_diag_mul_11 a b d

lemma exists_scaled_sl2c (P₀ : Matrix (Fin 2) (Fin 2) ℂ) (h : P₀.det ≠ 0) :
  ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (k : ℂ), (P : Matrix (Fin 2) (Fin 2) ℂ) = k • P₀ ∧ k ≠ 0 := by
  have h_inv : 1 / P₀.det ≠ 0 := by
    intro h0
    exact one_ne_zero ((div_eq_zero_iff.mp h0).resolve_right h)
  rcases Geometry.complex_exists_sq_of_ne_zero h_inv with ⟨k, hk, hk_ne⟩
  have h_det : (k • P₀).det = 1 := by
    calc
      (k • P₀).det = k ^ 2 * P₀.det := by exact Matrix.det_smul P₀ k
      _ = (1 / P₀.det) * P₀.det := by rw [hk]
      _ = 1 := div_mul_cancel₀ 1 h
  use ⟨k • P₀, h_det⟩, k, rfl, hk_ne

lemma sl2c_conj_lift (C P J : SpecialLinearGroup (Fin 2) ℂ)
  (h : C.val * P.val = P.val * J.val) : C = P * J * P⁻¹ := by
  apply Subtype.ext
  have h_inv : P⁻¹.val = P.val⁻¹ := by
    change (adjugate P.val) = P.val⁻¹
    have h_mul : P.val * adjugate P.val = 1 := by
      rw [Matrix.mul_adjugate P.val, P.prop, one_smul]
    exact Eq.symm (Matrix.inv_eq_right_inv h_mul)
  change C.val = P.val * J.val * P⁻¹.val
  have hdet_is_unit : IsUnit P.val.det := by rw [P.prop]; exact isUnit_one
  calc
    C.val = C.val * (P.val * P.val⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet_is_unit, Matrix.mul_one]
    _ = (C.val * P.val) * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P.val * J.val) * P.val⁻¹ := by rw [h]
    _ = P.val * J.val * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P.val * J.val * P⁻¹.val := by rw [←h_inv]

lemma mul_smul_comm_matrix (C P₀ J : Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ) (h : C * P₀ = P₀ * J) :
  C * (k • P₀) = (k • P₀) * J := by
  rw [Matrix.mul_smul, h, Matrix.smul_mul]

lemma diag_eq_diag_matrix (l m : ℂ) (hl : l ≠ 0) (hlm : l * m = 1) :
  Matrix.of ![![l, 0], ![0, m]] = (diag_matrix l hl).val := by
  have hm : m = l⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_comm, hlm]
  change Matrix.of ![![l, 0], ![0, m]] = Matrix.of ![![l, 0], ![0, l⁻¹]]
  rw [hm]

lemma jordan_eq_diag_mul_jordan (l x : ℂ) (hl : l ≠ 0) (hl2 : l * l = 1) :
  Matrix.of ![![l, x], ![0, l]] = (diag_matrix l hl * jordan_matrix (l⁻¹ * x)).val := by
  have hl_inv : l⁻¹ = l := by
    calc
      l⁻¹ = l⁻¹ * 1 := by rw [mul_one]
      _ = l⁻¹ * (l * l) := by rw [←hl2]
      _ = (l⁻¹ * l) * l := by rw [←mul_assoc]
      _ = 1 * l := by rw [inv_mul_cancel₀ hl]
      _ = l := by rw [one_mul]
  change Matrix.of ![![l, x], ![0, l]] = Matrix.of ![![l, 0], ![0, l⁻¹]] * Matrix.of ![![1, l⁻¹ * x], ![0, 1]]
  ext i j
  match i, j with
  | 0, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero]
  | 0, 1 =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [←mul_assoc, mul_inv_cancel₀ hl, one_mul]
  | 1, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  | 1, 1 =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hl_inv]

lemma exists_roots_of_tr (tr : ℂ) : ∃ (l m : ℂ), l + m = tr ∧ l * m = 1 := by
  rcases Geometry.complex_exists_sq (tr ^ 2 - 4) with ⟨s, hs⟩
  use (tr + s) / 2, (tr - s) / 2
  constructor
  · ring
  · calc
      (tr + s) / 2 * ((tr - s) / 2) = (tr ^ 2 - s ^ 2) / 4 := by ring
      _ = (tr ^ 2 - (tr ^ 2 - 4)) / 4 := by rw [hs]
      _ = 4 / 4 := by ring
      _ = 1 := by norm_num

lemma sl2c_c_eq_zero_jordan (a b d : ℂ) (h_det : a * d - b * 0 = 1) (had : a = d) :
  ∃ ε, ∃ (hε : ε = 1 ∨ ε = -1), ∃ c,
  Matrix.of ![![a, b], ![0, d]] =
    (1 : SpecialLinearGroup (Fin 2) ℂ).val * ((diag_matrix ε (by rcases hε with h | h <;> simp [h])).val * (jordan_matrix c).val) * (1 : SpecialLinearGroup (Fin 2) ℂ)⁻¹.val := by
  have ha2 : a * a = 1 := by
    calc a * a = a * d := by rw [had]
    _ = a * d - b * 0 := by ring
    _ = 1 := h_det
  have ha_sign : a = 1 ∨ a = -1 := by
    have h_sq : a ^ 2 - 1 = 0 := by
      calc a ^ 2 - 1 = a * a - 1 := by ring
      _ = 1 - 1 := by rw [ha2]
      _ = 0 := by ring
    have h_fac : (a - 1) * (a + 1) = 0 := by
      calc (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = 0 := h_sq
    cases mul_eq_zero.mp h_fac with
    | inl h1 => left; exact eq_of_sub_eq_zero h1
    | inr h2 => right; exact eq_neg_of_add_eq_zero_left h2
  have ha_ne_zero : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at ha2
    norm_num at ha2
  have ha_inv : a⁻¹ = a := by
    calc
      a⁻¹ = a⁻¹ * 1 := by rw [mul_one]
      _ = a⁻¹ * (a * a) := by rw [←ha2]
      _ = (a⁻¹ * a) * a := by rw [←mul_assoc]
      _ = 1 * a := by rw [inv_mul_cancel₀ ha_ne_zero]
      _ = a := by rw [one_mul]
  use a, ha_sign, b / a
  have h1 : (1 : SpecialLinearGroup (Fin 2) ℂ).val = 1 := rfl
  have hinv : (1 : SpecialLinearGroup (Fin 2) ℂ)⁻¹.val = 1 := by rw [inv_one]; rfl
  rw [h1, hinv, mul_one, one_mul]
  ext i j
  match i, j with
  | 0, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, diag_matrix, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero]
  | 0, 1 =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diag_matrix, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Eq.symm (calc
      a * (b / a) = a * (b * a⁻¹) := rfl
      _ = (a * a⁻¹) * b := by ring
      _ = 1 * b := by rw [mul_inv_cancel₀ ha_ne_zero]
      _ = b := by rw [one_mul])
  | 1, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, diag_matrix, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  | 1, 1 =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diag_matrix, jordan_matrix, J_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [←had]
    exact ha_inv.symm

lemma sl2c_c_eq_zero_diag (a b d : ℂ) (h_det : a * d - b * 0 = 1) (had : a ≠ d) :
  ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (l : ℂ) (hl : l ≠ 0),
  Matrix.of ![![a, b], ![0, d]] =
    P.val * (diag_matrix l hl).val * P⁻¹.val := by
  let P₀ := Matrix.of ![![1, -b / (a - d)], ![0, 1]]
  have hP₀_det : P₀.det = 1 := by
    simp [P₀, Matrix.det_fin_two]
  let P : SpecialLinearGroup (Fin 2) ℂ := ⟨P₀, hP₀_det⟩
  have ha_ne_zero : a ≠ 0 := by
    intro ha0
    have h_det2 : a * d = 1 := by
      calc a * d = a * d - b * 0 := by ring
      _ = 1 := h_det
    rw [ha0, zero_mul] at h_det2
    norm_num at h_det2
  use P, a, ha_ne_zero
  
  have h_conj : Matrix.of ![![a, b], ![0, d]] * P.val = P.val * (diag_matrix a ha_ne_zero).val := by
    have hd_eq : d = a⁻¹ := by
      have h_det2 : a * d = 1 := by
        calc a * d = a * d - b * 0 := by ring
        _ = 1 := h_det
      calc d = 1 * d := by rw [one_mul]
      _ = (a⁻¹ * a) * d := by rw [inv_mul_cancel₀ ha_ne_zero]
      _ = a⁻¹ * (a * d) := by rw [mul_assoc]
      _ = a⁻¹ * 1 := by rw [h_det2]
      _ = a⁻¹ := by rw [mul_one]
    change Matrix.of ![![a, b], ![0, d]] * Matrix.of ![![1, -b / (a - d)], ![0, 1]] =
      Matrix.of ![![1, -b / (a - d)], ![0, 1]] * Matrix.of ![![a, 0], ![0, a⁻¹]]
    ext i j
    match i, j with
    | 0, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero]
    | 0, 1 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      have had2 : a - d ≠ 0 := sub_ne_zero.mpr had
      apply mul_left_cancel₀ had2
      calc
        (a - d) * (a * (-b / (a - d)) + b) = a * (-b / (a - d) * (a - d)) + b * (a - d) := by ring
        _ = a * -b + b * (a - d) := by rw [div_mul_cancel₀ _ had2]
        _ = -b * d := by ring
        _ = (-b / (a - d) * (a - d)) * d := by rw [div_mul_cancel₀ _ had2]
        _ = (a - d) * (-b / (a - d) * d) := by ring
        _ = (a - d) * (-b / (a - d) * a⁻¹) := by rw [hd_eq]
    | 1, 0 => simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    | 1, 1 =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hd_eq]
  have h_inv : P⁻¹.val = P.val⁻¹ := by
    change (adjugate P.val) = P.val⁻¹
    have h_mul : P.val * adjugate P.val = 1 := by
      rw [Matrix.mul_adjugate P.val, P.prop, one_smul]
    exact Eq.symm (Matrix.inv_eq_right_inv h_mul)
  calc
    Matrix.of ![![a, b], ![0, d]] = Matrix.of ![![a, b], ![0, d]] * (P.val * P.val⁻¹) := by
      have hdet_is_unit : IsUnit P.val.det := by rw [P.prop]; exact isUnit_one
      rw [Matrix.mul_nonsing_inv _ hdet_is_unit, Matrix.mul_one]
    _ = (Matrix.of ![![a, b], ![0, d]] * P.val) * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P.val * (diag_matrix a ha_ne_zero).val) * P.val⁻¹ := by rw [h_conj]
    _ = P.val * (diag_matrix a ha_ne_zero).val * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P.val * (diag_matrix a ha_ne_zero).val * P⁻¹.val := by rw [←h_inv]

lemma sl2c_c_ne_zero_jordan (a b c d l : ℂ) (h_det : a * d - b * c = 1) (hc : c ≠ 0) (h_tr : l + l = a + d) (hl2 : l * l = 1) :
  ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (c' : ℂ),
  Matrix.of ![![a, b], ![c, d]] =
    P.val * ((diag_matrix ε (by rcases hε with h | h <;> simp [h])).val * (jordan_matrix c').val) * P⁻¹.val := by
  let P₀ := Matrix.of ![![l - d, 1], ![c, 0]]
  have hP₀_det : P₀.det = -c := by simp [P₀, Matrix.det_fin_two]
  have hP₀_ne_zero : P₀.det ≠ 0 := by
    rw [hP₀_det]
    intro hc0
    exact hc (neg_eq_zero.mp hc0)
  rcases exists_scaled_sl2c P₀ hP₀_ne_zero with ⟨P, k, hP_eq, hk_ne⟩
  have hl_sign : l = 1 ∨ l = -1 := by
    have h_sq : l ^ 2 - 1 = 0 := by
      calc l ^ 2 - 1 = l * l - 1 := by ring
      _ = 1 - 1 := by rw [hl2]
      _ = 0 := by ring
    have h_fac : (l - 1) * (l + 1) = 0 := by
      calc (l - 1) * (l + 1) = l ^ 2 - 1 := by ring
      _ = 0 := h_sq
    cases mul_eq_zero.mp h_fac with
    | inl h1 => left; exact eq_of_sub_eq_zero h1
    | inr h2 => right; exact eq_neg_of_add_eq_zero_left h2
  have hl_ne_zero : l ≠ 0 := by
    intro hl0
    rw [hl0, zero_mul] at hl2
    norm_num at hl2
  use P, l, hl_sign, l⁻¹
  have h_conj : Matrix.of ![![a, b], ![c, d]] * P₀ = P₀ * Matrix.of ![![l, 1], ![0, l]] := by
    have h_tr_sym : a + d - 2 * l = 0 := by linear_combination -h_tr
    have h_det_sym : a * d - b * c - 1 = 0 := by linear_combination h_det
    have hl_sym : l * l - 1 = 0 := by linear_combination hl2
    exact c_ne_zero_jordan_mul a b c d l h_tr_sym h_det_sym hl_sym
  have h_conj2 : Matrix.of ![![a, b], ![c, d]] * P.val = P.val * Matrix.of ![![l, 1], ![0, l]] := by
    rw [hP_eq]
    exact mul_smul_comm_matrix _ _ _ k h_conj
  have h_jordan : Matrix.of ![![l, 1], ![0, l]] = (diag_matrix l hl_ne_zero).val * (jordan_matrix l⁻¹).val := by
    have h1 := jordan_eq_diag_mul_jordan l 1 hl_ne_zero hl2
    rw [mul_one] at h1
    exact h1
  have h_inv : P⁻¹.val = P.val⁻¹ := by
    change (adjugate P.val) = P.val⁻¹
    have h_mul : P.val * adjugate P.val = 1 := by
      rw [Matrix.mul_adjugate P.val, P.prop, one_smul]
    exact Eq.symm (Matrix.inv_eq_right_inv h_mul)
  calc
    Matrix.of ![![a, b], ![c, d]] = Matrix.of ![![a, b], ![c, d]] * (P.val * P.val⁻¹) := by
      have hdet_is_unit : IsUnit P.val.det := by rw [P.prop]; exact isUnit_one
      rw [Matrix.mul_nonsing_inv _ hdet_is_unit, Matrix.mul_one]
    _ = (Matrix.of ![![a, b], ![c, d]] * P.val) * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P.val * Matrix.of ![![l, 1], ![0, l]]) * P.val⁻¹ := by rw [h_conj2]
    _ = P.val * Matrix.of ![![l, 1], ![0, l]] * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P.val * ((diag_matrix l hl_ne_zero).val * (jordan_matrix l⁻¹).val) * P⁻¹.val := by rw [←h_inv, ←h_jordan]

lemma sl2c_c_ne_zero_diag (a b c d l m : ℂ) (h_det : a * d - b * c = 1) (hc : c ≠ 0) (h_tr : l + m = a + d) (hlm : l * m = 1) (hlm_ne : l ≠ m) :
  ∃ (P : SpecialLinearGroup (Fin 2) ℂ) (a' : ℂ) (ha : a' ≠ 0),
  Matrix.of ![![a, b], ![c, d]] =
    P.val * (diag_matrix a' ha).val * P⁻¹.val := by
  let P₀ := Matrix.of ![![l - d, m - d], ![c, c]]
  have hP₀_det : P₀.det = c * (l - m) := by
    simp [P₀, Matrix.det_fin_two]
    ring
  have hP₀_ne_zero : P₀.det ≠ 0 := by
    rw [hP₀_det]
    intro hc0
    cases mul_eq_zero.mp hc0 with
    | inl h1 => exact hc h1
    | inr h2 => exact hlm_ne (eq_of_sub_eq_zero h2)
  rcases exists_scaled_sl2c P₀ hP₀_ne_zero with ⟨P, k, hP_eq, hk_ne⟩
  have hl_ne_zero : l ≠ 0 := by
    intro hl0
    rw [hl0, zero_mul] at hlm
    norm_num at hlm
  use P, l, hl_ne_zero
  have h_conj : Matrix.of ![![a, b], ![c, d]] * P₀ = P₀ * Matrix.of ![![l, 0], ![0, m]] := by
    have h_tr_sym : a + d - (l + m) = 0 := by linear_combination -h_tr
    have h_det_sym : a * d - b * c - 1 = 0 := by linear_combination h_det
    have hlm_sym : l * m - 1 = 0 := by linear_combination hlm
    exact c_ne_zero_diag_mul a b c d l m h_tr_sym h_det_sym hlm_sym
  have h_conj2 : Matrix.of ![![a, b], ![c, d]] * P.val = P.val * Matrix.of ![![l, 0], ![0, m]] := by
    rw [hP_eq]
    exact mul_smul_comm_matrix _ _ _ k h_conj
  have h_diag : Matrix.of ![![l, 0], ![0, m]] = (diag_matrix l hl_ne_zero).val := by
    exact diag_eq_diag_matrix l m hl_ne_zero hlm
  have h_inv : P⁻¹.val = P.val⁻¹ := by
    change (adjugate P.val) = P.val⁻¹
    have h_mul : P.val * adjugate P.val = 1 := by
      rw [Matrix.mul_adjugate P.val, P.prop, one_smul]
    exact Eq.symm (Matrix.inv_eq_right_inv h_mul)
  calc
    Matrix.of ![![a, b], ![c, d]] = Matrix.of ![![a, b], ![c, d]] * (P.val * P.val⁻¹) := by
      have hdet_is_unit : IsUnit P.val.det := by rw [P.prop]; exact isUnit_one
      rw [Matrix.mul_nonsing_inv _ hdet_is_unit, Matrix.mul_one]
    _ = (Matrix.of ![![a, b], ![c, d]] * P.val) * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = (P.val * Matrix.of ![![l, 0], ![0, m]]) * P.val⁻¹ := by rw [h_conj2]
    _ = P.val * Matrix.of ![![l, 0], ![0, m]] * P.val⁻¹ := by rw [Matrix.mul_assoc]
    _ = P.val * (diag_matrix l hl_ne_zero).val * P⁻¹.val := by rw [←h_inv, ←h_diag]

lemma sl2c_classification (C : SpecialLinearGroup (Fin 2) ℂ) :
  (∃ (P : SpecialLinearGroup (Fin 2) ℂ) (a : ℂ) (ha : a ≠ 0), C = P * diag_matrix a ha * P⁻¹) ∨
  (∃ (P : SpecialLinearGroup (Fin 2) ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (c : ℂ),
     C = P * (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c) * P⁻¹) := by
  let a := C.val 0 0
  let b := C.val 0 1
  let c := C.val 1 0
  let d := C.val 1 1
  have h_det : a * d - b * c = 1 := by
    have h := C.prop
    change C.val.det = 1 at h
    rw [Matrix.det_fin_two] at h
    exact h
  rcases exists_roots_of_tr (a + d) with ⟨l, m, h_tr, h_lm⟩

  by_cases hc : c = 0
  · 
    by_cases had : a = d
    · 
      have h_det2 : a * d - b * 0 = 1 := by rw [←hc]; exact h_det
      rcases sl2c_c_eq_zero_jordan a b d h_det2 had with ⟨ε, hε, c', hc'⟩
      right
      use 1, ε, hε, c'
      have hC : C.val = Matrix.of ![![a, b], ![0, d]] := by
        ext i j
        fin_cases i <;> fin_cases j
        · rfl
        · rfl
        · exact hc
        · rfl
      apply Subtype.ext
      rw [hC]
      exact hc'
    · 
      have h_det2 : a * d - b * 0 = 1 := by rw [←hc]; exact h_det
      rcases sl2c_c_eq_zero_diag a b d h_det2 had with ⟨P, l', hl', hc'⟩
      left
      use P, l', hl'
      have hC : C.val = Matrix.of ![![a, b], ![0, d]] := by
        ext i j
        fin_cases i <;> fin_cases j
        · rfl
        · rfl
        · exact hc
        · rfl
      apply Subtype.ext
      rw [hC]
      exact hc'
  · 
    by_cases hlm : l = m
    · 
      have hl2 : l * l = 1 := by rw [←hlm] at h_lm; exact h_lm
      have h_tr2 : l + l = a + d := by rw [←hlm] at h_tr; exact h_tr
      rcases sl2c_c_ne_zero_jordan a b c d l h_det hc h_tr2 hl2 with ⟨P, ε, hε, c', hc'⟩
      right
      use P, ε, hε, c'
      have hC : C.val = Matrix.of ![![a, b], ![c, d]] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      apply Subtype.ext
      rw [hC]
      exact hc'
    · 
      rcases sl2c_c_ne_zero_diag a b c d l m h_det hc h_tr h_lm hlm with ⟨P, l', hl', hc'⟩
      left
      use P, l', hl'
      have hC : C.val = Matrix.of ![![a, b], ![c, d]] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      apply Subtype.ext
      rw [hC]
      exact hc'

lemma aux_neg_one_comm (J : SpecialLinearGroup (Fin 2) ℂ) :
    J * (-1 : SpecialLinearGroup (Fin 2) ℂ) = (-1 : SpecialLinearGroup (Fin 2) ℂ) * J := by
  apply Subtype.ext
  change J.val * -1 = -1 * J.val
  ext i j
  simp

lemma aux_inv_neg_one : (-1 : SpecialLinearGroup (Fin 2) ℂ)⁻¹ = -1 := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply]

lemma aux_D_J_comm (D J : SpecialLinearGroup (Fin 2) ℂ) (hD : D = 1 ∨ D = -1) :
    J * D = D * J := by
  rcases hD with rfl | rfl
  · rw [mul_one, one_mul]
  · exact aux_neg_one_comm J

lemma spinorPhi_S_matrix_to_M_aux_g (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (c : ℂ) :
    (spinorPhi (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c,
     (sl2c_conj (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c))⁻¹)).val.val =
    (spinorPhi (jordan_matrix c, (sl2c_conj (jordan_matrix c))⁻¹)).val.val := by
  let D : SpecialLinearGroup (Fin 2) ℂ := diag_matrix ε (by rcases hε with h | h <;> simp [h])
  let J : SpecialLinearGroup (Fin 2) ℂ := jordan_matrix c
  have h_conj_D_J : sl2c_conj (D * J) = sl2c_conj D * sl2c_conj J := sl2c_conj_mul D J
  have h_inv_mul : (sl2c_conj D * sl2c_conj J)⁻¹ = (sl2c_conj J)⁻¹ * (sl2c_conj D)⁻¹ := _root_.mul_inv_rev (sl2c_conj D) (sl2c_conj J)

  have hD_val : sl2c_conj D = 1 ∨ sl2c_conj D = -1 := by
    rcases hε with rfl | rfl
    · left
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D, sl2c_conj, diag_matrix]
    · right
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D, sl2c_conj, diag_matrix]

  have hD_inv_val : (sl2c_conj D)⁻¹ = 1 ∨ (sl2c_conj D)⁻¹ = -1 := by
    rcases hD_val with h | h
    · left
      rw [h, inv_one]
    · right
      rw [h]
      exact aux_inv_neg_one

  have h_comm : (sl2c_conj J)⁻¹ * (sl2c_conj D)⁻¹ = (sl2c_conj D)⁻¹ * (sl2c_conj J)⁻¹ := by
    exact aux_D_J_comm ((sl2c_conj D)⁻¹) ((sl2c_conj J)⁻¹) hD_inv_val

  have h_tuple : (D * J, (sl2c_conj (D * J))⁻¹) = (D * J, (sl2c_conj D)⁻¹ * (sl2c_conj J)⁻¹) := by
    apply Prod.ext
    · rfl
    · rw [h_conj_D_J, h_inv_mul, h_comm]
  rw [h_tuple]
  have h_prod : (D * J, (sl2c_conj D)⁻¹ * (sl2c_conj J)⁻¹) = (D, (sl2c_conj D)⁻¹) * (J, (sl2c_conj J)⁻¹) := rfl
  rw [h_prod]
  have h_map := MonoidHom.map_mul spinorPhi (D, (sl2c_conj D)⁻¹) (J, (sl2c_conj J)⁻¹)
  change (spinorPhi ((D, (sl2c_conj D)⁻¹) * (J, (sl2c_conj J)⁻¹))).val.val = _
  rw [h_map]
  have h_mul_val : (spinorPhi (D, (sl2c_conj D)⁻¹) * spinorPhi (J, (sl2c_conj J)⁻¹)).val.val =
                   (spinorPhi (D, (sl2c_conj D)⁻¹)).val.val * (spinorPhi (J, (sl2c_conj J)⁻¹)).val.val := rfl
  rw [h_mul_val]
  have h_D_1 := spinorPhi_S_matrix_to_M_aux_f ε hε
  rw [h_D_1, Matrix.one_mul]

lemma spinorPhi_S_matrix_to_M (C : SpecialLinearGroup (Fin 2) ℂ) :
    ∃ (M : Matrix (Fin 4) (Fin 4) ℝ),
      Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0 ∧
      (spinorPhi (C, (sl2c_conj C)⁻¹)).val.val = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map M (fun x => (x : ℂ))) := by
  have h_cases := sl2c_classification C
  rcases h_cases with ⟨P, a, ha, hC⟩ | ⟨P, ε, hε, c, hC⟩
  · 
    rcases spinorPhi_S_matrix_to_M_diag a ha with ⟨M_d, h_lorentz, h_exp_d⟩
    let L : Matrix (Fin 4) (Fin 4) ℝ := Classical.choose (spinorPhi_is_real P)
    have hL : (spinorPhi (P, sl2c_conj P)).val.val = Matrix.map L (fun x => (x : ℂ)) := Classical.choose_spec (spinorPhi_is_real P)
    let L_inv : Matrix (Fin 4) (Fin 4) ℝ := Classical.choose (spinorPhi_is_real P⁻¹)
    have hL_inv : (spinorPhi (P⁻¹, sl2c_conj P⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)) := Classical.choose_spec (spinorPhi_is_real P⁻¹)
    have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P L hL L_inv hL_inv
    use L * M_d * L_inv
    constructor
    · have hL_lorentz := spinorPhi_S_matrix_to_M_aux_b P L hL
      exact spinorPhi_S_matrix_to_M_aux_d M_d L L_inv hL_lorentz h_L_inv_eq.1 h_L_inv_eq.2 h_lorentz
    · have h_e := spinorPhi_S_matrix_to_M_aux_e C P (diag_matrix a ha) hC
      rw [h_e, hL, hL_inv, h_exp_d]
      exact (exp_conj_complex L M_d L_inv h_L_inv_eq.1 h_L_inv_eq.2).symm
  · 
    rcases spinorPhi_S_matrix_to_M_jordan c with ⟨M_j, h_lorentz, h_exp_j⟩
    let L : Matrix (Fin 4) (Fin 4) ℝ := Classical.choose (spinorPhi_is_real P)
    have hL : (spinorPhi (P, sl2c_conj P)).val.val = Matrix.map L (fun x => (x : ℂ)) := Classical.choose_spec (spinorPhi_is_real P)
    let L_inv : Matrix (Fin 4) (Fin 4) ℝ := Classical.choose (spinorPhi_is_real P⁻¹)
    have hL_inv : (spinorPhi (P⁻¹, sl2c_conj P⁻¹)).val.val = Matrix.map L_inv (fun x => (x : ℂ)) := Classical.choose_spec (spinorPhi_is_real P⁻¹)
    have h_L_inv_eq := spinorPhi_S_matrix_to_M_aux_c P L hL L_inv hL_inv
    use L * M_j * L_inv
    constructor
    · have hL_lorentz := spinorPhi_S_matrix_to_M_aux_b P L hL
      exact spinorPhi_S_matrix_to_M_aux_d M_j L L_inv hL_lorentz h_L_inv_eq.1 h_L_inv_eq.2 h_lorentz
    · have h_e := spinorPhi_S_matrix_to_M_aux_e C P (diag_matrix ε (by rcases hε with h | h <;> simp [h]) * jordan_matrix c) hC
      rw [h_e, hL, hL_inv]
      have h_g := spinorPhi_S_matrix_to_M_aux_g ε hε c
      rw [h_g, h_exp_j]
      exact (exp_conj_complex L M_j L_inv h_L_inv_eq.1 h_L_inv_eq.2).symm


lemma complex_lorentz_cartan_core_matrix (Λ : Matrix (Fin 4) (Fin 4) ℂ)
    (h_lorentz : Λᵀ * minkowskiMetric * Λ = minkowskiMetric)
    (h_det : Λ.det = 1) :
    ∃ (M : Matrix (Fin 4) (Fin 4) ℝ),
      Mᵀ * minkowskiMetricReal + minkowskiMetricReal * M = 0 ∧
      Λ * (Matrix.map Λ star)⁻¹ = NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map M (fun x => (x : ℂ))) := by
  let Λ_GL : GeneralLinearGroup (Fin 4) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Λ (by rw [h_det]; exact one_ne_zero)
  have hΛ_SSCL_prop : (Λ_GL.val)ᵀ * minkowskiMetric * Λ_GL.val = minkowskiMetric ∧ (Λ_GL.val).det = 1 := ⟨h_lorentz, h_det⟩
  let Λ_SSCL : SpecialSpecialComplexLorentzGroup := ⟨Λ_GL, hΛ_SSCL_prop⟩
  rcases spinorPhi_surjective Λ_SSCL with ⟨⟨A, B⟩, hAB⟩
  have h_Λ_eq : Λ = (spinorPhi (A, B)).val.val := by
    change Λ_SSCL.val.val = (spinorPhi (A, B)).val.val
    rw [hAB]
  have h_S := spinorPhi_S_matrix A B
  rcases h_S with ⟨C, hC⟩
  rw [h_Λ_eq, hC]
  exact spinorPhi_S_matrix_to_M C

end Geometry.MatrixAnalysis
