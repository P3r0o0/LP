import MatrixAnalysis

open Matrix
open scoped ComplexOrder Norms.Operator
open Complex

open Geometry
open Geometry.MatrixAnalysis

noncomputable def c_s_diag (a : ℂ) (s : ℝ) : ℂ := Complex.exp (s * (Complex.log a).re + Complex.I * (s * (Complex.log a).im))
lemma c_s_diag_ne_zero (a : ℂ) (s : ℝ) : c_s_diag a s ≠ 0 := Complex.exp_ne_zero _

lemma exp_two_re_s_u (a : ℂ) (s : ℝ) :
  NormedSpace.exp (2 * (s * (Complex.log a).re : ℂ)) = c_s_diag a s * star (c_s_diag a s) := by
  have h_exp_eq : (NormedSpace.exp : ℂ → ℂ) = Complex.exp := Complex.exp_eq_exp_ℂ.symm
  rw [h_exp_eq]
  change Complex.exp _ = c_s_diag a s * (starRingEnd ℂ) (c_s_diag a s)
  dsimp [c_s_diag]
  have h1 : (starRingEnd ℂ) (Complex.exp (↑s * ↑(Complex.log a).re + Complex.I * (↑s * ↑(Complex.log a).im))) = Complex.exp (↑s * ↑(Complex.log a).re - Complex.I * (↑s * ↑(Complex.log a).im)) := by
    rw [←Complex.exp_conj]
    congr 1
    simp
    ring
  rw [h1, ←Complex.exp_add]
  congr 1
  ring

lemma exp_two_re_s_u_neg (a : ℂ) (s : ℝ) :
  NormedSpace.exp (-2 * (s * (Complex.log a).re : ℂ)) = (c_s_diag a s * star (c_s_diag a s))⁻¹ := by
  have h_exp_eq : (NormedSpace.exp : ℂ → ℂ) = Complex.exp := Complex.exp_eq_exp_ℂ.symm
  rw [h_exp_eq]
  have H := exp_two_re_s_u a s
  rw [h_exp_eq] at H
  rw [←H]
  rw [←Complex.exp_neg]
  congr 1
  ring

lemma exp_two_im_s_v (a : ℂ) (s : ℝ) :
  NormedSpace.exp (2 * Complex.I * (s * (Complex.log a).im : ℂ)) = c_s_diag a s * (star (c_s_diag a s))⁻¹ := by
  have h_exp_eq : (NormedSpace.exp : ℂ → ℂ) = Complex.exp := Complex.exp_eq_exp_ℂ.symm
  rw [h_exp_eq]
  change Complex.exp _ = c_s_diag a s * ((starRingEnd ℂ) (c_s_diag a s))⁻¹
  dsimp [c_s_diag]
  have h1 : (starRingEnd ℂ) (Complex.exp (↑s * ↑(Complex.log a).re + Complex.I * (↑s * ↑(Complex.log a).im))) = Complex.exp (↑s * ↑(Complex.log a).re - Complex.I * (↑s * ↑(Complex.log a).im)) := by
    rw [←Complex.exp_conj]
    congr 1
    simp
    ring
  rw [h1, ←Complex.exp_neg, ←Complex.exp_add]
  congr 1
  ring

lemma exp_two_im_s_v_neg (a : ℂ) (s : ℝ) :
  NormedSpace.exp (-2 * Complex.I * (s * (Complex.log a).im : ℂ)) = (c_s_diag a s)⁻¹ * star (c_s_diag a s) := by
  have h_exp_eq : (NormedSpace.exp : ℂ → ℂ) = Complex.exp := Complex.exp_eq_exp_ℂ.symm
  rw [h_exp_eq]
  change Complex.exp _ = (c_s_diag a s)⁻¹ * (starRingEnd ℂ) (c_s_diag a s)
  dsimp [c_s_diag]
  have h1 : (starRingEnd ℂ) (Complex.exp (↑s * ↑(Complex.log a).re + Complex.I * (↑s * ↑(Complex.log a).im))) = Complex.exp (↑s * ↑(Complex.log a).re - Complex.I * (↑s * ↑(Complex.log a).im)) := by
    rw [←Complex.exp_conj]
    congr 1
    simp
    ring
  rw [h1, ←Complex.exp_neg, ←Complex.exp_add]
  congr 1
  ring

lemma s_M_D_eq (a : ℂ) (s : ℝ) :
  ((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)) =
  ((2 * Complex.I) : ℂ) • Matrix.map (Matrix.of ![![0, 0, 0, s * (Complex.log a).im],
                   ![0, 0, - (s * (Complex.log a).re), 0],
                   ![0, s * (Complex.log a).re, 0, 0],
                   ![s * (Complex.log a).im, 0, 0, 0]]) (fun x => (x : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_D, Matrix.map_apply, Pi.smul_apply, Matrix.of_apply] <;> ring

lemma exp_re_eq (a : ℂ) (s : ℝ) : NormedSpace.exp (↑s * ↑(Complex.log a).re * 2 : ℂ) = c_s_diag a s * star (c_s_diag a s) := by
  have h : (↑s * ↑(Complex.log a).re * 2 : ℂ) = 2 * (↑s * ↑(Complex.log a).re) := by ring
  rw [h, exp_two_re_s_u]

lemma exp_re_neg_eq (a : ℂ) (s : ℝ) : NormedSpace.exp (-(↑s * ↑(Complex.log a).re * 2) : ℂ) = (c_s_diag a s * star (c_s_diag a s))⁻¹ := by
  have h : (-(↑s * ↑(Complex.log a).re * 2) : ℂ) = -2 * (↑s * ↑(Complex.log a).re) := by ring
  rw [h, exp_two_re_s_u_neg]

lemma exp_im_eq (a : ℂ) (s : ℝ) : NormedSpace.exp (I * ↑s * ↑(Complex.log a).im * 2 : ℂ) = c_s_diag a s * (star (c_s_diag a s))⁻¹ := by
  have h : (I * ↑s * ↑(Complex.log a).im * 2 : ℂ) = 2 * I * (↑s * ↑(Complex.log a).im) := by ring
  rw [h, exp_two_im_s_v]

lemma exp_im_neg_eq (a : ℂ) (s : ℝ) : NormedSpace.exp (-(I * ↑s * ↑(Complex.log a).im * 2) : ℂ) = (c_s_diag a s)⁻¹ * star (c_s_diag a s) := by
  have h : (-(I * ↑s * ↑(Complex.log a).im * 2) : ℂ) = -2 * I * (↑s * ↑(Complex.log a).im) := by ring
  rw [h, exp_two_im_s_v_neg]

lemma spinorPhi_S_matrix_to_M_diag_s_eq_0_0 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 0 0 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 0 0 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_0]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 0 0 = _
  rw [spinorPhi_matrix_diag_col_0 (c_s_diag a s) (c_s_diag_ne_zero a s) 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_0_1 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 0 1 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 0 1 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_1]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 0 1 = _
  rw [spinorPhi_matrix_diag_col_1 (c_s_diag a s) (c_s_diag_ne_zero a s) 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_0_2 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 0 2 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 0 2 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_2]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 0 2 = _
  rw [spinorPhi_matrix_diag_col_2 (c_s_diag a s) (c_s_diag_ne_zero a s) 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_0_3 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 0 3 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 0 3 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_0_3]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 0 3 = _
  rw [spinorPhi_matrix_diag_col_3 (c_s_diag a s) (c_s_diag_ne_zero a s) 0]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_1_0 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 1 0 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 1 0 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_0]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 1 0 = _
  rw [spinorPhi_matrix_diag_col_0 (c_s_diag a s) (c_s_diag_ne_zero a s) 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_1_1 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 1 1 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 1 1 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_1]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 1 1 = _
  rw [spinorPhi_matrix_diag_col_1 (c_s_diag a s) (c_s_diag_ne_zero a s) 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_1_2 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 1 2 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 1 2 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_2]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 1 2 = _
  rw [spinorPhi_matrix_diag_col_2 (c_s_diag a s) (c_s_diag_ne_zero a s) 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_1_3 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 1 3 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 1 3 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_1_3]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 1 3 = _
  rw [spinorPhi_matrix_diag_col_3 (c_s_diag a s) (c_s_diag_ne_zero a s) 1]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_2_0 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 2 0 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 2 0 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_0]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 2 0 = _
  rw [spinorPhi_matrix_diag_col_0 (c_s_diag a s) (c_s_diag_ne_zero a s) 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_2_1 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 2 1 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 2 1 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_1]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 2 1 = _
  rw [spinorPhi_matrix_diag_col_1 (c_s_diag a s) (c_s_diag_ne_zero a s) 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_2_2 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 2 2 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 2 2 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_2]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 2 2 = _
  rw [spinorPhi_matrix_diag_col_2 (c_s_diag a s) (c_s_diag_ne_zero a s) 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_2_3 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 2 3 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 2 3 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_2_3]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 2 3 = _
  rw [spinorPhi_matrix_diag_col_3 (c_s_diag a s) (c_s_diag_ne_zero a s) 2]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_3_0 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 3 0 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 3 0 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_0]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 3 0 = _
  rw [spinorPhi_matrix_diag_col_0 (c_s_diag a s) (c_s_diag_ne_zero a s) 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_3_1 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 3 1 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 3 1 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_1]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 3 1 = _
  rw [spinorPhi_matrix_diag_col_1 (c_s_diag a s) (c_s_diag_ne_zero a s) 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_3_2 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 3 2 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 3 2 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_2]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 3 2 = _
  rw [spinorPhi_matrix_diag_col_2 (c_s_diag a s) (c_s_diag_ne_zero a s) 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s_eq_3_3 (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
    (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val 3 3 =
    (NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ)))) 3 3 := by
  have h_exp_re := exp_two_re_s_u a s
  have h_exp_re_neg := exp_two_re_s_u_neg a s
  have h_exp_im := exp_two_im_s_v a s
  have h_exp_im_neg := exp_two_im_s_v_neg a s
  rw [s_M_D_eq]
  rw [exp_M_D]
  rw [P_D_P_inv_eq_3_3]
  change spinorPhi_matrix (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)) ((sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹) 3 3 = _
  rw [spinorPhi_matrix_diag_col_3 (c_s_diag a s) (c_s_diag_ne_zero a s) 3]
  dsimp [spinor_to_vec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
  try push_cast
  try rw [exp_two_re_s_u a s]
  try rw [exp_two_re_s_u_neg a s]
  try rw [exp_two_im_s_v a s]
  try rw [exp_two_im_s_v_neg a s]
  try simp only [starRingEnd_apply]
  try ring_nf
  try simp only [Complex.I_sq]
  try ring

lemma spinorPhi_S_matrix_to_M_diag_s (a : ℂ) (ha : a ≠ 0) (s : ℝ) :
  (spinorPhi (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s), (sl2c_conj (diag_matrix (c_s_diag a s) (c_s_diag_ne_zero a s)))⁻¹)).val.val =
  NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_D a) (fun x => (x : ℂ))) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_0_0 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_0_1 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_0_2 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_0_3 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_1_0 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_1_1 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_1_2 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_1_3 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_2_0 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_2_1 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_2_2 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_2_3 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_3_0 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_3_1 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_3_2 a ha s
  · exact spinorPhi_S_matrix_to_M_diag_s_eq_3_3 a ha s

lemma smul_M_J_eq (c : ℂ) (s : ℝ) :
  Matrix.map (s • M_J c) (fun x => (x : ℂ)) = Matrix.map (M_J (s * c)) (fun x => (x : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M_J, Matrix.map_apply, Pi.smul_apply, Matrix.of_apply] <;> ring

lemma spinorPhi_S_matrix_to_M_jordan_s_exact (c : ℂ) (s : ℝ) :
  (spinorPhi (jordan_matrix (s * c), (sl2c_conj (jordan_matrix (s * c)))⁻¹)).val.val =
  NormedSpace.exp (((2 * Complex.I) : ℂ) • Matrix.map (s • M_J c) (fun x => (x : ℂ))) := by
  have h_eq : ((2 * Complex.I) : ℂ) • Matrix.map (s • M_J c) (fun x => (x : ℂ)) = ((2 * Complex.I) : ℂ) • Matrix.map (M_J (s * c)) (fun x => (x : ℂ)) := by
    rw [smul_M_J_eq]
  rw [h_eq]
  have h_nilp : (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s * c)) (fun x => (x : ℂ))) ^ 3 = 0 := N_mat_nilpotent (s * c)
  rw [exp_of_nilpotent3 _ h_nilp]
  have h_pow2 : (((2 * Complex.I) : ℂ) • Matrix.map (M_J (s * c)) (fun x => (x : ℂ))) ^ 2 = N_mat (s * c) * N_mat (s * c) := by
    change N_mat (s * c) ^ 2 = N_mat (s * c) * N_mat (s * c)
    rw [pow_two]
  rw [h_pow2]
  change _ = 1 + N_mat (s * c) + (1 / 2 : ℂ) • (N_mat (s * c) * N_mat (s * c))
  exact spinorPhi_S_matrix_to_M_jordan_eq (s * c)
