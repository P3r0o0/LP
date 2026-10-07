import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Spinor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

open scoped Matrix
open Matrix
open Complex
open Filter Topology

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedAddCommGroup
noncomputable local instance : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedSpace

lemma analyticAt_matrix_proj (i j : Fin 2) (M₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    AnalyticAt ℂ (fun (M : Matrix (Fin 2) (Fin 2) ℂ) => M i j) M₀ := by
  let P_i : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) i
  let P_j : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) j
  let L := P_j.comp P_i
  have h_eq : (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) = ⇑L := rfl
  rw [h_eq]
  exact L.analyticAt M₀

lemma analyticAt_matrix_mulLeft (A : Matrix (Fin 2) (Fin 2) ℂ) (M₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    AnalyticAt ℂ (fun M => A * M) M₀ := by
  let H := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)
  have h_eq : (fun M => A * M) = ⇑H := rfl
  rw [h_eq]
  exact H.analyticAt M₀

namespace Geometry


noncomputable def sl2c_chart_at_id (a : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ (1 + a 0 ^ 2 + a 1 ^ 2) / (1 - a 2), a 0 - I * a 1 ;
      a 0 + I * a 1,                      1 - a 2 ]

lemma sl2c_chart_at_id_det (a : Fin 3 → ℂ) (h : a 2 ≠ 1) :
    (sl2c_chart_at_id a).det = 1 := by
  dsimp [sl2c_chart_at_id]
  rw [det_fin_two]
  change ((1 + a 0 ^ 2 + a 1 ^ 2) / (1 - a 2)) * (1 - a 2) - (a 0 - I * a 1) * (a 0 + I * a 1) = 1
  have h_div : (1 + a 0 ^ 2 + a 1 ^ 2) / (1 - a 2) * (1 - a 2) = 1 + a 0 ^ 2 + a 1 ^ 2 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr h.symm)
  rw [h_div]
  calc (1 + a 0 ^ 2 + a 1 ^ 2) - (a 0 - I * a 1) * (a 0 + I * a 1)
    _ = (1 + a 0 ^ 2 + a 1 ^ 2) - (a 0 ^ 2 - (I * a 1) ^ 2) := by ring
    _ = (1 + a 0 ^ 2 + a 1 ^ 2) - (a 0 ^ 2 - (I^2 * a 1 ^ 2)) := by ring
    _ = (1 + a 0 ^ 2 + a 1 ^ 2) - (a 0 ^ 2 - (-1 * a 1 ^ 2)) := by rw [I_sq]
    _ = 1 := by ring


noncomputable def sl2c_chart_inv (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  fun i =>
    if i = 0 then (A 0 1 + A 1 0) / 2
    else if i = 1 then (A 1 0 - A 0 1) / (2 * I)
    else 1 - A 1 1

lemma sl2c_chart_inv_left_inv (a : Fin 3 → ℂ) :
    sl2c_chart_inv (sl2c_chart_at_id a) = a := by
  ext i
  fin_cases i
  · change ((a 0 - I * a 1) + (a 0 + I * a 1)) / 2 = a 0
    ring
  · change ((a 0 + I * a 1) - (a 0 - I * a 1)) / (2 * I) = a 1
    have h_num : a 0 + I * a 1 - (a 0 - I * a 1) = 2 * I * a 1 := by ring
    rw [h_num]
    have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
    exact mul_div_cancel_left₀ (a 1) hI
  · change 1 - (1 - a 2) = a 2
    ring

lemma sl2c_chart_inv_right_inv (A : Matrix (Fin 2) (Fin 2) ℂ) (hdet : A.det = 1) (hA11 : A 1 1 ≠ 0) :
    sl2c_chart_at_id (sl2c_chart_inv A) = A := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [sl2c_chart_at_id, sl2c_chart_inv, sigma_1, sigma_2, sigma_3]
    have h1 : 1 - (1 - A 1 1) = A 1 1 := by ring
    rw [h1]
    have h2 : 1 + ((A 0 1 + A 1 0) / 2) ^ 2 + ((A 1 0 - A 0 1) / (2 * I)) ^ 2 = 1 + A 0 1 * A 1 0 := by
      calc
        1 + ((A 0 1 + A 1 0) / 2) ^ 2 + ((A 1 0 - A 0 1) / (2 * I)) ^ 2
          = 1 + (A 0 1 + A 1 0) ^ 2 / 4 + (A 1 0 - A 0 1) ^ 2 / ((2 * I) ^ 2) := by ring
        _ = 1 + (A 0 1 + A 1 0) ^ 2 / 4 + (A 1 0 - A 0 1) ^ 2 / (4 * I ^ 2) := by ring
        _ = 1 + (A 0 1 + A 1 0) ^ 2 / 4 + (A 1 0 - A 0 1) ^ 2 / (4 * -1) := by rw [I_sq]
        _ = 1 + (A 0 1 + A 1 0) ^ 2 / 4 - (A 1 0 - A 0 1) ^ 2 / 4 := by ring
        _ = 1 + A 0 1 * A 1 0 := by ring
    rw [h2]
    have hdet_eq : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      calc A 0 0 * A 1 1 - A 0 1 * A 1 0 = A.det := by rw [det_fin_two]
      _ = 1 := hdet
    have h3 : 1 + A 0 1 * A 1 0 = A 0 0 * A 1 1 := by
      calc 1 + A 0 1 * A 1 0 = A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 1 * A 1 0 := by rw [hdet_eq]
      _ = A 0 0 * A 1 1 := by ring
    rw [h3]
    exact mul_div_cancel_right₀ (A 0 0) hA11
  · dsimp [sl2c_chart_at_id, sl2c_chart_inv, sigma_1, sigma_2, sigma_3]
    have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
    calc
      (A 0 1 + A 1 0) / 2 - I * ((A 1 0 - A 0 1) / (2 * I))
        = (A 0 1 + A 1 0) / 2 - (I * (A 1 0 - A 0 1)) / (I * 2) := by ring
      _ = (A 0 1 + A 1 0) / 2 - (A 1 0 - A 0 1) / 2 := by rw [mul_div_mul_left (A 1 0 - A 0 1) 2 I_ne_zero]
      _ = A 0 1 := by ring
  · dsimp [sl2c_chart_at_id, sl2c_chart_inv, sigma_1, sigma_2, sigma_3]
    calc
      (A 0 1 + A 1 0) / 2 + I * ((A 1 0 - A 0 1) / (2 * I))
        = (A 0 1 + A 1 0) / 2 + (I * (A 1 0 - A 0 1)) / (I * 2) := by ring
      _ = (A 0 1 + A 1 0) / 2 + (A 1 0 - A 0 1) / 2 := by rw [mul_div_mul_left (A 1 0 - A 0 1) 2 I_ne_zero]
      _ = A 1 0 := by ring
  · dsimp [sl2c_chart_at_id, sl2c_chart_inv, sigma_1, sigma_2, sigma_3]
    ring


lemma sl2c_chart_at_id_analytic (a : Fin 3 → ℂ) (h : a 2 ≠ 1) :
    AnalyticAt ℂ sl2c_chart_at_id a := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · apply analyticAt_pi_iff.mpr
    intro j
    fin_cases j
    · dsimp [sl2c_chart_at_id]
      apply AnalyticAt.div
      · apply AnalyticAt.add
        · apply AnalyticAt.add
          · exact analyticAt_const
          · apply AnalyticAt.pow
            exact analyticAt_pi_iff.mp analyticAt_id 0
        · apply AnalyticAt.pow
          exact analyticAt_pi_iff.mp analyticAt_id 1
      · apply AnalyticAt.sub
        · exact analyticAt_const
        · exact analyticAt_pi_iff.mp analyticAt_id 2
      · exact sub_ne_zero.mpr h.symm
    · dsimp [sl2c_chart_at_id]
      apply AnalyticAt.sub
      · exact analyticAt_pi_iff.mp analyticAt_id 0
      · apply AnalyticAt.mul
        · exact analyticAt_const
        · exact analyticAt_pi_iff.mp analyticAt_id 1
  · apply analyticAt_pi_iff.mpr
    intro j
    fin_cases j
    · dsimp [sl2c_chart_at_id]
      apply AnalyticAt.add
      · exact analyticAt_pi_iff.mp analyticAt_id 0
      · apply AnalyticAt.mul
        · exact analyticAt_const
        · exact analyticAt_pi_iff.mp analyticAt_id 1
    · dsimp [sl2c_chart_at_id]
      apply AnalyticAt.sub
      · exact analyticAt_const
      · exact analyticAt_pi_iff.mp analyticAt_id 2


noncomputable def pauli_map_lin : (Fin 3 → ℂ) →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => a 0 • (sigma_1 : Matrix (Fin 2) (Fin 2) ℂ) + a 1 • (sigma_2 : Matrix (Fin 2) (Fin 2) ℂ) + a 2 • (sigma_3 : Matrix (Fin 2) (Fin 2) ℂ)
    map_add' := fun x y => by
      ext i j
      change (x 0 + y 0) * sigma_1 i j + (x 1 + y 1) * sigma_2 i j + (x 2 + y 2) * sigma_3 i j =
        (x 0 * sigma_1 i j + x 1 * sigma_2 i j + x 2 * sigma_3 i j) +
        (y 0 * sigma_1 i j + y 1 * sigma_2 i j + y 2 * sigma_3 i j)
      ring
    map_smul' := fun c x => by
      ext i j
      change (c * x 0) * sigma_1 i j + (c * x 1) * sigma_2 i j + (c * x 2) * sigma_3 i j =
        c * (x 0 * sigma_1 i j + x 1 * sigma_2 i j + x 2 * sigma_3 i j)
      ring
  }


lemma hasFDerivAt_sl2c_chart_at_id_zero :
    HasFDerivAt sl2c_chart_at_id pauli_map_lin 0 := by
  have H : HasFDerivAt sl2c_chart_at_id
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      ContinuousLinearMap.pi (fun j : Fin 2 =>
        LinearMap.toContinuousLinearMap {
          toFun := fun a => a 0 * sigma_1 i j + a 1 * sigma_2 i j + a 2 * sigma_3 i j
          map_add' := fun x y => by dsimp; ring
          map_smul' := fun (c : ℂ) x => by dsimp; ring
        }
      )
    )) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · apply hasFDerivAt_pi.mpr
      intro j
      fin_cases j
      · dsimp [sl2c_chart_at_id]
        have eq_fun : (fun a : Fin 3 → ℂ => (1 + a 0 ^ 2 + a 1 ^ 2) / (1 - a 2)) = (fun a : Fin 3 → ℂ => (1 + a 0 * a 0 + a 1 * a 1) * (1 - a 2)⁻¹) := by ext a; ring
        rw [eq_fun]

        have h0 := (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h0_sq := HasFDerivAt.mul h0 h0
        have h1 := (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h1_sq := HasFDerivAt.mul h1 h1
        have hc : HasFDerivAt (fun _ : Fin 3 → ℂ => (1 : ℂ)) (0 : (Fin 3 → ℂ) →L[ℂ] ℂ) 0 := hasFDerivAt_const 1 0

        have num_deriv := HasFDerivAt.add (HasFDerivAt.add hc h0_sq) h1_sq

        have h2 := (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have den_deriv_inner := HasFDerivAt.sub hc h2

        have h_inv_1 := hasFDerivAt_inv (x := (1 : ℂ)) (by norm_num)
        have h_eq : (1 : ℂ) = (((fun _ : Fin 3 → ℂ => (1:ℂ)) - (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ)) 0) := by simp
        have h_inv_2 := h_eq ▸ h_inv_1

        have den_deriv := HasFDerivAt.comp 0 h_inv_2 den_deriv_inner

        have prod_deriv := HasFDerivAt.mul num_deriv den_deriv

        apply prod_deriv.congr_fderiv
        ext a
        dsimp [sigma_1, sigma_2, sigma_3]
        simp [ContinuousLinearMap.toSpanSingleton]
      · have h0 := (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h1 := (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h1I := HasFDerivAt.const_smul h1 (I : ℂ)
        have hd := HasFDerivAt.sub h0 h1I
        apply hd.congr_fderiv
        ext a
        change a 0 - I * a 1 = a 0 * sigma_1 0 1 + a 1 * sigma_2 0 1 + a 2 * sigma_3 0 1
        dsimp [sigma_1, sigma_2, sigma_3]
        ring
    · apply hasFDerivAt_pi.mpr
      intro j
      fin_cases j
      · have h0 := (ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h1 := (ContinuousLinearMap.proj 1 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have h1I := HasFDerivAt.const_smul h1 (I : ℂ)
        have hd := HasFDerivAt.add h0 h1I
        apply hd.congr_fderiv
        ext a
        change a 0 + I * a 1 = a 0 * sigma_1 1 0 + a 1 * sigma_2 1 0 + a 2 * sigma_3 1 0
        dsimp [sigma_1, sigma_2, sigma_3]
        ring
      · have h2 := (ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := 0)
        have hc : HasFDerivAt (fun _ : Fin 3 → ℂ => (1 : ℂ)) (0 : (Fin 3 → ℂ) →L[ℂ] ℂ) 0 := hasFDerivAt_const 1 0
        have hd := HasFDerivAt.sub hc h2
        simp at hd
        apply hd.congr_fderiv
        ext a
        change - a 2 = a 0 * sigma_1 1 1 + a 1 * sigma_2 1 1 + a 2 * sigma_3 1 1
        dsimp [sigma_1, sigma_2, sigma_3]
        ring
  apply H.congr_fderiv
  ext a i j
  change a 0 * sigma_1 i j + a 1 * sigma_2 i j + a 2 * sigma_3 i j = (pauli_map_lin a) i j
  dsimp [pauli_map_lin]

lemma sl2c_chart_inv_continuous : Continuous sl2c_chart_inv := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1 + A 1 0) / 2)
    fun_prop
  · change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 0 - A 0 1) / (2 * I))
    fun_prop
  · change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => 1 - A 1 1)
    fun_prop

noncomputable def sl2c_chart_invFun (a : Fin 3 → ℂ) : SpecialLinearGroup (Fin 2) ℂ :=
  if h : a 2 = 1 then
    1
  else
    ⟨sl2c_chart_at_id a, sl2c_chart_at_id_det a h⟩

lemma sl2c_chart_invFun_eq {a : Fin 3 → ℂ} (h : a 2 ≠ 1) :
    (sl2c_chart_invFun a).1 = sl2c_chart_at_id a := by
  dsimp [sl2c_chart_invFun]
  rw [dif_neg h]

lemma continuousOn_invFun_aux : ContinuousOn sl2c_chart_invFun { a | a 2 ≠ 1 } := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.subtype_mk
  have h_cont : Continuous (Set.restrict {a | a 2 ≠ 1} sl2c_chart_at_id) := by
    exact continuousOn_iff_continuous_restrict.mp (fun a ha => (sl2c_chart_at_id_analytic a ha).continuousAt.continuousWithinAt)
  have h_eq : Continuous (fun x : {a | a 2 ≠ 1} => sl2c_chart_at_id x.val) := h_cont
  exact Continuous.congr h_eq (fun x => (sl2c_chart_invFun_eq x.prop).symm)

noncomputable def sl2c_chart_at_id_open_homeomorph :
    OpenPartialHomeomorph (SpecialLinearGroup (Fin 2) ℂ) (Fin 3 → ℂ) where
  toFun A := sl2c_chart_inv A.1
  invFun a := sl2c_chart_invFun a
  source := { A | A.1 1 1 ≠ 0 }
  target := { a | a 2 ≠ 1 }
  map_source' A hA := by
    dsimp at hA ⊢
    dsimp [sl2c_chart_inv]
    intro h
    have h1 : A.1 1 1 = 0 := by
      calc A.1 1 1 = 1 - (1 - A.1 1 1) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
    contradiction
  map_target' a ha := by
    dsimp at ha ⊢
    have heq := sl2c_chart_invFun_eq ha
    have h_eval : (sl2c_chart_invFun a).1 1 1 = sl2c_chart_at_id a 1 1 := congrFun (congrFun heq 1) 1
    rw [h_eval]
    dsimp [sl2c_chart_at_id, sigma_1, sigma_2, sigma_3]
    intro h
    have h1 : a 2 = 1 := by
      calc a 2 = 1 - (1 - a 2) := by ring
      _ = 1 - 0 := by rw [h]
      _ = 1 := by ring
    contradiction
  left_inv' A hA := by
    dsimp at hA ⊢
    have h_a2 : sl2c_chart_inv A.1 2 ≠ 1 := by
      dsimp [sl2c_chart_inv]
      intro h
      have h1 : A.1 1 1 = 0 := by
        calc A.1 1 1 = 1 - (1 - A.1 1 1) := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by ring
      contradiction
    ext i j
    have heq := sl2c_chart_invFun_eq h_a2
    have h_eval : (sl2c_chart_invFun (sl2c_chart_inv A.1)).1 i j = sl2c_chart_at_id (sl2c_chart_inv A.1) i j := congrFun (congrFun heq i) j
    rw [h_eval]
    have h_eq2 := sl2c_chart_inv_right_inv A.1 A.2 hA
    exact congrFun (congrFun h_eq2 i) j
  right_inv' a ha := by
    dsimp at ha ⊢
    have heq := sl2c_chart_invFun_eq ha
    have hext : (sl2c_chart_invFun a).1 = sl2c_chart_at_id a := heq
    have h_eq2 := sl2c_chart_inv_left_inv a
    
    rw [hext]
    exact h_eq2
  open_source := by
    have h1 : Continuous (fun A : SpecialLinearGroup (Fin 2) ℂ => A.1 1 1) := by fun_prop
    exact isOpen_ne_fun h1 continuous_const
  open_target := by
    have h1 : Continuous (fun a : Fin 3 → ℂ => a 2) := by fun_prop
    exact isOpen_ne_fun h1 continuous_const
  continuousOn_toFun := by
    have h1 : Continuous (fun A : SpecialLinearGroup (Fin 2) ℂ => sl2c_chart_inv A.1) :=
      sl2c_chart_inv_continuous.comp continuous_subtype_val
    exact h1.continuousOn
  continuousOn_invFun := continuousOn_invFun_aux

noncomputable def sl2c_chartAt (B : SpecialLinearGroup (Fin 2) ℂ) :
    OpenPartialHomeomorph (SpecialLinearGroup (Fin 2) ℂ) (Fin 3 → ℂ) :=
  (Homeomorph.mulLeft B⁻¹).toOpenPartialHomeomorph.trans sl2c_chart_at_id_open_homeomorph

noncomputable instance : ChartedSpace (Fin 3 → ℂ) (SpecialLinearGroup (Fin 2) ℂ) where
  atlas := Set.range sl2c_chartAt
  chartAt := sl2c_chartAt
  mem_chart_source B := by
    dsimp [sl2c_chartAt, OpenPartialHomeomorph.trans]
    have h : (B⁻¹ * B).1 1 1 ≠ 0 := by
      rw [inv_mul_cancel]
      exact one_ne_zero
    exact ⟨Set.mem_univ B, h⟩
  chart_mem_atlas B := Set.mem_range_self B

open scoped Manifold

lemma sl2c_chart_transition_eq (B B' : SpecialLinearGroup (Fin 2) ℂ) (a : Fin 3 → ℂ) :
    ((sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B')).toFun a =
    sl2c_chart_inv ((B'⁻¹ * (B * sl2c_chart_invFun a)).1) := by
  change sl2c_chart_inv (B'⁻¹ * ((B⁻¹)⁻¹ * sl2c_chart_invFun a)).1 = _
  rw [inv_inv B]

lemma analyticAt_matrix_mulRight (A : Matrix (Fin 2) (Fin 2) ℂ) (M₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    AnalyticAt ℂ (fun M => M * A) M₀ := by
  let H := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ A)
  have h_eq : (fun M => M * A) = ⇑H := rfl
  rw [h_eq]
  exact H.analyticAt M₀

lemma sl2c_inv_eq_adjugate (M : SpecialLinearGroup (Fin 2) ℂ) : (M⁻¹).1 = adjugate M.1 := by
  have h1 : M.1 * adjugate M.1 = 1 := by rw [Matrix.mul_adjugate, M.2, one_smul]
  have h3 : (M⁻¹).1 * M.1 = 1 := by exact congrArg Subtype.val (inv_mul_cancel M)
  calc (M⁻¹).1 = (M⁻¹).1 * 1 := by rw [Matrix.mul_one]
    _ = (M⁻¹).1 * (M.1 * adjugate M.1) := by rw [← h1]
    _ = ((M⁻¹).1 * M.1) * adjugate M.1 := by rw [Matrix.mul_assoc]
    _ = 1 * adjugate M.1 := by rw [h3]
    _ = adjugate M.1 := by rw [Matrix.one_mul]

lemma sl2c_chart_transition_analytic (B B' : SpecialLinearGroup (Fin 2) ℂ) :
    ContDiffOn ℂ ω (𝓘(ℂ, Fin 3 → ℂ) ∘ (sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B') ∘ 𝓘(ℂ, Fin 3 → ℂ).symm)
    (𝓘(ℂ, Fin 3 → ℂ).symm ⁻¹' ((sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B')).source ∩ Set.range 𝓘(ℂ, Fin 3 → ℂ)) := by
  apply AnalyticOn.contDiffOn
  · intro a ha
    dsimp [Set.mem_inter_iff, Set.mem_preimage, OpenPartialHomeomorph.trans_source] at ha
    have ha2 : a 2 ≠ 1 := by
      exact ha.1.1.1
    have H_base : AnalyticAt ℂ (fun x => sl2c_chart_inv ((B'⁻¹).1 * (B.1 * sl2c_chart_at_id x))) a := by
      have h_inv : ∀ M, AnalyticAt ℂ sl2c_chart_inv M := by
        intro M
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact AnalyticAt.div (AnalyticAt.add (analyticAt_matrix_proj 0 1 M) (analyticAt_matrix_proj 1 0 M)) analyticAt_const (by norm_num)
        · exact AnalyticAt.div (AnalyticAt.sub (analyticAt_matrix_proj 1 0 M) (analyticAt_matrix_proj 0 1 M)) analyticAt_const (by simp [I_ne_zero])
        · exact AnalyticAt.sub analyticAt_const (analyticAt_matrix_proj 1 1 M)
      have h_mul1 : ∀ M, AnalyticAt ℂ (fun M : Matrix (Fin 2) (Fin 2) ℂ => (B'⁻¹).1 * M) M := by
        intro M
        exact analyticAt_matrix_mulLeft (B'⁻¹).1 M
      have h_mul2 : ∀ M, AnalyticAt ℂ (fun M : Matrix (Fin 2) (Fin 2) ℂ => B.1 * M) M := by
        intro M
        exact analyticAt_matrix_mulLeft B.1 M
      have h_id := sl2c_chart_at_id_analytic a ha2
      exact (h_inv _).comp ((h_mul1 _).comp ((h_mul2 _).comp h_id))
    have H_at := H_base.analyticWithinAt (s := 𝓘(ℂ, Fin 3 → ℂ).symm ⁻¹' ((sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B')).source ∩ Set.range 𝓘(ℂ, Fin 3 → ℂ))
    apply H_at.congr
    · intro x hx
      dsimp [Set.mem_inter_iff, Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hx
      have hx2 : x 2 ≠ 1 := by exact hx.1.1.1
      have h_eq1 := sl2c_chart_transition_eq B B' x
      have h_eq2 : (sl2c_chart_invFun x).1 = sl2c_chart_at_id x := sl2c_chart_invFun_eq hx2
      change _ = sl2c_chart_inv ((B'⁻¹).1 * (B.1 * (sl2c_chart_invFun x).1)) at h_eq1
      rw [h_eq2] at h_eq1
      change ((sl2c_chartAt B).symm ≫ₕ sl2c_chartAt B') x = sl2c_chart_inv ((B'⁻¹).1 * (B.1 * sl2c_chart_at_id x))
      exact h_eq1
    · dsimp
      have h_eq1 := sl2c_chart_transition_eq B B' a
      have h_eq2 : (sl2c_chart_invFun a).1 = sl2c_chart_at_id a := sl2c_chart_invFun_eq ha2
      change _ = sl2c_chart_inv ((B'⁻¹).1 * (B.1 * (sl2c_chart_invFun a).1)) at h_eq1
      rw [h_eq2] at h_eq1
      change ((sl2c_chartAt B).symm ≫ₕ sl2c_chartAt B') a = sl2c_chart_inv ((B'⁻¹).1 * (B.1 * sl2c_chart_at_id a))
      exact h_eq1
  · have h1 : IsOpen (((sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B')).source) := ((sl2c_chartAt B).symm ≫ₕ (sl2c_chartAt B')).open_source
    have h2 : Continuous 𝓘(ℂ, Fin 3 → ℂ).symm := 𝓘(ℂ, Fin 3 → ℂ).continuous_symm
    have h3 := h1.preimage h2
    have h4 : Set.range 𝓘(ℂ, Fin 3 → ℂ) = Set.univ := by
      exact Set.eq_univ_of_forall (fun x => ⟨x, rfl⟩)
    rw [h4]
    exact (h3.inter isOpen_univ).uniqueDiffOn

lemma contDiff_adjugate_fin_two : ContDiff ℂ ω (adjugate : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) := by
  have H_eq : (adjugate : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) = fun M => !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
    ext M i j
    exact congrFun (congrFun (adjugate_fin_two M) i) j
  rw [H_eq]
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  fin_cases i <;> fin_cases j
  · change ContDiff ℂ ω (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    let P_1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
    let P_1' : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
    exact (P_1'.comp P_1).contDiff
  · change ContDiff ℂ ω (fun M : Matrix (Fin 2) (Fin 2) ℂ => -M 0 1)
    let P_0 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
    let P_1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
    apply ContDiff.neg
    exact (P_1.comp P_0).contDiff
  · change ContDiff ℂ ω (fun M : Matrix (Fin 2) (Fin 2) ℂ => -M 1 0)
    let P_1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
    let P_0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
    apply ContDiff.neg
    exact (P_0.comp P_1).contDiff
  · change ContDiff ℂ ω (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    let P_0 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
    let P_0' : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
    exact (P_0'.comp P_0).contDiff

lemma contDiff_sl2c_chart_inv : ContDiff ℂ ω sl2c_chart_inv := by
  let P_0 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
  let P_1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
  let P_0' : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 0
  let P_1' : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) 1
  let M00 := P_0'.comp P_0
  let M01 := P_1'.comp P_0
  let M10 := P_0'.comp P_1
  let M11 := P_1'.comp P_1

  apply contDiff_pi.mpr; intro i
  fin_cases i
  · 
    change ContDiff ℂ ω (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 1 + A 1 0) / 2)
    apply ContDiff.div_const
    apply ContDiff.add
    · exact M01.contDiff
    · exact M10.contDiff
  · 
    change ContDiff ℂ ω (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 0 - A 0 1) / (2 * I))
    apply ContDiff.div_const
    apply ContDiff.sub
    · exact M10.contDiff
    · exact M01.contDiff
  · 
    change ContDiff ℂ ω (fun A : Matrix (Fin 2) (Fin 2) ℂ => 1 - A 1 1)
    apply ContDiff.sub
    · exact contDiff_const
    · exact M11.contDiff

noncomputable instance sl2c_isManifold : IsManifold 𝓘(ℂ, Fin 3 → ℂ) ω (SpecialLinearGroup (Fin 2) ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  dsimp [atlas, ChartedSpace.atlas] at he he'
  rcases he with ⟨B, hB⟩
  rcases he' with ⟨B', hB'⟩
  rw [← hB, ← hB']
  exact sl2c_chart_transition_analytic B B'

lemma sl2c_chartAt_apply (B : SpecialLinearGroup (Fin 2) ℂ) (M : SpecialLinearGroup (Fin 2) ℂ) :
    sl2c_chartAt B M = sl2c_chart_inv (B⁻¹ * M).1 := rfl

lemma sl2c_chartAt_symm_apply (B : SpecialLinearGroup (Fin 2) ℂ) (a : Fin 3 → ℂ) :
    (sl2c_chartAt B).symm a = B * sl2c_chart_invFun a := by
  dsimp [sl2c_chartAt, OpenPartialHomeomorph.trans, PartialEquiv.trans]
  change (B⁻¹)⁻¹ * sl2c_chart_invFun a = B * sl2c_chart_invFun a
  rw [inv_inv]

lemma sl2c_chart_inv_transition_eq (B B' : SpecialLinearGroup (Fin 2) ℂ) (x : Fin 3 → ℂ) (hx : x 2 ≠ 1) :
    (sl2c_chartAt B' ((sl2c_chartAt B).symm x)⁻¹) = sl2c_chart_inv ((B'⁻¹).1 * (adjugate (sl2c_chart_at_id x) * (B⁻¹).1)) := by
  rw [sl2c_chartAt_symm_apply, sl2c_chartAt_apply]
  congr 1
  have h_inv : (B * sl2c_chart_invFun x)⁻¹.1 = ((sl2c_chart_invFun x)⁻¹ * B⁻¹).1 := by
    exact congrArg Subtype.val (mul_inv_rev B (sl2c_chart_invFun x))
  have h_adj : (sl2c_chart_invFun x)⁻¹.1 = adjugate (sl2c_chart_invFun x).1 := sl2c_inv_eq_adjugate _
  have h_chart : (sl2c_chart_invFun x).1 = sl2c_chart_at_id x := sl2c_chart_invFun_eq hx
  have h1 : (B'⁻¹ * (B * sl2c_chart_invFun x)⁻¹).1 = (B'⁻¹).1 * (B * sl2c_chart_invFun x)⁻¹.1 := rfl
  have h2 : ((sl2c_chart_invFun x)⁻¹ * B⁻¹).1 = (sl2c_chart_invFun x)⁻¹.1 * (B⁻¹).1 := rfl
  rw [h1, h_inv, h2, h_adj, h_chart]

lemma extChartAt_eq (B : SpecialLinearGroup (Fin 2) ℂ) :
    extChartAt 𝓘(ℂ, Fin 3 → ℂ) B = (sl2c_chartAt B).toPartialEquiv := by
  dsimp [extChartAt, modelWithCornersSelf]
  exact PartialEquiv.trans_refl _

lemma analyticAt_matrix_mulLeft_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Matrix (Fin 2) (Fin 2) ℂ) {f : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun x => M * f x) x := by
  have H : AnalyticAt ℂ (fun M' => M * M') (f x) := analyticAt_matrix_mulLeft M (f x)
  exact H.comp hf

lemma analyticAt_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun x => f x * g x) x := by
  have hf_comp : ∀ i j, AnalyticAt ℂ (fun x => f x i j) x := fun i j => analyticAt_matrix_proj i j _ |>.comp hf
  have hg_comp : ∀ i j, AnalyticAt ℂ (fun x => g x i j) x := fun i j => analyticAt_matrix_proj i j _ |>.comp hg
  apply AnalyticAt.pi; intro i
  apply AnalyticAt.pi; intro j
  simp only [Matrix.mul_apply]
  let k0 : Fin 2 := 0
  let k1 : Fin 2 := 1
  have h_sum : (fun x => ∑ k : Fin 2, f x i k * g x k j) = fun x => (f x i k0 * g x k0 j) + (f x i k1 * g x k1 j) := by
    ext y; rw [Fin.sum_univ_two]
  rw [h_sum]
  apply AnalyticAt.add
  · exact (hf_comp i k0).mul (hg_comp k0 j)
  · exact (hf_comp i k1).mul (hg_comp k1 j)

lemma sl2c_chart_mul_transition_eq (B B' B'' : SpecialLinearGroup (Fin 2) ℂ) (x y : Fin 3 → ℂ) (hx : x 2 ≠ 1) (hy : y 2 ≠ 1) :
    sl2c_chartAt B'' ((sl2c_chartAt B).symm x * (sl2c_chartAt B').symm y) =
    sl2c_chart_inv ((B''⁻¹).1 * ((B.1 * sl2c_chart_at_id x) * (B'.1 * sl2c_chart_at_id y))) := by
  rw [sl2c_chartAt_symm_apply B x, sl2c_chartAt_symm_apply B' y, sl2c_chartAt_apply]
  congr 1
  have h_chart_x : (sl2c_chart_invFun x).1 = sl2c_chart_at_id x := sl2c_chart_invFun_eq hx
  have h_chart_y : (sl2c_chart_invFun y).1 = sl2c_chart_at_id y := sl2c_chart_invFun_eq hy
  have h1 : (B''⁻¹ * (B * sl2c_chart_invFun x * (B' * sl2c_chart_invFun y))).1 =
      (B''⁻¹).1 * ((B.1 * (sl2c_chart_invFun x).1) * (B'.1 * (sl2c_chart_invFun y).1)) := by
    change (B''⁻¹).1 * ((B.1 * (sl2c_chart_invFun x).1) * (B'.1 * (sl2c_chart_invFun y).1)) = _
    rfl
  rw [h1, h_chart_x, h_chart_y]

lemma uniqueDiffOn_mul (B B' B'' : SpecialLinearGroup (Fin 2) ℂ) :
    UniqueDiffOn ℂ (((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.target ∩ ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.symm ⁻¹' (fun p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ => p.1 * p.2) ⁻¹' (sl2c_chartAt B'').toPartialEquiv.source) := by
  have H_target_open : IsOpen ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.target := ((sl2c_chartAt B).prod (sl2c_chartAt B')).open_target
  have H_source_open : IsOpen (sl2c_chartAt B'').toPartialEquiv.source := (sl2c_chartAt B'').open_source
  have H_cont_symm : ContinuousOn ((sl2c_chartAt B).prod (sl2c_chartAt B')).symm ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.target := ((sl2c_chartAt B).prod (sl2c_chartAt B')).continuousOn_symm
  have H_cont_mul : Continuous (fun p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ => p.1 * p.2) := continuous_mul
  have H_cont := Continuous.comp_continuousOn H_cont_mul H_cont_symm
  have H_inter_open := ContinuousOn.isOpen_inter_preimage H_cont H_target_open H_source_open
  exact H_inter_open.uniqueDiffOn

lemma sl2c_chartAt_target_eq (B : SpecialLinearGroup (Fin 2) ℂ) : (sl2c_chartAt B).target = { a | a 2 ≠ 1 } := by
  ext a
  simp [sl2c_chartAt, sl2c_chart_at_id_open_homeomorph]

lemma my_analyticAt_fst {p : (Fin 3 → ℂ) × (Fin 3 → ℂ)} :
    AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1) p :=
  (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ)).analyticAt p

lemma sl2c_chart_at_id_fst_analytic (x y : Fin 3 → ℂ) (hx2 : x 2 ≠ 1) :
    AnalyticAt ℂ (sl2c_chart_at_id ∘ fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1) (x, y) := by
  have h1 : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1) (x, y) := my_analyticAt_fst
  have h2 : AnalyticAt ℂ sl2c_chart_at_id ((fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1) (x, y)) := sl2c_chart_at_id_analytic x hx2
  exact AnalyticAt.comp h2 h1

lemma my_analyticAt_snd {p : (Fin 3 → ℂ) × (Fin 3 → ℂ)} :
    AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2) p :=
  (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ)).analyticAt p

lemma sl2c_chart_at_id_snd_analytic (x y : Fin 3 → ℂ) (hy2 : y 2 ≠ 1) :
    AnalyticAt ℂ (sl2c_chart_at_id ∘ fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2) (x, y) := by
  have h1 : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2) (x, y) := my_analyticAt_snd
  have h2 : AnalyticAt ℂ sl2c_chart_at_id ((fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2) (x, y)) := sl2c_chart_at_id_analytic y hy2
  exact AnalyticAt.comp h2 h1

noncomputable instance : LieGroup 𝓘(ℂ, Fin 3 → ℂ) ω (SpecialLinearGroup (Fin 2) ℂ) where
  contMDiff_mul := by
    rw [contMDiff_iff]
    refine ⟨continuous_mul, fun p B'' => ?_⟩
    rcases p with ⟨B, B'⟩
    have H_extChart_x : extChartAt 𝓘(ℂ, Fin 3 → ℂ) B = (sl2c_chartAt B).toPartialEquiv := extChartAt_eq B
    have H_extChart_y : extChartAt 𝓘(ℂ, Fin 3 → ℂ) B' = (sl2c_chartAt B').toPartialEquiv := extChartAt_eq B'
    have H_extChart_z : extChartAt 𝓘(ℂ, Fin 3 → ℂ) B'' = (sl2c_chartAt B'').toPartialEquiv := extChartAt_eq B''
    have H_extChart_prod : extChartAt (𝓘(ℂ, Fin 3 → ℂ).prod 𝓘(ℂ, Fin 3 → ℂ)) (B, B') = ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv := by
      change extChartAt (𝓘(ℂ, Fin 3 → ℂ).prod 𝓘(ℂ, Fin 3 → ℂ)) (B, B') = ((sl2c_chartAt B).toPartialEquiv.prod (sl2c_chartAt B').toPartialEquiv)
      rw [extChartAt_prod, H_extChart_x, H_extChart_y]
    rw [H_extChart_prod, H_extChart_z]
    apply AnalyticOn.contDiffOn
    intro ⟨x, y⟩ hxy
    have hx_in : x ∈ (sl2c_chartAt B).target := hxy.1.1
    have hy_in : y ∈ (sl2c_chartAt B').target := hxy.1.2
    have hx2 : x 2 ≠ 1 := by rw [sl2c_chartAt_target_eq B] at hx_in; exact hx_in
    have hy2 : y 2 ≠ 1 := by rw [sl2c_chartAt_target_eq B'] at hy_in; exact hy_in
    have H_base : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => sl2c_chart_inv ((B''⁻¹).1 * ((B.1 * sl2c_chart_at_id p.1) * (B'.1 * sl2c_chart_at_id p.2)))) (x, y) := by
      have h_inv : ∀ M, AnalyticAt ℂ sl2c_chart_inv M := by
        intro M
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact AnalyticAt.div (AnalyticAt.add (analyticAt_matrix_proj 0 1 M) (analyticAt_matrix_proj 1 0 M)) analyticAt_const (by norm_num)
        · exact AnalyticAt.div (AnalyticAt.sub (analyticAt_matrix_proj 1 0 M) (analyticAt_matrix_proj 0 1 M)) analyticAt_const (by simp [I_ne_zero])
        · exact AnalyticAt.sub analyticAt_const (analyticAt_matrix_proj 1 1 M)
      have h1 : AnalyticAt ℂ (sl2c_chart_at_id ∘ fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1) (x, y) := sl2c_chart_at_id_fst_analytic x y hx2
      have h2 : AnalyticAt ℂ (sl2c_chart_at_id ∘ fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2) (x, y) := sl2c_chart_at_id_snd_analytic x y hy2
      have h_B1 : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => B.1 * (sl2c_chart_at_id ∘ fun p => p.1) p) (x, y) := analyticAt_matrix_mulLeft_comp B.1 h1
      have h_B2 : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => B'.1 * (sl2c_chart_at_id ∘ fun p => p.2) p) (x, y) := analyticAt_matrix_mulLeft_comp B'.1 h2
      have h_mul := analyticAt_matrix_mul h_B1 h_B2
      have h_fin : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => (B''⁻¹).1 * ((B.1 * (sl2c_chart_at_id ∘ fun p => p.1) p) * (B'.1 * (sl2c_chart_at_id ∘ fun p => p.2) p))) (x, y) := analyticAt_matrix_mulLeft_comp (B''⁻¹).1 h_mul
      have h_fin' : AnalyticAt ℂ (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => (B''⁻¹).1 * ((B.1 * sl2c_chart_at_id p.1) * (B'.1 * sl2c_chart_at_id p.2))) (x, y) := h_fin
      exact (h_inv _).comp h_fin'
    have H_at := H_base.analyticWithinAt (s := ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.target ∩ ((sl2c_chartAt B).prod (sl2c_chartAt B')).toPartialEquiv.symm ⁻¹' (fun p => p.1 * p.2) ⁻¹' (sl2c_chartAt B'').toPartialEquiv.source)
    apply H_at.congr
    · intro ⟨x', y'⟩ hx'y'
      have hx_in' : x' ∈ (sl2c_chartAt B).target := hx'y'.1.1
      have hy_in' : y' ∈ (sl2c_chartAt B').target := hx'y'.1.2
      have hx2' : x' 2 ≠ 1 := by rw [sl2c_chartAt_target_eq B] at hx_in'; exact hx_in'
      have hy2' : y' 2 ≠ 1 := by rw [sl2c_chartAt_target_eq B'] at hy_in'; exact hy_in'
      exact sl2c_chart_mul_transition_eq B B' B'' x' y' hx2' hy2'
    · exact sl2c_chart_mul_transition_eq B B' B'' x y hx2 hy2
    · exact uniqueDiffOn_mul B B' B''
  contMDiff_inv := by
    rw [contMDiff_iff]
    refine ⟨continuous_inv, fun B B' => ?_⟩
    have H_extChart_x : extChartAt 𝓘(ℂ, Fin 3 → ℂ) B = (sl2c_chartAt B).toPartialEquiv := extChartAt_eq B
    have H_extChart_y : extChartAt 𝓘(ℂ, Fin 3 → ℂ) B' = (sl2c_chartAt B').toPartialEquiv := extChartAt_eq B'
    rw [H_extChart_x, H_extChart_y]
    apply AnalyticOn.contDiffOn
    intro a ha
    dsimp [Set.mem_inter_iff, Set.mem_preimage, OpenPartialHomeomorph.trans_source] at ha
    have ha2 : a 2 ≠ 1 := by exact ha.1.1
    have H_base : AnalyticAt ℂ (fun x => sl2c_chart_inv ((B'⁻¹).1 * (adjugate (sl2c_chart_at_id x) * (B⁻¹).1))) a := by
      have h_inv : ∀ M, AnalyticAt ℂ sl2c_chart_inv M := by
        intro M
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact AnalyticAt.div (AnalyticAt.add (analyticAt_matrix_proj 0 1 M) (analyticAt_matrix_proj 1 0 M)) analyticAt_const (by norm_num)
        · exact AnalyticAt.div (AnalyticAt.sub (analyticAt_matrix_proj 1 0 M) (analyticAt_matrix_proj 0 1 M)) analyticAt_const (by simp [I_ne_zero])
        · exact AnalyticAt.sub analyticAt_const (analyticAt_matrix_proj 1 1 M)
      have h_mul1 : ∀ M, AnalyticAt ℂ (fun M : Matrix (Fin 2) (Fin 2) ℂ => (B'⁻¹).1 * M) M := by
        intro M
        exact analyticAt_matrix_mulLeft (B'⁻¹).1 M
      have h_mul2 : ∀ M, AnalyticAt ℂ (fun M : Matrix (Fin 2) (Fin 2) ℂ => M * (B⁻¹).1) M := by
        intro M
        exact analyticAt_matrix_mulRight (B⁻¹).1 M
      have h_adj : ∀ M, AnalyticAt ℂ (fun M : Matrix (Fin 2) (Fin 2) ℂ => adjugate M) M := by
        intro M
        exact contDiff_adjugate_fin_two.contDiffAt.analyticAt
      have h_id := sl2c_chart_at_id_analytic a ha2
      exact (h_inv _).comp ((h_mul1 _).comp ((h_mul2 _).comp ((h_adj _).comp h_id)))
    have H_at := H_base.analyticWithinAt (s := ((sl2c_chartAt B).toPartialEquiv.target ∩ (sl2c_chartAt B).toPartialEquiv.symm ⁻¹' (fun A => A⁻¹) ⁻¹' (sl2c_chartAt B').toPartialEquiv.source))
    apply H_at.congr
    · intro x hx
      dsimp [Set.mem_inter_iff, Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hx
      have hx2 : x 2 ≠ 1 := by exact hx.1.1
      exact sl2c_chart_inv_transition_eq B B' x hx2
    · exact sl2c_chart_inv_transition_eq B B' a ha2
    have h1 : IsOpen (((sl2c_chartAt B).symm ≫ₕ (Homeomorph.inv (SpecialLinearGroup (Fin 2) ℂ)).toOpenPartialHomeomorph ≫ₕ (sl2c_chartAt B')).source) :=
      OpenPartialHomeomorph.open_source _
    have h2 : (((sl2c_chartAt B).symm ≫ₕ (Homeomorph.inv (SpecialLinearGroup (Fin 2) ℂ)).toOpenPartialHomeomorph ≫ₕ (sl2c_chartAt B')).source) =
        ((sl2c_chartAt B).toPartialEquiv.target ∩ (sl2c_chartAt B).toPartialEquiv.symm ⁻¹' (fun A => A⁻¹) ⁻¹' (sl2c_chartAt B').toPartialEquiv.source) := by
      ext x
      simp [Set.mem_inter_iff, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph]
    rw [← h2]
    exact h1.uniqueDiffOn

end Geometry
