import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Real.Sqrt
import Minkowski
import Mathlib.Topology.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic

namespace Geometry
open Set Matrix Complex

def closed_forward_light_cone : Set (Fin 4 → ℝ) :=
  { x | x 0 ≥ 0 ∧ minkowskiInner x x ≥ 0 }

lemma continuous_minkowskiInner_diag : Continuous (fun (x : Fin 4 → ℝ) => minkowskiInner x x) := by
  simp_rw [minkowskiInner_explicit]
  have h0 : Continuous (fun (x : Fin 4 → ℝ) => x 0 * x 0) := (continuous_apply 0).mul (continuous_apply 0)
  have h1 : Continuous (fun (x : Fin 4 → ℝ) => x 1 * x 1) := (continuous_apply 1).mul (continuous_apply 1)
  have h2 : Continuous (fun (x : Fin 4 → ℝ) => x 2 * x 2) := (continuous_apply 2).mul (continuous_apply 2)
  have h3 : Continuous (fun (x : Fin 4 → ℝ) => x 3 * x 3) := (continuous_apply 3).mul (continuous_apply 3)
  exact ((h0.sub h1).sub h2).sub h3

lemma closed_forward_light_cone_isClosed : IsClosed closed_forward_light_cone := by
  have h1 : IsClosed { x : Fin 4 → ℝ | x 0 ≥ 0 } := isClosed_Ici.preimage (continuous_apply 0)
  have h2 : IsClosed { x : Fin 4 → ℝ | minkowskiInner x x ≥ 0 } := isClosed_Ici.preimage continuous_minkowskiInner_diag
  exact h1.inter h2


lemma closed_forward_light_cone_inner_nonneg {x y : Fin 4 → ℝ}
  (hx : x ∈ closed_forward_light_cone) (hy : y ∈ closed_forward_light_cone) :
  minkowskiInner x y ≥ 0 := by
  have hx0 : x 0 ≥ 0 := hx.1
  have hy0 : y 0 ≥ 0 := hy.1
  have hxx : minkowskiInner x x ≥ 0 := hx.2
  have hyy : minkowskiInner y y ≥ 0 := hy.2
  rw [minkowskiInner_explicit] at hxx hyy ⊢
  have hxx2 : (x 0)^2 ≥ (x 1)^2 + (x 2)^2 + (x 3)^2 := by linarith
  have hyy2 : (y 0)^2 ≥ (y 1)^2 + (y 2)^2 + (y 3)^2 := by linarith
  have hA : (x 1)^2 + (x 2)^2 + (x 3)^2 ≥ 0 := by positivity
  have hB : (y 1)^2 + (y 2)^2 + (y 3)^2 ≥ 0 := by positivity
  have h_prod : (x 0)^2 * (y 0)^2 ≥ ((x 1)^2 + (x 2)^2 + (x 3)^2) * ((y 1)^2 + (y 2)^2 + (y 3)^2) := by nlinarith
  have hCS := cauchy_schwarz_3 (x 1) (x 2) (x 3) (y 1) (y 2) (y 3)
  have h_sq : (x 0 * y 0)^2 ≥ (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)^2 := by linarith
  have h_xy0 : x 0 * y 0 ≥ 0 := mul_nonneg hx0 hy0
  have h_diff : (x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)) * (x 0 * y 0 + (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)) ≥ 0 := by
    calc
      _ = (x 0 * y 0)^2 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)^2 := by ring
      _ ≥ 0 := by linarith
  rcases mul_nonneg_iff.mp h_diff with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · have h_contra : x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3) ≥ 0 := by linarith
    linarith

lemma closed_forward_light_cone_convex : Convex ℝ closed_forward_light_cone := by
  intro x hx y hy a b ha hb hab
  dsimp [closed_forward_light_cone] at *
  constructor
  · have hx0 : x 0 ≥ 0 := hx.1
    have hy0 : y 0 ≥ 0 := hy.1
    change a * x 0 + b * y 0 ≥ 0
    positivity
  · have hxx : minkowskiInner x x ≥ 0 := hx.2
    have hyy : minkowskiInner y y ≥ 0 := hy.2
    have hxy : minkowskiInner x y ≥ 0 := closed_forward_light_cone_inner_nonneg hx hy
    have eq1 : minkowskiInner (a • x + b • y) (a • x + b • y) =
      a^2 * minkowskiInner x x + b^2 * minkowskiInner y y + 2 * a * b * minkowskiInner x y := by
      rw [minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit]
      dsimp
      ring
    rw [eq1]
    positivity


open Real

lemma forward_lightcone_self_dual (u : Fin 4 → ℝ)
  (h_dual : ∀ y ∈ closed_forward_light_cone, minkowskiInner u y ≥ 0) :
  u ∈ closed_forward_light_cone := by
  dsimp [closed_forward_light_cone]
  let y0 : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0
  have hy0 : y0 ∈ closed_forward_light_cone := by
    dsimp [closed_forward_light_cone]
    constructor
    · simp [y0]
    · simp [y0, minkowskiInner_explicit]
  have hu0 := h_dual y0 hy0
  have hu0_eq : minkowskiInner u y0 = u 0 := by
    simp [y0, minkowskiInner_explicit]
  rw [hu0_eq] at hu0
  constructor
  · exact hu0
  · by_contra h_neg
    have h_neg' := not_le.mp h_neg
    have h_space : u 0 ^ 2 < u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
      rw [minkowskiInner_explicit] at h_neg'
      have h1 : u 0 ^ 2 = u 0 * u 0 := by ring
      have h2 : u 1 ^ 2 = u 1 * u 1 := by ring
      have h3 : u 2 ^ 2 = u 2 * u 2 := by ring
      have h4 : u 3 ^ 2 = u 3 * u 3 := by ring
      linarith
    let S := u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2
    have hS : S ≥ 0 := by positivity
    have hS_pos : S > 0 := by
      calc
        0 ≤ u 0 ^ 2 := sq_nonneg (u 0)
        _ < S := h_space
    let y : Fin 4 → ℝ := fun i => if i = 0 then Real.sqrt S else u i
    have hy : y ∈ closed_forward_light_cone := by
      dsimp [closed_forward_light_cone]
      constructor
      · simp [y]
      · simp [y, minkowskiInner_explicit, S]
        have h_sqrt : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS
        linarith
    have huy := h_dual y hy
    have huy_eq : minkowskiInner u y = u 0 * Real.sqrt S - S := by
      simp [y, minkowskiInner_explicit, S]
      ring
    rw [huy_eq] at huy
    have h_u0_sqrt : u 0 * Real.sqrt S ≥ S := by linarith
    have h_sqrt_pos : Real.sqrt S > 0 := Real.sqrt_pos.mpr hS_pos
    have h_u0_ge : Real.sqrt S ≤ u 0 := by
      have h1 : Real.sqrt S * Real.sqrt S ≤ u 0 * Real.sqrt S := by
        calc
          Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS
          _ ≤ u 0 * Real.sqrt S := h_u0_sqrt
      exact le_of_mul_le_mul_right h1 h_sqrt_pos
    have h_u0_sq_ge : S ≤ u 0 ^ 2 := by
      have h2 : (Real.sqrt S)^2 ≤ u 0 ^ 2 := by nlinarith [h_u0_ge]
      rwa [Real.sq_sqrt hS] at h2
    linarith


lemma exists_minkowskiInner_eq_apply (f : (Fin 4 → ℝ) →L[ℝ] ℝ) : ∃ u : Fin 4 → ℝ, ∀ x, f x = minkowskiInner u x := by
  let e (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0
  let u : Fin 4 → ℝ := fun i => if i = 0 then f (e 0) else - f (e i)
  use u
  intro x
  have h_x : x = ∑ i : Fin 4, (x i) • (e i) := by
    ext j
    simp [e, smul_eq_mul]
  have h_fx : f x = ∑ i : Fin 4, x i * f (e i) := by
    nth_rw 1 [h_x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h_smul : f (x i • e i) = x i * f (e i) := by
      exact ContinuousLinearMap.map_smul f (x i) (e i)
    rw [h_smul]
  rw [h_fx]
  dsimp [u]
  rw [minkowskiInner_explicit]
  have eq_sum : (∑ i : Fin 4, x i * f (e i)) = x 0 * f (e 0) + x 1 * f (e 1) + x 2 * f (e 2) + x 3 * f (e 3) := by
    repeat rw [Fin.sum_univ_four]
  rw [eq_sum]
  dsimp
  ring

lemma disjoint_K_lightcone (K : Set (Fin 4 → ℝ)) (hK_spacelike : ∀ x ∈ K, is_spacelike x) :
  Disjoint K closed_forward_light_cone := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp
  intro hx hx_cone
  have hinner := hx_cone.2
  have h_space := hK_spacelike x hx
  dsimp [is_spacelike] at h_space
  linarith

lemma separation_hyperplane_exists (K : Set (Fin 4 → ℝ)) (hK_compact : IsCompact K)
  (hK_convex : Convex ℝ K) (hK_spacelike : ∀ x ∈ K, is_spacelike x)
  (hK_nonempty : K.Nonempty) :
  ∃ (u : Fin 4 → ℝ), u ∈ closed_forward_light_cone ∧ ∀ x ∈ K, minkowskiInner u x < 0 := by
  have disj : Disjoint K closed_forward_light_cone := disjoint_K_lightcone K hK_spacelike
  have h_sep := geometric_hahn_banach_compact_closed hK_convex hK_compact closed_forward_light_cone_convex closed_forward_light_cone_isClosed disj
  rcases h_sep with ⟨f, u_val, v_val, hK, huv, hV⟩
  have h_rep := exists_minkowskiInner_eq_apply f
  rcases h_rep with ⟨u, hu⟩
  use u
  have h0_in : (0 : Fin 4 → ℝ) ∈ closed_forward_light_cone := by
    dsimp [closed_forward_light_cone]
    constructor
    · simp
    · simp [minkowskiInner_explicit]
  have hV0 := hV 0 h0_in
  have hf0 : f 0 = 0 := ContinuousLinearMap.map_zero f
  rw [hf0] at hV0
  have hu_val_neg : u_val < 0 := by linarith
  constructor
  · apply forward_lightcone_self_dual
    intro y hy
    by_contra h_neg
    have h_neg' := not_le.mp h_neg
    have huy_eq : f y = minkowskiInner u y := hu y
    have hfy_neg : f y < 0 := by linarith
    let c := (2 * -v_val) / (-f y)
    have hc_pos : c > 0 := div_pos (by linarith) (by linarith)
    let cy : Fin 4 → ℝ := fun i => c * y i
    have hcy_in : cy ∈ closed_forward_light_cone := by
      dsimp [closed_forward_light_cone] at hy ⊢
      constructor
      · exact mul_nonneg (le_of_lt hc_pos) hy.1
      · have h_cy_inner : minkowskiInner cy cy = c^2 * minkowskiInner y y := by
          simp [cy, minkowskiInner_explicit]
          ring
        rw [h_cy_inner]
        exact mul_nonneg (sq_nonneg c) hy.2
    have hV_cy := hV cy hcy_in
    have hf_cy : f cy = c * f y := by
      have h_smul : cy = c • y := by ext i; simp [cy]
      rw [h_smul]
      exact ContinuousLinearMap.map_smul f c y
    rw [hf_cy] at hV_cy
    have hc_fy_eq : c * f y = 2 * v_val := by
      dsimp [c]
      have h_den : -f y ≠ 0 := by linarith
      have h1 : (2 * -v_val) / (-f y) * (-f y) = 2 * -v_val := div_mul_cancel₀ _ h_den
      calc (2 * -v_val) / (-f y) * f y = - ((2 * -v_val) / (-f y) * (-f y)) := by ring
        _ = - (2 * -v_val) := by rw [h1]
        _ = 2 * v_val := by ring
    rw [hc_fy_eq] at hV_cy
    linarith
  · intro x hx
    have hKx := hK x hx
    have hfx_eq : f x = minkowskiInner u x := hu x
    rw [hfx_eq] at hKx
    linarith


lemma exists_strictly_timelike_separator (K : Set (Fin 4 → ℝ)) (hK_compact : IsCompact K)
  (u : Fin 4 → ℝ) (hu : u ∈ closed_forward_light_cone)
  (h_sep : ∀ x ∈ K, minkowskiInner u x < 0) :
  ∃ (w : Fin 4 → ℝ), w 0 > Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) ∧ ∀ x ∈ K, minkowskiInner w x < 0 := by
  by_cases hK_empty : K = ∅
  · use fun i => if i = 0 then 1 else 0
    constructor
    · simp
    · intro x hx
      rw [hK_empty] at hx
      exact False.elim hx
  · have hK_nonempty : K.Nonempty := nonempty_iff_ne_empty.mpr hK_empty
    have h_cont1 : Continuous (fun (x : Fin 4 → ℝ) => minkowskiInner u x) := by
      simp only [minkowskiInner_explicit]
      apply Continuous.sub
      apply Continuous.sub
      apply Continuous.sub
      · exact continuous_const.mul (continuous_apply 0)
      · exact continuous_const.mul (continuous_apply 1)
      · exact continuous_const.mul (continuous_apply 2)
      · exact continuous_const.mul (continuous_apply 3)
    rcases hK_compact.exists_isMaxOn hK_nonempty h_cont1.continuousOn with ⟨x_max, hx_max, h_max⟩
    have h_delta : minkowskiInner u x_max < 0 := h_sep x_max hx_max
    have h_cont2 : Continuous (fun (x : Fin 4 → ℝ) => x 0) := continuous_apply 0
    rcases hK_compact.exists_isMaxOn hK_nonempty h_cont2.continuousOn with ⟨x_max0, hx_max0, h_max0⟩
    let M := max (x_max0 0) 0
    let delta := - minkowskiInner u x_max
    have h_delta_pos : delta > 0 := neg_pos.mpr h_delta
    let eps := delta / (M + 1)
    have heps_pos : eps > 0 := div_pos h_delta_pos (by linarith [le_max_right (x_max0 0) 0])
    let w : Fin 4 → ℝ := fun i => if i = 0 then u 0 + eps else u i
    use w
    constructor
    · have hu_cone : u 0 ≥ Real.sqrt (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) := by
        have hu0 : u 0 ≥ 0 := hu.1
        have huu : minkowskiInner u u ≥ 0 := hu.2
        rw [minkowskiInner_explicit] at huu
        have h_sq : u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 ≤ u 0 ^ 2 := by linarith
        exact (Real.sqrt_le_iff.mpr ⟨hu0, h_sq⟩)
      have hw_eq : Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) = Real.sqrt (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) := rfl
      rw [hw_eq]
      simp [w]
      linarith [hu_cone, heps_pos]
    · intro x hx
      have hw_inner : minkowskiInner w x = minkowskiInner u x + eps * x 0 := by
        rw [minkowskiInner_explicit, minkowskiInner_explicit]
        dsimp [w]
        ring
      rw [hw_inner]
      have hx0_le : x 0 ≤ M := by
        calc
          x 0 ≤ x_max0 0 := h_max0 hx
          _ ≤ M := le_max_left (x_max0 0) 0
      have h_eps_x0 : eps * x 0 ≤ eps * M := mul_le_mul_of_nonneg_left hx0_le (le_of_lt heps_pos)
      have h_eps_M : eps * M < delta := by
        dsimp [eps]
        have h_div : delta / (M + 1) * M < delta := by
          rw [div_mul_eq_mul_div, div_lt_iff₀]
          · linarith
          · linarith [le_max_right (x_max0 0) 0]
        exact h_div
      have h_le : minkowskiInner u x ≤ minkowskiInner u x_max := h_max hx
      linarith



lemma dotProduct_mulVec_left_real (M : Matrix (Fin 4) (Fin 4) ℝ) (v w : Fin 4 → ℝ) :
  dotProduct (M *ᵥ v) w = dotProduct v (Mᵀ *ᵥ w) := by
  dsimp [dotProduct, Matrix.mulVec, Matrix.transpose]
  simp [Fin.sum_univ_four]
  ring

lemma lorentz_preserves_inner (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λᵀ * minkowskiMetricReal * Λ = minkowskiMetricReal) (x y : Fin 4 → ℝ) :
  minkowskiInner (Λ *ᵥ x) (Λ *ᵥ y) = minkowskiInner x y := by
  dsimp [minkowskiInner]
  have h_eq : dotProduct (Λ *ᵥ x) (minkowskiMetricReal *ᵥ (Λ *ᵥ y)) = dotProduct x (Λᵀ *ᵥ ((minkowskiMetricReal * Λ) *ᵥ y)) := by
    have h1 : minkowskiMetricReal *ᵥ (Λ *ᵥ y) = (minkowskiMetricReal * Λ) *ᵥ y := by
      exact Matrix.mulVec_mulVec y minkowskiMetricReal Λ
    rw [h1]
    exact dotProduct_mulVec_left_real Λ x ((minkowskiMetricReal * Λ) *ᵥ y)
  rw [h_eq]
  have h4 : Λᵀ * (minkowskiMetricReal * Λ) = Λᵀ * minkowskiMetricReal * Λ := by
    exact (Matrix.mul_assoc _ _ _).symm
  have h3 : Λᵀ *ᵥ ((minkowskiMetricReal * Λ) *ᵥ y) = (Λᵀ * (minkowskiMetricReal * Λ)) *ᵥ y := by
    exact Matrix.mulVec_mulVec y Λᵀ (minkowskiMetricReal * Λ)
  rw [h3, h4, hΛ]

lemma lorentz_spatial_zero (R : Matrix (Fin 4) (Fin 4) ℝ)
  (hR_lor : Matrix.transpose R * minkowskiMetricReal * R = minkowskiMetricReal)
  (hR_spatial : ∀ y : Fin 4 → ℝ, (R *ᵥ y) 0 = y 0) :
  R 3 0 = 0 := by
  let e0 : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0
  have he0_0 : e0 0 = 1 := by simp [e0]
  have he0_1 : e0 1 = 0 := by simp [e0]
  have he0_2 : e0 2 = 0 := by simp [e0]
  have he0_3 : e0 3 = 0 := by simp [e0]
  have h_inner_e0 : minkowskiInner e0 e0 = 1 := by
    rw [minkowskiInner_explicit]
    simp [he0_0, he0_1, he0_2, he0_3]
  have h_inner_Re0 : minkowskiInner (R *ᵥ e0) (R *ᵥ e0) = 1 := by
    rw [lorentz_preserves_inner R hR_lor e0 e0, h_inner_e0]
  have h_Re0_0 : (R *ᵥ e0) 0 = 1 := by
    rw [hR_spatial e0, he0_0]
  have h_Re0_1 : (R *ᵥ e0) 1 = R 1 0 := by
    change ∑ j, R 1 j * e0 j = R 1 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_Re0_2 : (R *ᵥ e0) 2 = R 2 0 := by
    change ∑ j, R 2 j * e0 j = R 2 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_Re0_3 : (R *ᵥ e0) 3 = R 3 0 := by
    change ∑ j, R 3 j * e0 j = R 3 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_exp : minkowskiInner (R *ᵥ e0) (R *ᵥ e0) = 1 - (R 1 0)^2 - (R 2 0)^2 - (R 3 0)^2 := by
    rw [minkowskiInner_explicit, h_Re0_0, h_Re0_1, h_Re0_2, h_Re0_3]
    ring
  rw [h_exp] at h_inner_Re0
  have h_sum_zero : (R 1 0)^2 + (R 2 0)^2 + (R 3 0)^2 = 0 := by linarith
  have h_3_sq_zero : (R 3 0)^2 = 0 := by linarith [sq_nonneg (R 1 0), sq_nonneg (R 2 0), sq_nonneg (R 3 0)]
  exact sq_eq_zero_iff.mp h_3_sq_zero

lemma matrix_mulVec_three_eq
  (R T : Matrix (Fin 4) (Fin 4) ℝ)
  (h_R30 : R 3 0 = 0)
  (h_T0 : ∀ y, (T *ᵥ y) 0 = -y 0)
  (h_T1 : ∀ y, (T *ᵥ y) 1 = y 1)
  (h_T2 : ∀ y, (T *ᵥ y) 2 = y 2)
  (h_T3 : ∀ y, (T *ᵥ y) 3 = y 3)
  (y : Fin 4 → ℝ) :
  (R *ᵥ (T *ᵥ y)) 3 = (R *ᵥ y) 3 := by
  have h_R_val_T : ∀ a b, (R *ᵥ a) b = ∑ j, R b j * a j := fun a b => rfl
  have h1 : (R *ᵥ (T *ᵥ y)) 3 = R 3 0 * (T *ᵥ y) 0 + R 3 1 * (T *ᵥ y) 1 + R 3 2 * (T *ᵥ y) 2 + R 3 3 * (T *ᵥ y) 3 := by
    rw [h_R_val_T, Fin.sum_univ_four]
  have h2 : (R *ᵥ y) 3 = R 3 0 * y 0 + R 3 1 * y 1 + R 3 2 * y 2 + R 3 3 * y 3 := by
    rw [h_R_val_T, Fin.sum_univ_four]
  rw [h1, h2, h_T0, h_T1, h_T2, h_T3, h_R30]
  ring

lemma exists_lorentz_mapping_K_past
  (K : Set (Fin 4 → ℝ)) (hK_compact : IsCompact K)
  (hK_convex : Convex ℝ K) (hK_spacelike : ∀ x ∈ K, is_spacelike x)
  (hK_nonempty : K.Nonempty) :
  ∃ (Λ : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    (Λ.valᵀ * minkowskiMetricReal * Λ.val = minkowskiMetricReal) ∧
    (Λ.val.det = 1) ∧
    ∀ x ∈ K, (Λ.val *ᵥ x) 0 < 0 := by
  have h_sep := separation_hyperplane_exists K hK_compact hK_convex hK_spacelike hK_nonempty
  rcases h_sep with ⟨u, hu_cone, h_sep_u⟩
  have h_strict_sep := exists_strictly_timelike_separator K hK_compact u hu_cone h_sep_u
  rcases h_strict_sep with ⟨w, hw_space, hw_sep⟩

  have hw_non_spacelike : ¬ is_spacelike w := by
    intro hw_sp
    have hw0_sq : w 0 ^ 2 > w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by
      have h_nonneg : 0 ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
      have h_sq : (Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))^2 < w 0 ^ 2 := by
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
        nlinarith
      rwa [Real.sq_sqrt h_nonneg] at h_sq
    have h_sp_eq : minkowskiInner w w = w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - w 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    change minkowskiInner w w < 0 at hw_sp
    rw [h_sp_eq] at hw_sp
    linarith

  have h_align := lorentz_align_non_spacelike w hw_non_spacelike
  let R := Classical.choose h_align
  have hR := Classical.choose_spec h_align
  have hR_lor := hR.1
  have hR_det := hR.2.1
  have hR_1 := hR.2.2.1
  have hR_2 := hR.2.2.2.1
  have hR_0 := hR.2.2.2.2.1
  have hR_spatial := hR.2.2.2.2.2
  let w' := R.val *ᵥ w

  have hw_inner : minkowskiInner w' w' = minkowskiInner w w := lorentz_preserves_inner R.val hR_lor w w

  have hw_inner_pos : minkowskiInner w w > 0 := by
    have hw0_sq : w 0 ^ 2 > w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by
      have h_nonneg : 0 ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
      have h_sq : (Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))^2 < w 0 ^ 2 := by
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
        nlinarith
      rwa [Real.sq_sqrt h_nonneg] at h_sq
    have h_inner_eq : minkowskiInner w w = w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - w 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    rw [h_inner_eq]
    linarith

  have hw'_inner : w' 0 ^ 2 - w' 3 ^ 2 > 0 := by
    have hw'_inner_pos : minkowskiInner w' w' > 0 := by
      rw [hw_inner]
      exact hw_inner_pos
    have h_exp : minkowskiInner w' w' = w' 0 ^ 2 - w' 1 ^ 2 - w' 2 ^ 2 - w' 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    rw [h_exp] at hw'_inner_pos
    have h_w'1 : w' 1 = 0 := hR_1
    have h_w'2 : w' 2 = 0 := hR_2
    rw [h_w'1, h_w'2] at hw'_inner_pos
    linarith

  have h_w'0_pos : w' 0 > 0 := by
    have h_w'0 : w' 0 = w 0 := hR_0
    rw [h_w'0]
    calc
      0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
      _ < w 0 := hw_space

  let v := w' 3 / w' 0
  have hv : v^2 < 1 := by
    have h_div : v^2 = w' 3 ^ 2 / w' 0 ^ 2 := by
      dsimp [v]
      ring
    rw [h_div, div_lt_iff₀]
    · linarith
    · positivity

  let Bz_val := real_boost_z v
  have hBz_lor : Bz_valᵀ * minkowskiMetricReal * Bz_val = minkowskiMetricReal := real_boost_z_is_lorentz v hv

  let Bz_inv := real_boost_z (-v)
  have hBz_mul_inv : Bz_val * Bz_inv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.mul_apply, Matrix.one_apply]
      rw [Fin.sum_univ_four]
      simp [Bz_val, Bz_inv, real_boost_z]
      try ring_nf
      try {
        have h_den : 1 - v^2 ≠ 0 := by linarith
        have h_den2 : Real.sqrt (1 - v^2) ^ 2 = 1 - v^2 := Real.sq_sqrt (by linarith)
        have h_inv : (Real.sqrt (1 - v ^ 2))⁻¹ ^ 2 = (1 - v ^ 2)⁻¹ := by
          calc (Real.sqrt (1 - v ^ 2))⁻¹ ^ 2
            _ = (Real.sqrt (1 - v ^ 2) ^ 2)⁻¹ := by rw [← inv_pow]
            _ = (1 - v ^ 2)⁻¹ := by rw [h_den2]
        rw [h_inv]
        calc -(v ^ 2 * (1 - v ^ 2)⁻¹) + (1 - v ^ 2)⁻¹
          _ = (1 - v ^ 2) * (1 - v ^ 2)⁻¹ := by ring
          _ = 1 := mul_inv_cancel₀ h_den
      }
    }
  have hBz_inv_mul : Bz_inv * Bz_val = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.mul_apply, Matrix.one_apply]
      rw [Fin.sum_univ_four]
      simp [Bz_val, Bz_inv, real_boost_z]
      try ring_nf
      try {
        have h_den : 1 - v^2 ≠ 0 := by linarith
        have h_den2 : Real.sqrt (1 - v^2) ^ 2 = 1 - v^2 := Real.sq_sqrt (by linarith)
        have h_inv : (Real.sqrt (1 - v ^ 2))⁻¹ ^ 2 = (1 - v ^ 2)⁻¹ := by
          calc (Real.sqrt (1 - v ^ 2))⁻¹ ^ 2
            _ = (Real.sqrt (1 - v ^ 2) ^ 2)⁻¹ := by rw [← inv_pow]
            _ = (1 - v ^ 2)⁻¹ := by rw [h_den2]
        rw [h_inv]
        calc -(v ^ 2 * (1 - v ^ 2)⁻¹) + (1 - v ^ 2)⁻¹
          _ = (1 - v ^ 2) * (1 - v ^ 2)⁻¹ := by ring
          _ = 1 := mul_inv_cancel₀ h_den
      }
    }
  let Bz : Matrix.GeneralLinearGroup (Fin 4) ℝ := ⟨Bz_val, Bz_inv, hBz_mul_inv, hBz_inv_mul⟩

  let Λ := Bz * R
  use Λ
  constructor
  · exact lorentz_mul _ _ hBz_lor hR_lor
  constructor
  · change (Bz.val * R.val).det = 1
    rw [Matrix.det_mul, real_boost_z_det v hv, hR_det, mul_one]
  · intro x hx
    have h_mul : Λ.val = Bz_val * R.val := rfl
    have hΛ_lor : Matrix.transpose Λ.val * minkowskiMetricReal * Λ.val = minkowskiMetricReal := by
      rw [h_mul]
      exact lorentz_mul Bz_val R.val hBz_lor hR_lor
    have hl_inner : minkowskiInner (Λ.val *ᵥ w) (Λ.val *ᵥ x) = minkowskiInner w x := by
      exact lorentz_preserves_inner Λ.val hΛ_lor w x
    have hw_x_neg : minkowskiInner w x < 0 := hw_sep x hx
    have h_inner_neg : minkowskiInner (Λ.val *ᵥ w) (Λ.val *ᵥ x) < 0 := by linarith
    have h_Lam_w : Λ.val *ᵥ w = Bz_val *ᵥ w' := by
      rw [h_mul]
      exact (Matrix.mulVec_mulVec w Bz_val R.val).symm
    have h_inner_neg2 : minkowskiInner (Bz_val *ᵥ w') (Λ.val *ᵥ x) < 0 := by
      rwa [← h_Lam_w]
    have hBz_w'_0 : (Bz_val *ᵥ w') 0 = (1 / Real.sqrt (1 - v ^ 2)) * (w' 0 - v * w' 3) := by
      change (real_boost_z v *ᵥ w') 0 = _
      simp [real_boost_z, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      ring
    have hBz_w'_1 : (Bz_val *ᵥ w') 1 = 0 := by
      change (real_boost_z v *ᵥ w') 1 = _
      simp [real_boost_z, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      exact hR_1
    have hBz_w'_2 : (Bz_val *ᵥ w') 2 = 0 := by
      change (real_boost_z v *ᵥ w') 2 = _
      simp [real_boost_z, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      exact hR_2
    have hBz_w'_3 : (Bz_val *ᵥ w') 3 = 0 := by
      change (real_boost_z v *ᵥ w') 3 = _
      simp [real_boost_z, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      dsimp [v]
      have h_w'0_ne_0 : w' 0 ≠ 0 := by linarith
      have h_div : (w' 3 / w' 0) * w' 0 = w' 3 := div_mul_cancel₀ (w' 3) h_w'0_ne_0
      calc
        -((Real.sqrt (1 - (w' 3 / w' 0) ^ 2))⁻¹ * (w' 3 / w' 0) * w' 0) + (Real.sqrt (1 - (w' 3 / w' 0) ^ 2))⁻¹ * w' 3
          = (Real.sqrt (1 - (w' 3 / w' 0) ^ 2))⁻¹ * (-( (w' 3 / w' 0) * w' 0) + w' 3) := by ring
        _ = (Real.sqrt (1 - (w' 3 / w' 0) ^ 2))⁻¹ * (-w' 3 + w' 3) := by rw [h_div]
        _ = 0 := by ring
    have h_inner_exp : minkowskiInner (Bz_val *ᵥ w') (Λ.val *ᵥ x) = (Bz_val *ᵥ w') 0 * (Λ.val *ᵥ x) 0 := by
      rw [minkowskiInner_explicit]
      rw [hBz_w'_1, hBz_w'_2, hBz_w'_3]
      ring
    have h_c_neg : (Bz_val *ᵥ w') 0 * (Λ.val *ᵥ x) 0 < 0 := by
      rwa [h_inner_exp] at h_inner_neg2
    have h_c_pos : (Bz_val *ᵥ w') 0 > 0 := by
      rw [hBz_w'_0]
      have h_sqrt_pos : 1 / Real.sqrt (1 - v ^ 2) > 0 := by
        apply one_div_pos.mpr
        apply Real.sqrt_pos.mpr
        linarith
      have h_term2_pos : w' 0 - v * w' 3 > 0 := by
        dsimp [v]
        have h_w'0_ne_0 : w' 0 ≠ 0 := by linarith
        have h_eq : w' 0 - (w' 3 / w' 0) * w' 3 = (w' 0 ^ 2 - w' 3 ^ 2) / w' 0 := by
          calc
            w' 0 - (w' 3 / w' 0) * w' 3 = (w' 0 * w' 0) / w' 0 - w' 3 ^ 2 / w' 0 := by
              rw [mul_div_cancel_right₀ (w' 0) h_w'0_ne_0]
              ring
            _ = (w' 0 ^ 2 - w' 3 ^ 2) / w' 0 := by ring
        rw [h_eq]
        exact div_pos hw'_inner h_w'0_pos
      exact mul_pos h_sqrt_pos h_term2_pos
    have h_or := mul_neg_iff.mp h_c_neg
    exact h_or.resolve_right (fun h => not_lt_of_gt h_c_pos h.1) |>.2

lemma spatial_rotation_R_3_0 (R : Matrix.GeneralLinearGroup (Fin 4) ℝ)
  (hR_lor : R.valᵀ * minkowskiMetricReal * R.val = minkowskiMetricReal)
  (hR_spatial : ∀ x, (R.val *ᵥ x) 0 = x 0) :
  R.val 3 0 = 0 := by
  let e0 : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0
  have he0_0 : e0 0 = 1 := by simp [e0]
  have he0_1 : e0 1 = 0 := by simp [e0]
  have he0_2 : e0 2 = 0 := by simp [e0]
  have he0_3 : e0 3 = 0 := by simp [e0]
  have h_inner_e0 : minkowskiInner e0 e0 = 1 := by
    rw [minkowskiInner_explicit]
    simp [he0_0, he0_1, he0_2, he0_3]
  have h_inner_Re0 : minkowskiInner (R.val *ᵥ e0) (R.val *ᵥ e0) = 1 := by
    rw [lorentz_preserves_inner R.val hR_lor e0 e0, h_inner_e0]
  have h_Re0_0 : (R.val *ᵥ e0) 0 = 1 := by
    rw [hR_spatial e0, he0_0]
  have h_Re0_1 : (R.val *ᵥ e0) 1 = R.val 1 0 := by
    change ∑ j, R.val 1 j * e0 j = R.val 1 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_Re0_2 : (R.val *ᵥ e0) 2 = R.val 2 0 := by
    change ∑ j, R.val 2 j * e0 j = R.val 2 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_Re0_3 : (R.val *ᵥ e0) 3 = R.val 3 0 := by
    change ∑ j, R.val 3 j * e0 j = R.val 3 0
    rw [Fin.sum_univ_four]
    simp [e0]
  have h_exp : minkowskiInner (R.val *ᵥ e0) (R.val *ᵥ e0) = 1 - (R.val 1 0)^2 - (R.val 2 0)^2 - (R.val 3 0)^2 := by
    rw [minkowskiInner_explicit, h_Re0_0, h_Re0_1, h_Re0_2, h_Re0_3]
    generalize v1 : R.val 1 0 = a
    generalize v2 : R.val 2 0 = b
    generalize v3 : R.val 3 0 = c
    ring
  rw [h_exp] at h_inner_Re0
  have h_sum_zero : (R.val 1 0)^2 + (R.val 2 0)^2 + (R.val 3 0)^2 = 0 := by
    generalize v1 : (R.val 1 0)^2 = a at h_inner_Re0 ⊢
    generalize v2 : (R.val 2 0)^2 = b at h_inner_Re0 ⊢
    generalize v3 : (R.val 3 0)^2 = c at h_inner_Re0 ⊢
    linarith
  have h_sq_nonneg : 0 ≤ (R.val 1 0)^2 + (R.val 2 0)^2 := by positivity
  have h_3_sq_zero : (R.val 3 0)^2 = 0 := by
    generalize v1 : (R.val 1 0)^2 + (R.val 2 0)^2 = a at h_sum_zero h_sq_nonneg ⊢
    generalize v3 : (R.val 3 0)^2 = c at h_sum_zero ⊢
    have h_c_nonneg : 0 ≤ c := by rw [←v3]; exact sq_nonneg (R.val 3 0)
    linarith
  exact sq_eq_zero_iff.mp h_3_sq_zero



def rotation_to_z_wedge_T : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![-1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

lemma rotation_to_z_wedge_aux_neg
  (K' : Set (Fin 4 → ℝ)) (hK'_past : ∀ y ∈ K', y 0 < 0)
  (w : Fin 4 → ℝ) (hw_space : w 0 > Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))
  (R : Matrix.GeneralLinearGroup (Fin 4) ℝ)
  (hR_lor : R.valᵀ * minkowskiMetricReal * R.val = minkowskiMetricReal)
  (hR_det : R.val.det = 1)
  (hR_1 : (R.val *ᵥ w) 1 = 0) (hR_2 : (R.val *ᵥ w) 2 = 0)
  (hR_0 : (R.val *ᵥ w) 0 = w 0) (hR_spatial : ∀ y, (R.val *ᵥ y) 0 = y 0)
  (hw_sep : ∀ y ∈ K', minkowskiInner w (rotation_to_z_wedge_T *ᵥ y) < 0)
  (hx_past : ∀ y ∈ K', (rotation_to_z_wedge_T *ᵥ y) 0 > 0)
  (hw'_0_pos : (R.val *ᵥ w) 0 > 0)
  (h_w'3_sq : (R.val *ᵥ w) 3 ^ 2 = w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2)
  (h_w'3 : (R.val *ᵥ w) 3 < 0) :
  ∃ (Λ_rot : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    Λ_rot.valᵀ * minkowskiMetricReal * Λ_rot.val = minkowskiMetricReal ∧
    (Λ_rot.val.det = 1) ∧
    ∀ y ∈ K', |(Λ_rot.val *ᵥ y) 0| < (Λ_rot.val *ᵥ y) 3 := by
  let w' := R.val *ᵥ w
  let S_val := algebraic_rotation_y (-1) 0
  have h_sq : (-1:ℝ)^2 + 0^2 = 1 := by norm_num
  have hS_lor := algebraic_rotation_y_is_lorentz (-1) 0 h_sq
  let S_inv := S_val
  have hS_inv : S_val * S_inv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.mul_apply, Matrix.one_apply]
      rw [Fin.sum_univ_four]
      simp [S_val, S_inv, algebraic_rotation_y]
    }
  have hS_inv2 : S_inv * S_val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.mul_apply, Matrix.one_apply]
      rw [Fin.sum_univ_four]
      simp [S_val, S_inv, algebraic_rotation_y]
    }
  let S : Matrix.GeneralLinearGroup (Fin 4) ℝ := ⟨S_val, S_inv, hS_inv, hS_inv2⟩
  let Λ := S * R
  use Λ
  refine ⟨?_, ?_, ?_⟩
  · exact lorentz_mul S_val R.val hS_lor hR_lor
  · change (S.val * R.val).det = 1
    rw [Matrix.det_mul, algebraic_rotation_y_det (-1) 0 h_sq, hR_det, mul_one]
  · intro y hy
    have h_x_past := hx_past y hy
    have hy_past : y 0 < 0 := hK'_past y hy
    have h_sep_x := hw_sep y hy
    have h_inner : minkowskiInner w' (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) = minkowskiInner w (rotation_to_z_wedge_T *ᵥ y) := lorentz_preserves_inner R.val hR_lor w (rotation_to_z_wedge_T *ᵥ y)
    rw [←h_inner] at h_sep_x
    have h_exp : minkowskiInner w' (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) = w' 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 0 - w' 1 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 1 - w' 2 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 2 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      rw [minkowskiInner_explicit]
    rw [h_exp] at h_sep_x
    have hw'1 : w' 1 = 0 := hR_1
    have hw'2 : w' 2 = 0 := hR_2
    rw [hw'1, hw'2] at h_sep_x
    have h_x0 : (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 0 = (rotation_to_z_wedge_T *ᵥ y) 0 := hR_spatial (rotation_to_z_wedge_T *ᵥ y)
    rw [h_x0] at h_sep_x
    have h_ineq : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      have h_simp : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 - 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 1 - 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 2 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by ring
      linarith
    have h_y0_eq : (rotation_to_z_wedge_T *ᵥ y) 0 = -y 0 := by
      change ∑ i : Fin 4, rotation_to_z_wedge_T 0 i * y i = -y 0
      rw [Fin.sum_univ_four]
      change (-1) * y 0 + 0 * y 1 + 0 * y 2 + 0 * y 3 = -y 0
      ring
    have h_abs_y0 : (rotation_to_z_wedge_T *ᵥ y) 0 = |y 0| := by
      rw [h_y0_eq, abs_of_neg hy_past]
    have h_T_val_y0_pos : (rotation_to_z_wedge_T *ᵥ y) 0 > 0 := h_x_past
    have h_neg_w'3_pos : -w' 3 > 0 := by exact neg_pos.mpr h_w'3
    have h_w'0_gt : w' 0 > -w' 3 := by
      have h_sq_gt : (-w' 3)^2 < w' 0^2 := by
        calc
          (-w' 3)^2 = w' 3^2 := by ring
          _ = w 1^2 + w 2^2 + w 3^2 := h_w'3_sq
          _ < w 0^2 := by
            have h_nonneg : 0 ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
            have h_sq_w : (Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))^2 < w 0 ^ 2 := by
              have h_sqrt_nonneg : 0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
              nlinarith
            rwa [Real.sq_sqrt h_nonneg] at h_sq_w
          _ = w' 0^2 := by
            have hw'0_eq : w' 0 = w 0 := hR_0
            rw [hw'0_eq]
      generalize hw0_var : w' 0 = v_0 at h_sq_gt hw'_0_pos
      generalize hw3_var : w' 3 = v_3 at h_sq_gt h_neg_w'3_pos
      nlinarith
    have h_step1 : (-w' 3) * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 := by
      exact mul_lt_mul_of_pos_right h_w'0_gt h_T_val_y0_pos
    have h_step2 : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      generalize v1 : w' 0 = a
      generalize v2 : (rotation_to_z_wedge_T *ᵥ y) 0 = b
      generalize v3 : w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = c
      have h_ineq_g : a * b < c := by rw [←v1, ←v2, ←v3]; exact h_ineq
      exact h_ineq_g
    have h_step3 : (-w' 3) * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      exact lt_trans h_step1 h_step2
    have h_step4 : (-w' 3) * (rotation_to_z_wedge_T *ᵥ y) 0 < (-w' 3) * (-(R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3) := by
      have h_eq : w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = (-w' 3) * (-(R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3) := by
        generalize a : w' 3 = a_var
        generalize b : (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = b_var
        ring
      rwa [h_eq] at h_step3
    have h_final : (rotation_to_z_wedge_T *ᵥ y) 0 < -(R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 :=
      lt_of_mul_lt_mul_left h_step4 (le_of_lt h_neg_w'3_pos)
    have h_R_val_0 : (Λ.val *ᵥ y) 0 = y 0 := by
      have h1 : (Λ.val *ᵥ y) 0 = ∑ i : Fin 4, (S_val * R.val) 0 i * y i := rfl
      have h2 : ∀ i, (S_val * R.val) 0 i = ∑ j : Fin 4, S_val 0 j * R.val j i := fun i => rfl
      rw [h1]
      simp_rw [h2]
      have h3 : ∀ i, ∑ j : Fin 4, S_val 0 j * R.val j i = R.val 0 i := by
        intro i
        have hS00 : S_val 0 0 = 1 := rfl
        have hS01 : S_val 0 1 = 0 := rfl
        have hS02 : S_val 0 2 = 0 := rfl
        have hS03 : S_val 0 3 = 0 := rfl
        rw [Fin.sum_univ_four, hS00, hS01, hS02, hS03]
        ring
      have h_sum : ∑ i : Fin 4, (∑ j : Fin 4, S_val 0 j * R.val j i) * y i = ∑ i : Fin 4, R.val 0 i * y i := by
        congr
        ext i
        rw [h3 i]
      rw [h_sum]
      have h_R0 : ∑ i : Fin 4, R.val 0 i * y i = (R.val *ᵥ y) 0 := rfl
      rw [h_R0]
      exact hR_spatial y
    have h_R_val_3 : (Λ.val *ᵥ y) 3 = -(R.val *ᵥ y) 3 := by
      have h1 : (Λ.val *ᵥ y) 3 = ∑ i : Fin 4, (S_val * R.val) 3 i * y i := rfl
      have h2 : ∀ i, (S_val * R.val) 3 i = ∑ j : Fin 4, S_val 3 j * R.val j i := fun i => rfl
      rw [h1]
      simp_rw [h2]
      have h3 : ∀ i, ∑ j : Fin 4, S_val 3 j * R.val j i = -R.val 3 i := by
        intro i
        have hS30 : S_val 3 0 = 0 := rfl
        have hS31 : S_val 3 1 = 0 := neg_zero
        have hS32 : S_val 3 2 = 0 := rfl
        have hS33 : S_val 3 3 = -1 := rfl
        rw [Fin.sum_univ_four, hS30, hS31, hS32, hS33]
        ring
      have h_sum : ∑ i : Fin 4, (∑ j : Fin 4, S_val 3 j * R.val j i) * y i = ∑ i : Fin 4, -R.val 3 i * y i := by
        congr
        ext i
        rw [h3 i]
      rw [h_sum]
      have h4 : ∑ i : Fin 4, -R.val 3 i * y i = -(∑ i : Fin 4, R.val 3 i * y i) := by
        rw [← Finset.sum_neg_distrib]
        congr
        ext i
        ring
      rw [h4]
      rfl
    have h_T_val_3 : (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = (R.val *ᵥ y) 3 := by
      have h_R30 : R.val 3 0 = 0 := lorentz_spatial_zero R.val hR_lor hR_spatial
      have h_T0 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 0 = -y' 0 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 0 i * y' i = -y' 0
        rw [Fin.sum_univ_four]
        change (-1) * y' 0 + 0 * y' 1 + 0 * y' 2 + 0 * y' 3 = -y' 0
        ring
      have h_T1 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 1 = y' 1 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 1 i * y' i = y' 1
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 1 * y' 1 + 0 * y' 2 + 0 * y' 3 = y' 1
        ring
      have h_T2 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 2 = y' 2 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 2 i * y' i = y' 2
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 0 * y' 1 + 1 * y' 2 + 0 * y' 3 = y' 2
        ring
      have h_T3 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 3 = y' 3 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 3 i * y' i = y' 3
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 0 * y' 1 + 0 * y' 2 + 1 * y' 3 = y' 3
        ring
      exact matrix_mulVec_three_eq R.val rotation_to_z_wedge_T h_R30 h_T0 h_T1 h_T2 h_T3 y
    rw [h_T_val_3] at h_final
    rw [h_abs_y0] at h_final
    have h_R_val_0_abs : |(Λ.val *ᵥ y) 0| = |y 0| := by rw [h_R_val_0]
    rw [h_R_val_0_abs, h_R_val_3]
    exact h_final

lemma rotation_to_z_wedge_aux_pos
  (K' : Set (Fin 4 → ℝ)) (hK'_past : ∀ y ∈ K', y 0 < 0)
  (w : Fin 4 → ℝ) (hw_space : w 0 > Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))
  (R : Matrix.GeneralLinearGroup (Fin 4) ℝ)
  (hR_lor : R.valᵀ * minkowskiMetricReal * R.val = minkowskiMetricReal)
  (hR_det : R.val.det = 1)
  (hR_1 : (R.val *ᵥ w) 1 = 0) (hR_2 : (R.val *ᵥ w) 2 = 0)
  (hR_0 : (R.val *ᵥ w) 0 = w 0) (hR_spatial : ∀ y, (R.val *ᵥ y) 0 = y 0)
  (hw_sep : ∀ y ∈ K', minkowskiInner w (rotation_to_z_wedge_T *ᵥ y) < 0)
  (hx_past : ∀ y ∈ K', (rotation_to_z_wedge_T *ᵥ y) 0 > 0)
  (hw'_0_pos : (R.val *ᵥ w) 0 > 0)
  (hw'_3_nz : (R.val *ᵥ w) 3 ≠ 0)
  (h_w'3_sq : (R.val *ᵥ w) 3 ^ 2 = w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2)
  (h_w'3 : ¬ (R.val *ᵥ w) 3 < 0) :
  ∃ (Λ_rot : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    Λ_rot.valᵀ * minkowskiMetricReal * Λ_rot.val = minkowskiMetricReal ∧
    (Λ_rot.val.det = 1) ∧
    ∀ y ∈ K', |(Λ_rot.val *ᵥ y) 0| < (Λ_rot.val *ᵥ y) 3 := by
  let w' := R.val *ᵥ w
  let Λ := R
  use Λ
  refine ⟨?_, ?_, ?_⟩
  · exact hR_lor
  · exact hR_det
  · intro y hy
    have h_x_past := hx_past y hy
    have hy_past : y 0 < 0 := hK'_past y hy
    have h_sep_x := hw_sep y hy
    have h_inner : minkowskiInner w' (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) = minkowskiInner w (rotation_to_z_wedge_T *ᵥ y) := lorentz_preserves_inner R.val hR_lor w (rotation_to_z_wedge_T *ᵥ y)
    rw [←h_inner] at h_sep_x
    have h_exp : minkowskiInner w' (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) = w' 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 0 - w' 1 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 1 - w' 2 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 2 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      rw [minkowskiInner_explicit]
    rw [h_exp] at h_sep_x
    have hw'1 : w' 1 = 0 := hR_1
    have hw'2 : w' 2 = 0 := hR_2
    rw [hw'1, hw'2] at h_sep_x
    have h_x0 : (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 0 = (rotation_to_z_wedge_T *ᵥ y) 0 := hR_spatial (rotation_to_z_wedge_T *ᵥ y)
    rw [h_x0] at h_sep_x
    have h_ineq : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      have h_simp : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 - 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 1 - 0 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 2 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 - w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by ring
      linarith
    have h_y0_eq : (rotation_to_z_wedge_T *ᵥ y) 0 = -y 0 := by
      change ∑ i : Fin 4, rotation_to_z_wedge_T 0 i * y i = -y 0
      rw [Fin.sum_univ_four]
      change (-1) * y 0 + 0 * y 1 + 0 * y 2 + 0 * y 3 = -y 0
      ring
    have h_abs_y0 : (rotation_to_z_wedge_T *ᵥ y) 0 = |y 0| := by
      rw [h_y0_eq, abs_of_neg hy_past]
    have h_w'0_gt : w' 0 > w' 3 := by
      have h_sq : (w' 3)^2 < w' 0^2 := by
        calc
          (w' 3)^2 = w 1^2 + w 2^2 + w 3^2 := h_w'3_sq
          _ < w 0^2 := by
            have h_sqrt_nonneg : 0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
            have ht1 := mul_self_lt_mul_self h_sqrt_nonneg hw_space
            rw [←pow_two, ←pow_two] at ht1
            have h_nonneg : 0 ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
            rwa [Real.sq_sqrt h_nonneg] at ht1
          _ = w' 0^2 := by
            have hw'0_eq : w' 0 = w 0 := hR_0
            rw [hw'0_eq]
      have hs1 : Real.sqrt ((w' 3)^2) < Real.sqrt (w' 0^2) := by
        apply Real.sqrt_lt_sqrt
        · exact sq_nonneg (w' 3)
        · exact h_sq
      rwa [Real.sqrt_sq (not_lt.mp h_w'3), Real.sqrt_sq (le_of_lt hw'_0_pos)] at hs1
    have h_T_val_y0_pos : (rotation_to_z_wedge_T *ᵥ y) 0 > 0 := h_x_past
    have h_w'3_pos : w' 3 > 0 := by
      have h1 : 0 ≤ w' 3 := not_lt.mp h_w'3
      have h2 : 0 ≠ w' 3 := Ne.symm hw'_3_nz
      exact lt_of_le_of_ne h1 h2
    have h_step1 : w' 3 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 := by
      exact mul_lt_mul_of_pos_right h_w'0_gt h_T_val_y0_pos
    have h_step2 : w' 0 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      generalize v1 : w' 0 = a
      generalize v2 : (rotation_to_z_wedge_T *ᵥ y) 0 = b
      generalize v3 : w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = c
      have h_ineq_g : a * b < c := by rw [←v1, ←v2, ←v3]; exact h_ineq
      exact h_ineq_g
    have h_step3 : w' 3 * (rotation_to_z_wedge_T *ᵥ y) 0 < w' 3 * (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 := by
      exact lt_trans h_step1 h_step2
    have h_final : (rotation_to_z_wedge_T *ᵥ y) 0 < (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 :=
      lt_of_mul_lt_mul_left h_step3 (le_of_lt h_w'3_pos)
    have h_R_val_0 : (Λ.val *ᵥ y) 0 = y 0 := hR_spatial y
    have h_T_val_3 : (R.val *ᵥ (rotation_to_z_wedge_T *ᵥ y)) 3 = (R.val *ᵥ y) 3 := by
      have h_R30 : R.val 3 0 = 0 := lorentz_spatial_zero R.val hR_lor hR_spatial
      have h_T0 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 0 = -y' 0 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 0 i * y' i = -y' 0
        rw [Fin.sum_univ_four]
        change (-1) * y' 0 + 0 * y' 1 + 0 * y' 2 + 0 * y' 3 = -y' 0
        ring
      have h_T1 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 1 = y' 1 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 1 i * y' i = y' 1
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 1 * y' 1 + 0 * y' 2 + 0 * y' 3 = y' 1
        ring
      have h_T2 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 2 = y' 2 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 2 i * y' i = y' 2
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 0 * y' 1 + 1 * y' 2 + 0 * y' 3 = y' 2
        ring
      have h_T3 : ∀ y', (rotation_to_z_wedge_T *ᵥ y') 3 = y' 3 := by
        intro y'
        change ∑ i : Fin 4, rotation_to_z_wedge_T 3 i * y' i = y' 3
        rw [Fin.sum_univ_four]
        change 0 * y' 0 + 0 * y' 1 + 0 * y' 2 + 1 * y' 3 = y' 3
        ring
      exact matrix_mulVec_three_eq R.val rotation_to_z_wedge_T h_R30 h_T0 h_T1 h_T2 h_T3 y
    rw [h_T_val_3] at h_final
    rw [h_abs_y0] at h_final
    have h_R_val_0_abs : |(Λ.val *ᵥ y) 0| = |y 0| := by
      have ht1 : (Λ.val *ᵥ y) 0 = y 0 := h_R_val_0
      rw [ht1]
    have ht2 : (R.val *ᵥ y) 3 = (Λ.val *ᵥ y) 3 := rfl
    rw [ht2] at h_final
    rw [h_R_val_0_abs]
    exact h_final

lemma rotation_to_z_wedge
  (K' : Set (Fin 4 → ℝ)) (hK'_compact : IsCompact K') (hK'_convex : Convex ℝ K')
  (hK'_spacelike : ∀ w' ∈ K', is_spacelike w')
  (hK'_past : ∀ w' ∈ K', w' 0 < 0)
  (hK'_nonempty : K'.Nonempty) :
  ∃ (Λ_rot : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    Λ_rot.valᵀ * minkowskiMetricReal * Λ_rot.val = minkowskiMetricReal ∧
    (Λ_rot.val.det = 1) ∧
    ∀ w' ∈ K', |(Λ_rot.val *ᵥ w') 0| < (Λ_rot.val *ᵥ w') 3 := by
  let T_val := rotation_to_z_wedge_T

  have hT_cont : Continuous (fun x => T_val *ᵥ x) := by
    apply continuous_pi
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply continuous_finsetSum
    intro j _
    exact (continuous_apply j).const_smul (T_val i j)

  let K'' := (fun x => T_val *ᵥ x) '' K'

  have hK''_compact : IsCompact K'' := hK'_compact.image hT_cont

  have hT_lin : IsLinearMap ℝ (fun x => T_val *ᵥ x) := by
    constructor
    · intro x y; exact Matrix.mulVec_add T_val x y
    · intro c x; exact Matrix.mulVec_smul T_val c x

  have hK''_convex : Convex ℝ K'' := hK'_convex.is_linear_image hT_lin

  have hK''_spacelike : ∀ w'' ∈ K'', is_spacelike w'' := by
    rintro w'' ⟨w', hw', rfl⟩
    have h_w'_space := hK'_spacelike w' hw'
    have h_inner_eq : minkowskiInner (T_val *ᵥ w') (T_val *ᵥ w') = minkowskiInner w' w' := by
      rw [minkowskiInner_explicit, minkowskiInner_explicit]
      have h0 : (T_val *ᵥ w') 0 = -w' 0 := by change ∑ i : Fin 4, T_val 0 i * w' i = -w' 0; rw [Fin.sum_univ_four]; change (-1) * w' 0 + 0 * w' 1 + 0 * w' 2 + 0 * w' 3 = -w' 0; ring
      have h1 : (T_val *ᵥ w') 1 = w' 1 := by change ∑ i : Fin 4, T_val 1 i * w' i = w' 1; rw [Fin.sum_univ_four]; change 0 * w' 0 + 1 * w' 1 + 0 * w' 2 + 0 * w' 3 = w' 1; ring
      have h2 : (T_val *ᵥ w') 2 = w' 2 := by change ∑ i : Fin 4, T_val 2 i * w' i = w' 2; rw [Fin.sum_univ_four]; change 0 * w' 0 + 0 * w' 1 + 1 * w' 2 + 0 * w' 3 = w' 2; ring
      have h3 : (T_val *ᵥ w') 3 = w' 3 := by change ∑ i : Fin 4, T_val 3 i * w' i = w' 3; rw [Fin.sum_univ_four]; change 0 * w' 0 + 0 * w' 1 + 0 * w' 2 + 1 * w' 3 = w' 3; ring
      rw [h0, h1, h2, h3]
      ring
    unfold is_spacelike at *
    rwa [h_inner_eq]

  have hK''_future : ∀ w'' ∈ K'', w'' 0 > 0 := by
    rintro w'' ⟨w', hw', rfl⟩
    have h_w'_past := hK'_past w' hw'
    have h_T_y0 : (T_val *ᵥ w') 0 = -w' 0 := by
      change ∑ i : Fin 4, T_val 0 i * w' i = -w' 0
      rw [Fin.sum_univ_four]
      change (-1) * w' 0 + 0 * w' 1 + 0 * w' 2 + 0 * w' 3 = -w' 0
      ring
    change (T_val *ᵥ w') 0 > 0
    rw [h_T_y0]
    linarith

  have hK''_nonempty : K''.Nonempty := hK'_nonempty.image (fun x => T_val *ᵥ x)
  have h_sep := separation_hyperplane_exists K'' hK''_compact hK''_convex hK''_spacelike hK''_nonempty
  rcases h_sep with ⟨u, hu_cone, h_sep_u⟩
  have h_strict_sep := exists_strictly_timelike_separator K'' hK''_compact u hu_cone h_sep_u
  rcases h_strict_sep with ⟨w, hw_space, hw_sep⟩

  have hw_non_spacelike : ¬ is_spacelike w := by
    intro hw_sp
    have hw0_sq : w 0 ^ 2 > w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by
      have h_nonneg : 0 ≤ w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by positivity
      have h_sq : (Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2))^2 < w 0 ^ 2 := by
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
        nlinarith
      rwa [Real.sq_sqrt h_nonneg] at h_sq
    have h_sp_eq : minkowskiInner w w = w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - w 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    change minkowskiInner w w < 0 at hw_sp
    rw [h_sp_eq] at hw_sp
    linarith

  have h_align := lorentz_align_non_spacelike w hw_non_spacelike
  let R := Classical.choose h_align
  have hR := Classical.choose_spec h_align
  have hR_lor := hR.1
  have hR_det := hR.2.1
  have hR_1 := hR.2.2.1
  have hR_2 := hR.2.2.2.1
  have hR_0 := hR.2.2.2.2.1
  have hR_spatial := hR.2.2.2.2.2
  let w' := R.val *ᵥ w

  have h_w'3_sq : w' 3 ^ 2 = w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 := by
    have h_inner : minkowskiInner w' w' = minkowskiInner w w := lorentz_preserves_inner R.val hR_lor w w
    have h_w'_inner : minkowskiInner w' w' = w' 0 ^ 2 - w' 1 ^ 2 - w' 2 ^ 2 - w' 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    have h_w_inner : minkowskiInner w w = w 0 ^ 2 - w 1 ^ 2 - w 2 ^ 2 - w 3 ^ 2 := by
      rw [minkowskiInner_explicit]
      ring
    have hw'1 : w' 1 = 0 := hR_1
    have hw'2 : w' 2 = 0 := hR_2
    have hw'0 : w' 0 = w 0 := hR_0
    rw [h_w'_inner, h_w_inner, hw'1, hw'2, hw'0] at h_inner
    linarith

  have hw'_0_pos : w' 0 > 0 := by
    have hw'0 : w' 0 = w 0 := hR_0
    rw [hw'0]
    calc
      0 ≤ Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) := Real.sqrt_nonneg _
      _ < w 0 := hw_space

  have hw'_3_nz : w' 3 ≠ 0 := by
    intro h
    rw [h] at h_w'3_sq
    have h_sum_zero : w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 = 0 := by linarith
    have h_w_zero : Real.sqrt (w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2) = 0 := Real.sqrt_eq_zero'.mpr (by linarith)
    have hw0_pos : w 0 > 0 := by linarith
    have hu_cone_prop := hu_cone.1
    rcases hK''_nonempty with ⟨x, hx⟩
    have h_sep_x := hw_sep x hx
    have hx0_pos := hK''_future x hx
    have h_inner_x : minkowskiInner w x = w 0 * x 0 - w 1 * x 1 - w 2 * x 2 - w 3 * x 3 := by rw [minkowskiInner_explicit]
    have hw1_zero : w 1 = 0 := by
      have h1 : 0 ≤ w 1 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ w 2 ^ 2 := sq_nonneg _
      have h3 : 0 ≤ w 3 ^ 2 := sq_nonneg _
      nlinarith
    have hw2_zero : w 2 = 0 := by
      have h1 : 0 ≤ w 1 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ w 2 ^ 2 := sq_nonneg _
      have h3 : 0 ≤ w 3 ^ 2 := sq_nonneg _
      nlinarith
    have hw3_zero : w 3 = 0 := by
      have h1 : 0 ≤ w 1 ^ 2 := sq_nonneg _
      have h2 : 0 ≤ w 2 ^ 2 := sq_nonneg _
      have h3 : 0 ≤ w 3 ^ 2 := sq_nonneg _
      nlinarith
    rw [hw1_zero, hw2_zero, hw3_zero] at h_inner_x
    have h_inner_x_pos : w 0 * x 0 > 0 := mul_pos hw0_pos hx0_pos
    linarith

  have hw_sep_T : ∀ y ∈ K', minkowskiInner w (rotation_to_z_wedge_T *ᵥ y) < 0 := by
    intro y hy
    exact hw_sep (rotation_to_z_wedge_T *ᵥ y) ⟨y, hy, rfl⟩

  have hx_past_T : ∀ y ∈ K', (rotation_to_z_wedge_T *ᵥ y) 0 > 0 := by
    intro y hy
    exact hK''_future (rotation_to_z_wedge_T *ᵥ y) ⟨y, hy, rfl⟩

  by_cases h_w'3 : w' 3 < 0
  · apply rotation_to_z_wedge_aux_neg K' hK'_past w hw_space R hR_lor hR_det hR_1 hR_2 hR_0 hR_spatial hw_sep_T hx_past_T hw'_0_pos h_w'3_sq h_w'3
  · apply rotation_to_z_wedge_aux_pos K' hK'_past w hw_space R hR_lor hR_det hR_1 hR_2 hR_0 hR_spatial hw_sep_T hx_past_T hw'_0_pos hw'_3_nz h_w'3_sq h_w'3

lemma bhw_geometric_lemma (K : Set (Fin 4 → ℝ)) (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
  (hK_spacelike : ∀ w ∈ K, is_spacelike w)
  (u : Fin 4 → ℝ) (hu : ¬ is_spacelike u)
  (h_sep : ∀ w ∈ K, minkowskiInner u w ≥ 0) :
  ∃ (Λ : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    (Matrix.transpose Λ.val * minkowskiMetricReal * Λ.val = minkowskiMetricReal) ∧
    (Λ.val.det = 1) ∧
    ∀ w ∈ K, |Matrix.mulVec Λ.val w 0| < Matrix.mulVec Λ.val w 3 := by
  by_cases hK_nonempty : K.Nonempty
  · 
    obtain ⟨Λ_past, hΛ_past_lor, hΛ_past_det, h_past⟩ := exists_lorentz_mapping_K_past K hK_compact hK_convex hK_spacelike hK_nonempty

    
    let K' := (fun w => Λ_past.val *ᵥ w) '' K

    have h_cont : Continuous (fun (w : Fin 4 → ℝ) => Λ_past.val *ᵥ w) := by
      apply continuous_pi
      intro i
      simp only [Matrix.mulVec, dotProduct]
      apply continuous_finsetSum
      intro j _
      have h_const : Continuous (fun (a : Fin 4 → ℝ) => Λ_past.val i j * a j) := by
        exact Continuous.const_smul (continuous_apply j) (Λ_past.val i j)
      exact h_const

    have hK'_compact : IsCompact K' := hK_compact.image h_cont

    have hK'_nonempty : K'.Nonempty := hK_nonempty.image _

    have h_lin : IsLinearMap ℝ (fun w => Λ_past.val *ᵥ w) := by
      constructor
      · intro x y; exact Matrix.mulVec_add Λ_past.val x y
      · intro c x; exact Matrix.mulVec_smul Λ_past.val c x
    have hK'_convex : Convex ℝ K' := hK_convex.is_linear_image h_lin

    have hK'_spacelike : ∀ w' ∈ K', is_spacelike w' := by
      rintro w' ⟨w, hw, rfl⟩
      have h_w_space := hK_spacelike w hw
      have h_inner_eq : minkowskiInner (Λ_past.val *ᵥ w) (Λ_past.val *ᵥ w) = minkowskiInner w w :=
        lorentz_preserves_inner Λ_past.val hΛ_past_lor w w
      unfold is_spacelike at *
      rwa [h_inner_eq]

    have hK'_past : ∀ w' ∈ K', w' 0 < 0 := by
      rintro w' ⟨w, hw, rfl⟩
      exact h_past w hw

    
    obtain ⟨Λ_rot, hΛ_rot_lor, hΛ_rot_det, h_wedge⟩ := rotation_to_z_wedge K' hK'_compact hK'_convex hK'_spacelike hK'_past hK'_nonempty

    
    let Λ := Λ_rot * Λ_past
    use Λ
    refine ⟨?_, ?_, ?_⟩
    · change (Λ_rot.val * Λ_past.val)ᵀ * minkowskiMetricReal * (Λ_rot.val * Λ_past.val) = minkowskiMetricReal
      rw [Matrix.transpose_mul]
      have h1 : Λ_past.valᵀ * (Λ_rot.valᵀ * minkowskiMetricReal * Λ_rot.val) * Λ_past.val = Λ_past.valᵀ * minkowskiMetricReal * Λ_past.val := by rw [hΛ_rot_lor]
      have h2 : (Λ_past.valᵀ * Λ_rot.valᵀ) * minkowskiMetricReal * (Λ_rot.val * Λ_past.val) = Λ_past.valᵀ * (Λ_rot.valᵀ * minkowskiMetricReal * Λ_rot.val) * Λ_past.val := by simp only [Matrix.mul_assoc]
      rw [h2, h1, hΛ_past_lor]
    · change (Λ_rot.val * Λ_past.val).det = 1
      rw [Matrix.det_mul, hΛ_rot_det, hΛ_past_det, mul_one]
    · intro w hw
      have h_w' : Λ_past.val *ᵥ w ∈ K' := ⟨w, hw, rfl⟩
      have h_wedge_w := h_wedge (Λ_past.val *ᵥ w) h_w'
      have h_assoc : Λ_rot.val *ᵥ (Λ_past.val *ᵥ w) = (Λ_rot.val * Λ_past.val) *ᵥ w := Matrix.mulVec_mulVec w Λ_rot.val Λ_past.val
      change |((Λ_rot.val * Λ_past.val) *ᵥ w) 0| < ((Λ_rot.val * Λ_past.val) *ᵥ w) 3
      rw [←h_assoc]
      exact h_wedge_w
  · use 1
    refine ⟨?_, ?_, ?_⟩
    · simp [minkowskiMetricReal]
    · change (1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1
      exact Matrix.det_one
    · intro w hw
      have h_not_mem : w ∉ K := fun h => hK_nonempty ⟨w, h⟩
      exact False.elim (h_not_mem hw)






lemma forward_tube_has_no_real_points (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hn : n > 1) :
  coeReal n x ∉ forward_tube_n n := by
  intro h
  have hi : (0 : ℕ) + 1 < n := hn
  have h1 := h ⟨0, by linarith⟩ hi
  have h2 : (fun (j : Fin 4) => -((coeReal n x ⟨0, by linarith⟩ - coeReal n x ⟨(0:ℕ) + 1, hi⟩) j).im) 0 = 0 := by
    simp [coeReal]
  have h3 : (fun (j : Fin 4) => -((coeReal n x ⟨0, by linarith⟩ - coeReal n x ⟨(0:ℕ) + 1, hi⟩) j).im) 0 > 0 := h1.1
  rw [h2] at h3
  exact lt_irrefl 0 h3


lemma jost_hull_disjoint_cone (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ jost_points_n n) :
  Disjoint forward_light_cone (jost_convex_hull n x) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext v
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hv_cone hv_jost
  have hv_not_zero : v ≠ 0 := by
    intro h_zero
    rw [h_zero] at hv_cone
    have h_v0 : (0 : Fin 4 → ℝ) 0 = 0 := rfl
    have h_v0_pos : (0 : Fin 4 → ℝ) 0 > 0 := hv_cone.1
    rw [h_v0] at h_v0_pos
    exact lt_irrefl 0 h_v0_pos
  have h1 : is_spacelike v := hx v hv_jost
  have h2 : minkowskiInner v v > 0 := hv_cone.2
  have h3 : minkowskiInner v v < 0 := h1
  linarith

lemma forward_light_cone_isOpen : IsOpen forward_light_cone := by
  have h1 : IsOpen { x : Fin 4 → ℝ | x 0 > 0 } := by
    have hc : Continuous (fun x : Fin 4 → ℝ => x 0) := continuous_apply 0
    exact isOpen_lt continuous_const hc
  have h2 : IsOpen { x : Fin 4 → ℝ | minkowskiInner x x > 0 } := by
    have hc : Continuous (fun x : Fin 4 → ℝ => minkowskiInner x x) := by
      have h_eq : (fun x : Fin 4 → ℝ => minkowskiInner x x) = (fun x => x 0 * x 0 - x 1 * x 1 - x 2 * x 2 - x 3 * x 3) := by
        ext x
        rw [minkowskiInner_explicit]
      rw [h_eq]
      continuity
    exact isOpen_lt continuous_const hc
  exact IsOpen.inter h1 h2

lemma jost_separation (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ jost_points_n n) :
  ∃ f : (Fin 4 → ℝ) →L[ℝ] ℝ, ∃ s : ℝ,
    (∀ v ∈ forward_light_cone, f v < s) ∧
    (∀ w ∈ jost_convex_hull n x, s ≤ f w) := by
  apply geometric_hahn_banach_open forward_light_cone_convex forward_light_cone_isOpen (jost_convex_hull_convex n x) (jost_hull_disjoint_cone n x hx)





noncomputable def complex_boost_1 (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![
    Complex.cos (θ:ℂ), Complex.I * Complex.sin (θ:ℂ), 0, 0;
    Complex.I * Complex.sin (θ:ℂ), Complex.cos (θ:ℂ), 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1
  ]

lemma complex_boost_1_is_lorentz (θ : ℝ) :
  (complex_boost_1 θ)ᵀ * minkowskiMetric * (complex_boost_1 θ) = minkowskiMetric := by
  have hi : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
  have h_cs : (Complex.cos (θ:ℂ))^2 + (Complex.sin (θ:ℂ))^2 = 1 := Complex.cos_sq_add_sin_sq (θ:ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    calc Complex.cos ↑θ * Complex.cos ↑θ + -(Complex.I * Complex.sin ↑θ * (Complex.I * Complex.sin ↑θ))
        = (Complex.cos ↑θ)^2 - Complex.I * Complex.I * (Complex.sin ↑θ)^2 := by ring
      _ = (Complex.cos ↑θ)^2 - (-1) * (Complex.sin ↑θ)^2 := by rw [hi]
      _ = (Complex.cos ↑θ)^2 + (Complex.sin ↑θ)^2 := by ring
      _ = 1 := h_cs
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp; ring
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp; try ring_nf
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    calc Complex.I * Complex.sin ↑θ * (Complex.I * Complex.sin ↑θ) + -(Complex.cos ↑θ * Complex.cos ↑θ)
        = Complex.I * Complex.I * (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 := by ring
      _ = (-1) * (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 := by rw [hi]
      _ = -((Complex.cos ↑θ)^2 + (Complex.sin ↑θ)^2) := by ring
      _ = -(1 : ℂ) := by rw [h_cs]
      _ = -1 := by ring
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_1, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp





lemma minkowski_riesz (f : (Fin 4 → ℝ) →L[ℝ] ℝ) :
  ∃ u : Fin 4 → ℝ, ∀ v, f v = minkowskiInner u v := by
  let e (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0
  let u : Fin 4 → ℝ := fun i => if i = 0 then f (e 0) else - f (e i)
  use u
  intro v
  have hv : v = ∑ i : Fin 4, v i • e i := by
    ext j
    simp [e, Finset.sum_apply]
  have hfv : f v = ∑ i : Fin 4, v i * f (e i) := by
    calc f v
      _ = f (∑ i : Fin 4, v i • e i) := by nth_rw 1 [hv]
      _ = ∑ i : Fin 4, f (v i • e i) := map_sum f _ _
      _ = ∑ i : Fin 4, v i * f (e i) := by simp
  have hinner : minkowskiInner u v = ∑ i : Fin 4, v i * f (e i) := by
    simp [minkowskiInner_explicit, u, e]
    repeat rw [Fin.sum_univ_four]
    ring
  rw [hfv, hinner]

lemma separating_vector_is_timelike (u : Fin 4 → ℝ) (s : ℝ)
  (h_cone : ∀ v ∈ forward_light_cone, minkowskiInner u v < s) :
  ¬ is_spacelike u := by
  intro hu
  have h_le_zero : ∀ v ∈ forward_light_cone, minkowskiInner u v ≤ 0 := by
    intro v hv
    by_contra h_pos
    push Not at h_pos
    let a := |s| / minkowskiInner u v + 1
    have h1 : |s| / minkowskiInner u v ≥ 0 := div_nonneg (abs_nonneg s) (le_of_lt h_pos)
    have ha : a > 0 := by linarith
    let va : Fin 4 → ℝ := a • v
    have hva0 : va 0 = a * v 0 := rfl
    have h_in : va ∈ forward_light_cone := by
      constructor
      · rw [hva0]; have hv0 : v 0 > 0 := hv.1; positivity
      · have h_pos2 : minkowskiInner v v > 0 := hv.2
        have h_inner_va : minkowskiInner va va = a^2 * minkowskiInner v v := by
          simp [minkowskiInner_explicit, va]
          ring
        rw [h_inner_va]
        positivity
    have h_lt := h_cone va h_in
    have h_eval : minkowskiInner u va = a * minkowskiInner u v := by
      simp [minkowskiInner_explicit, va]
      ring
    rw [h_eval] at h_lt
    have h_calc : a * minkowskiInner u v = |s| + minkowskiInner u v := by
      calc a * minkowskiInner u v
        _ = (|s| / minkowskiInner u v + 1) * minkowskiInner u v := rfl
        _ = (|s| / minkowskiInner u v) * minkowskiInner u v + minkowskiInner u v := by ring
        _ = |s| + minkowskiInner u v := by rw [div_mul_cancel₀ _ (ne_of_gt h_pos)]
    rw [h_calc] at h_lt
    have h_abs : s ≤ |s| := le_abs_self s
    linarith
  have h_space : minkowskiInner u u < 0 := hu
  let R2 := (u 1)^2 + (u 2)^2 + (u 3)^2
  have h_u_inner : minkowskiInner u u = (u 0)^2 - R2 := by
    simp [minkowskiInner_explicit, R2]
    ring
  have h_R2 : R2 = (u 1)^2 + (u 2)^2 + (u 3)^2 := rfl
  rw [h_u_inner] at h_space
  have h_R2_pos : R2 > (u 0)^2 := by linarith
  have h_R2_nonneg : R2 ≥ 0 := by linarith [sq_nonneg (u 0)]
  let R := Real.sqrt R2
  have h_R : R^2 = R2 := Real.sq_sqrt h_R2_nonneg
  have h_u0_R : (u 0)^2 < R^2 := by linarith
  have h_R_pos : R > 0 := by
    by_contra h_neg
    push Not at h_neg
    have h_R_zero : R = 0 := le_antisymm h_neg (Real.sqrt_nonneg R2)
    rw [h_R_zero] at h_u0_R
    have h_sq : (u 0)^2 ≥ 0 := sq_nonneg (u 0)
    linarith
  have h_R2_pos_strict : R2 > 0 := by rw [←h_R]; exact pow_pos h_R_pos 2
  by_cases h_u0 : u 0 < 0
  · let c := - u 0
    have hc : c > 0 := neg_pos.mpr h_u0
    have hcR : c^2 < R^2 := by
      calc c^2 = (-u 0)^2 := by ring
        _ = (u 0)^2 := by ring
        _ < R^2 := h_u0_R
    have hcR_lin : c < R := by nlinarith [Real.sqrt_nonneg R2]
    let v0 := (R + R^2 / c) / 2
    have h_v0_pos : v0 > 0 := by
      have h1 : R^2 > 0 := by positivity
      have h2 : R^2 / c > 0 := div_pos h1 hc
      exact add_pos h_R_pos h2 |> (fun h => div_pos h (by norm_num))
    have h_v0_gt_R : v0 > R := by
      have h1 : R * c < R^2 := by
        calc R * c < R * R := mul_lt_mul_of_pos_left hcR_lin h_R_pos
          _ = R^2 := by ring
      have h2 : R < R^2 / c := (lt_div_iff₀ hc).mpr h1
      calc v0 = (R + R^2 / c) / 2 := rfl
        _ > (R + R) / 2 := by linarith
        _ = R := by ring
    let v : Fin 4 → ℝ := fun i => if i = 0 then v0 else - u i
    have h_v0 : v 0 = v0 := rfl
    have h_v_cone : v ∈ forward_light_cone := by
      constructor
      · exact h_v0_pos
      · have h_inner_vv : minkowskiInner v v = v0^2 - R2 := by
          simp [minkowskiInner_explicit, v]
          calc v0 * v0 - u 1 * u 1 - u 2 * u 2 - u 3 * u 3
            _ = v0^2 - ((u 1)^2 + (u 2)^2 + (u 3)^2) := by ring
            _ = v0^2 - R2 := by rw [h_R2]
        rw [h_inner_vv]
        have hv0R : v0^2 > R^2 := by
          have hv0pos : v0 > 0 := h_v0_pos
          nlinarith
        linarith
    have h_uv_pos : minkowskiInner u v > 0 := by
      have h_inner : minkowskiInner u v = u 0 * v0 + R2 := by
        simp [minkowskiInner_explicit, v]
        calc u 0 * v0 + u 1 * u 1 + u 2 * u 2 + u 3 * u 3
          _ = u 0 * v0 + ((u 1)^2 + (u 2)^2 + (u 3)^2) := by ring
          _ = u 0 * v0 + R2 := by rw [h_R2]
      rw [h_inner]
      have h2 : u 0 * v0 = - (c * v0) := by
        have h_c : c = - u 0 := rfl
        linarith
      rw [h2]
      have h4 : c * v0 = (c * R + R^2) / 2 := by
        calc c * v0 = c * ((R + R^2 / c) / 2) := rfl
          _ = (c * R + c * (R^2 / c)) / 2 := by ring
          _ = (c * R + R^2) / 2 := by rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      have h5 : - (c * v0) + R2 = R2 - c * v0 := by ring
      rw [h5, h4, ←h_R]
      have hcR2 : c * R < R^2 := by
        calc c * R < R * R := mul_lt_mul_of_pos_right hcR_lin h_R_pos
          _ = R^2 := by ring
      linarith
    have h_le := h_le_zero v h_v_cone
    linarith
  · push Not at h_u0
    let v0 := R + 1
    have h_v0_gt_R : v0 > R := by linarith
    let v : Fin 4 → ℝ := fun i => if i = 0 then v0 else - u i
    have h_v0 : v 0 = v0 := rfl
    have h_v_cone : v ∈ forward_light_cone := by
      constructor
      · linarith
      · have h_inner_vv : minkowskiInner v v = v0^2 - R2 := by
          simp [minkowskiInner_explicit, v]
          calc v0 * v0 - u 1 * u 1 - u 2 * u 2 - u 3 * u 3
            _ = v0^2 - ((u 1)^2 + (u 2)^2 + (u 3)^2) := by ring
            _ = v0^2 - R2 := by rw [h_R2]
        rw [h_inner_vv]
        have hv0R : v0^2 > R^2 := by
          have hv0pos : v0 > 0 := by linarith
          nlinarith
        linarith
    have h_uv_pos : minkowskiInner u v > 0 := by
      have h_inner : minkowskiInner u v = u 0 * v0 + R2 := by
        simp [minkowskiInner_explicit, v]
        calc u 0 * v0 + u 1 * u 1 + u 2 * u 2 + u 3 * u 3
          _ = u 0 * v0 + ((u 1)^2 + (u 2)^2 + (u 3)^2) := by ring
          _ = u 0 * v0 + R2 := by rw [h_R2]
      rw [h_inner]
      have hv0pos : v0 > 0 := by linarith
      have hu0pos : u 0 ≥ 0 := h_u0
      have : u 0 * v0 ≥ 0 := mul_nonneg hu0pos (by linarith)
      linarith
    have h_le := h_le_zero v h_v_cone
    linarith

noncomputable def spatial_reflection (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let r := Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3)
  let v : Fin 4 → ℝ := fun i ↦ if i = 1 then u 1 else if i = 2 then u 2 else if i = 3 then u 3 - r else 0
  let v2_norm := v 1 * v 1 + v 2 * v 2 + v 3 * v 3
  if v2_norm = 0 then 1 else 1 - (2 / v2_norm) • Matrix.vecMulVec v v

lemma spatial_reflection_is_lorentz (u : Fin 4 → ℝ) :
  (spatial_reflection u)ᵀ * minkowskiMetricReal * (spatial_reflection u) = minkowskiMetricReal := by
  dsimp [spatial_reflection]
  split_ifs with h_v2
  · simp
  · let r := Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3)
    let v : Fin 4 → ℝ := fun i ↦ if i = 1 then u 1 else if i = 2 then u 2 else if i = 3 then u 3 - r else 0
    let v2_norm := v 1 * v 1 + v 2 * v 2 + v 3 * v 3
    let M := Matrix.vecMulVec v v
    let c := 2 / v2_norm
    change (1 - c • M)ᵀ * minkowskiMetricReal * (1 - c • M) = minkowskiMetricReal
    have h_M_trans : Mᵀ = M := by
      ext i j; dsimp [M, Matrix.vecMulVec, transpose_apply]; ring
    have h_eta_M : minkowskiMetricReal * M = -M := by
      ext i j; dsimp [M, Matrix.vecMulVec, Matrix.mul_apply, minkowskiMetricReal, v]; fin_cases i <;> fin_cases j <;> { simp_rw [Fin.sum_univ_four]; simp (config := {decide := true}); try ring }
    have h_M_eta : M * minkowskiMetricReal = -M := by
      ext i j; dsimp [M, Matrix.vecMulVec, Matrix.mul_apply, minkowskiMetricReal, v]; fin_cases i <;> fin_cases j <;> { simp_rw [Fin.sum_univ_four]; simp (config := {decide := true}); try ring }
    have h_M_sq : M * M = v2_norm • M := by
      ext i j; dsimp [M, Matrix.vecMulVec, Matrix.mul_apply, v2_norm, v, Matrix.smul_apply]; fin_cases i <;> fin_cases j <;> { simp_rw [Fin.sum_univ_four]; simp (config := {decide := true}); try ring }
    rw [transpose_sub, transpose_one, transpose_smul, h_M_trans]
    rw [sub_mul, mul_sub, one_mul, mul_one]
    rw [Matrix.smul_mul, h_M_eta, smul_neg, sub_neg_eq_add]
    rw [Matrix.mul_smul, Matrix.add_mul, h_eta_M, Matrix.smul_mul, h_M_sq]
    ext i j
    dsimp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Pi.neg_apply]
    have hc : c = 2 / v2_norm := rfl
    calc minkowskiMetricReal i j + c * M i j - c * (-M i j + c * (v2_norm * M i j))
      _ = minkowskiMetricReal i j + (2 * c - c * c * v2_norm) * M i j := by ring
      _ = minkowskiMetricReal i j + (2 * c - 2 * c) * M i j := by
        congr 2
        congr 1
        calc c * c * v2_norm
          _ = c * (c * v2_norm) := by ring
          _ = c * (2 / v2_norm * v2_norm) := by rw [hc]
          _ = c * 2 := by rw [div_mul_cancel₀ 2 (by exact h_v2)]
          _ = 2 * c := by ring
      _ = minkowskiMetricReal i j := by ring

noncomputable def boost_z (γ β : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 0 then γ
    else if i = 0 ∧ j = 3 then - γ * β
    else if i = 3 ∧ j = 0 then - γ * β
    else if i = 3 ∧ j = 3 then γ
    else if i = j then 1
    else 0

lemma boost_z_is_lorentz (γ β : ℝ) (h : γ ^ 2 - (γ * β) ^ 2 = 1) :
  (boost_z γ β)ᵀ * minkowskiMetricReal * (boost_z γ β) = minkowskiMetricReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    repeat rw [Fin.sum_univ_four]
    simp [boost_z, minkowskiMetricReal]
    try nlinarith
  }

lemma spatial_reflection_mulVec (u : Fin 4 → ℝ) :
  (spatial_reflection u) *ᵥ u = fun (i:Fin 4) ↦ if i = 0 then u 0 else if i = 3 then Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) else 0 := by
  dsimp [spatial_reflection]
  split_ifs with h_v2_eq
  · let r := Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3)
    have hu1 : u 1 = 0 := by nlinarith
    have hu2 : u 2 = 0 := by nlinarith
    have hu3 : u 3 = r := by nlinarith
    ext i
    dsimp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    simp_rw [Fin.sum_univ_four]
    fin_cases i
    · simp
    · simp; exact hu1
    · simp; exact hu2
    · simp; exact hu3
  · let r := Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3)
    let v : Fin 4 → ℝ := fun i ↦ if i = 1 then u 1 else if i = 2 then u 2 else if i = 3 then u 3 - r else 0
    let v2_norm := v 1 * v 1 + v 2 * v 2 + v 3 * v 3
    let c := 2 / v2_norm
    let M := Matrix.vecMulVec v v
    have hM_u : M *ᵥ u = (v 1 * u 1 + v 2 * u 2 + v 3 * u 3) • v := by
      ext i
      dsimp [M, Matrix.vecMulVec, Matrix.mulVec, dotProduct, v]
      simp_rw [Fin.sum_univ_four]
      fin_cases i <;> { simp (config := {decide := true}); try ring }
    have h_v_dot_u : v 1 * u 1 + v 2 * u 2 + v 3 * u 3 = v2_norm / 2 := by
      dsimp [v, v2_norm]
      have h_nonneg : 0 ≤ u 1 * u 1 + u 2 * u 2 + u 3 * u 3 := by
        calc 0 ≤ u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by positivity
             _ = u 1 * u 1 + u 2 * u 2 + u 3 * u 3 := by ring
      have hr2 : r ^ 2 = u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
        rw [Real.sq_sqrt h_nonneg]
        ring
      linarith [hr2]
    have hc_v_dot_u : c * (v 1 * u 1 + v 2 * u 2 + v 3 * u 3) = 1 := by
      rw [h_v_dot_u]
      dsimp [c]
      have hv2_ne_zero : v2_norm ≠ 0 := h_v2_eq
      calc 2 / v2_norm * (v2_norm / 2) = (2 / 2) * (v2_norm / v2_norm) := by ring
        _ = 1 * 1 := by rw [div_self (by norm_num), div_self hv2_ne_zero]
        _ = 1 := by ring

    change (1 - c • M) *ᵥ u = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hM_u]
    ext i
    dsimp [Matrix.sub_apply, Pi.smul_apply, Pi.sub_apply]
    rw [← mul_assoc, hc_v_dot_u, one_mul]
    dsimp [v, r]
    fin_cases i <;> { simp (config := {decide := true}); try ring }



lemma lorentz_align_timelike (u : Fin 4 → ℝ) (hu : minkowskiInner u u > 0) :
  ∃ Λ : RealLorentzGroup, ∀ i ≠ 0, (Λ • u) i = 0 := by
  let r2 := u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2
  let r := Real.sqrt r2
  have hr2_nonneg : 0 ≤ r2 := by
    dsimp [r2]; positivity
  have hu0_sq : u 0 ^ 2 > r2 := by
    have h_inner : minkowskiInner u u = u 0 * u 0 - u 1 * u 1 - u 2 * u 2 - u 3 * u 3 := minkowskiInner_explicit u u
    rw [h_inner] at hu
    dsimp [r2]
    calc u 0 ^ 2 = u 0 * u 0 := by ring
      _ > u 1 * u 1 + u 2 * u 2 + u 3 * u 3 := by linarith
      _ = u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by ring
  have hu0_ne_zero : u 0 ≠ 0 := by
    intro h
    rw [h] at hu0_sq
    linarith
  let β := r / u 0
  have hβ_sq : β ^ 2 < 1 := by
    dsimp [β]
    rw [div_pow]
    have h_r_sq : r ^ 2 = r2 := Real.sq_sqrt hr2_nonneg
    rw [h_r_sq]
    exact (div_lt_one (sq_pos_of_ne_zero hu0_ne_zero)).mpr hu0_sq
  let γ := 1 / Real.sqrt (1 - β^2)
  have hγ_β : γ ^ 2 - (γ * β) ^ 2 = 1 := by
    dsimp [γ]
    have h_sub_pos : 1 - β^2 > 0 := sub_pos.mpr hβ_sq
    have h_sqrt : (Real.sqrt (1 - β^2)) ^ 2 = 1 - β^2 := Real.sq_sqrt (by linarith)
    calc
      (1 / Real.sqrt (1 - β^2)) ^ 2 - (1 / Real.sqrt (1 - β^2) * β) ^ 2
        = 1 / (Real.sqrt (1 - β^2)) ^ 2 - β^2 / (Real.sqrt (1 - β^2)) ^ 2 := by ring
      _ = 1 / (1 - β^2) - β^2 / (1 - β^2) := by rw [h_sqrt]
      _ = (1 - β^2) / (1 - β^2) := by ring
      _ = 1 := div_self (ne_of_gt h_sub_pos)

  let Λ_mat := boost_z γ β * spatial_reflection u
  have hΛ_lorentz : Λ_matᵀ * minkowskiMetricReal * Λ_mat = minkowskiMetricReal := by
    dsimp [Λ_mat]
    rw [Matrix.transpose_mul]
    have h_assoc : (spatial_reflection u)ᵀ * (boost_z γ β)ᵀ * minkowskiMetricReal * (boost_z γ β * spatial_reflection u) = (spatial_reflection u)ᵀ * ((boost_z γ β)ᵀ * minkowskiMetricReal * boost_z γ β) * spatial_reflection u := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, boost_z_is_lorentz γ β hγ_β, spatial_reflection_is_lorentz u]

  have h_det_eta : minkowskiMetricReal.det = -1 := by
    have h1 : minkowskiMetricReal = Matrix.diagonal (fun (i:Fin 4) => if i = 0 then (1:ℝ) else -1) := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_four]
    simp
  have h_det_eq : Λ_mat.det ^ 2 * minkowskiMetricReal.det = minkowskiMetricReal.det := by
    have h1 := congr_arg Matrix.det hΛ_lorentz
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    calc Λ_mat.det ^ 2 * minkowskiMetricReal.det
      _ = Λ_mat.det * minkowskiMetricReal.det * Λ_mat.det := by ring
      _ = minkowskiMetricReal.det := h1
  have h_det_sq : Λ_mat.det ^ 2 = 1 := by
    rw [h_det_eta] at h_det_eq
    linarith
  have h_det_ne_zero : Λ_mat.det ≠ 0 := by
    intro h
    rw [h] at h_det_sq
    linarith
  have h_det : IsUnit Λ_mat.det := isUnit_iff_ne_zero.mpr h_det_ne_zero
  let Λ_GL : Matrix.GeneralLinearGroup (Fin 4) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero Λ_mat h_det_ne_zero
  have h_mem : Λ_GL.valᵀ * minkowskiMetricReal * Λ_GL.val = minkowskiMetricReal := hΛ_lorentz

  use ⟨Λ_GL, h_mem⟩
  intro i hi
  have h_action : Λ_mat *ᵥ u = fun (j:Fin 4) ↦ if j = 0 then γ * u 0 - γ * β * r else if j = 3 then -(γ * β * u 0) + γ * r else 0 := by
    dsimp [Λ_mat]
    rw [← Matrix.mulVec_mulVec, spatial_reflection_mulVec u]
    ext j
    dsimp [boost_z, Matrix.mulVec, dotProduct]
    simp_rw [Fin.sum_univ_four]
    fin_cases j
    · simp (config := {decide := true})
      have hr_eq : Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) = r := by
        dsimp [r, r2]
        congr 1
        ring
      rw [hr_eq]
      ring
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
    · simp (config := {decide := true})
      have hr_eq : Real.sqrt (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) = r := by
        dsimp [r, r2]
        congr 1
        ring
      rw [hr_eq]
      try left
      ring

  have h_goal : (Λ_mat *ᵥ u) i = 0 := by
    rw [h_action]
    fin_cases i <;> try contradiction
    · rfl
    · rfl
    · dsimp [β]
      have hβ_u0 : (r / u 0) * u 0 = r := div_mul_cancel₀ r hu0_ne_zero
      calc -(γ * (r / u 0) * u 0) + γ * r
        _ = -(γ * ((r / u 0) * u 0)) + γ * r := by ring
        _ = -(γ * r) + γ * r := by rw [hβ_u0]
        _ = 0 := by ring
  exact h_goal


lemma separating_hyperplane_pos (f : (Fin 4 → ℝ) →L[ℝ] ℝ) (s : ℝ)
  (h_cone : ∀ v ∈ forward_light_cone, f v < s) : s ≥ 0 := by
  by_contra h_neg
  push Not at h_neg
  let v1 : Fin 4 → ℝ := fun i => if i = 0 then (1:ℝ) else 0
  have hv1 : (1 : ℝ) > 0 := by positivity
  by_cases hf : f v1 ≥ 0
  · have h_in : v1 ∈ forward_light_cone := by
      constructor
      · exact hv1
      · simp [minkowskiInner_explicit, v1]
    have h_lt := h_cone v1 h_in
    linarith
  · push Not at hf
    let a := s / (2 * f v1)
    have ha : a > 0 := div_pos_of_neg_of_neg h_neg (mul_neg_of_pos_of_neg (by positivity) hf)
    let va : Fin 4 → ℝ := a • v1
    have hva0 : va 0 = a := by
      calc va 0
        _ = (a • v1) 0 := rfl
        _ = a * v1 0 := rfl
        _ = a * 1 := by simp [v1]
        _ = a := by ring
    have h_in : va ∈ forward_light_cone := by
      constructor
      · rw [hva0]; exact ha
      · simp [minkowskiInner_explicit, va, v1]
        positivity
    have h_lt := h_cone va h_in
    have h_eval : f va = a * f v1 := by
      have h1 : f va = f (a • v1) := rfl
      rw [h1, ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [h_eval] at h_lt
    have h_calc : a * f v1 = s / 2 := by
      calc a * f v1
        _ = (s / (2 * f v1)) * f v1 := rfl
        _ = (s / 2) / f v1 * f v1 := by ring
        _ = s / 2 := div_mul_cancel₀ (s / 2) (ne_of_lt hf)
    rw [h_calc] at h_lt
    linarith

open Complex

noncomputable def complex_boost_z (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![
    Real.cos θ, 0, 0, -I * Real.sin θ;
    0, 1, 0, 0;
    0, 0, 1, 0;
    -I * Real.sin θ, 0, 0, Real.cos θ
  ]

lemma complex_boost_z_det (θ : ℝ) : (complex_boost_z θ).det = 1 := by
  dsimp [complex_boost_z]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have h1 : ![0, 0, (1 : ℂ), 0] (Fin.succAbove 3 2) = 1 := rfl
  rw [h1]
  have h_eq : Complex.cos (θ:ℂ) * Complex.cos (θ:ℂ) + (-1) ^ 3 * (I * Complex.sin (θ:ℂ)) * (1 * (I * Complex.sin (θ:ℂ))) = Complex.cos (θ:ℂ) ^ 2 + Complex.sin (θ:ℂ) ^ 2 := by
    calc Complex.cos (θ:ℂ) * Complex.cos (θ:ℂ) + (-1) ^ 3 * (I * Complex.sin (θ:ℂ)) * (1 * (I * Complex.sin (θ:ℂ)))
      _ = Complex.cos (θ:ℂ) ^ 2 - (I * Complex.sin (θ:ℂ)) ^ 2 := by ring
      _ = Complex.cos (θ:ℂ) ^ 2 - (I ^ 2 * Complex.sin (θ:ℂ) ^ 2) := by ring
      _ = Complex.cos (θ:ℂ) ^ 2 - (-1 * Complex.sin (θ:ℂ) ^ 2) := by rw [I_sq]
      _ = Complex.cos (θ:ℂ) ^ 2 + Complex.sin (θ:ℂ) ^ 2 := by ring
  rw [h_eq]
  exact Complex.cos_sq_add_sin_sq (θ:ℂ)

lemma complex_boost_z_is_lorentz (θ : ℝ) :
  (complex_boost_z θ)ᵀ * minkowskiMetric * (complex_boost_z θ) = minkowskiMetric := by
  have hi : Complex.I * Complex.I = -1 := by rw [← sq]; exact Complex.I_sq
  have h_cs : (Complex.cos (θ:ℂ))^2 + (Complex.sin (θ:ℂ))^2 = 1 := Complex.cos_sq_add_sin_sq (θ:ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    calc Complex.cos ↑θ * Complex.cos ↑θ + -(Complex.I * Complex.sin ↑θ * (Complex.I * Complex.sin ↑θ))
        = (Complex.cos ↑θ)^2 - Complex.I * Complex.I * (Complex.sin ↑θ)^2 := by ring
      _ = (Complex.cos ↑θ)^2 - (-1) * (Complex.sin ↑θ)^2 := by rw [hi]
      _ = (Complex.cos ↑θ)^2 + (Complex.sin ↑θ)^2 := by ring
      _ = 1 := h_cs
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    ring
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    ring
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
  · simp [Matrix.mul_apply, complex_boost_z, minkowskiMetric]; repeat rw [Fin.sum_univ_four]; simp
    calc Complex.I * Complex.sin ↑θ * (Complex.I * Complex.sin ↑θ) + -(Complex.cos ↑θ * Complex.cos ↑θ)
        = Complex.I * Complex.I * (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 := by ring
      _ = (-1) * (Complex.sin ↑θ)^2 - (Complex.cos ↑θ)^2 := by rw [hi]
      _ = -((Complex.cos ↑θ)^2 + (Complex.sin ↑θ)^2) := by ring
      _ = -(1 : ℂ) := by rw [h_cs]
      _ = -1 := by ring


lemma complex_boost_z_action (θ : ℝ) (w : Fin 4 → ℝ) :
  (fun k => -((complex_boost_z θ).mulVec (fun i => (w i : ℂ)) k).im) =
  fun k => if k = 0 then (Real.sin θ) * w 3 else if k = 3 then (Real.sin θ) * w 0 else 0 := by
  ext k
  fin_cases k
  · simp [mulVec, dotProduct, complex_boost_z]
    repeat rw [Fin.sum_univ_four]
    simp
    left
    have h : Complex.sin ↑θ = ↑(Real.sin θ) := by rw [← ofReal_sin]
    rw [h]
    rfl
  · simp [mulVec, dotProduct, complex_boost_z]
    repeat rw [Fin.sum_univ_four]
    simp
  · simp [mulVec, dotProduct, complex_boost_z]
    repeat rw [Fin.sum_univ_four]
    simp
  · simp [mulVec, dotProduct, complex_boost_z]
    repeat rw [Fin.sum_univ_four]
    simp
    left
    have h : Complex.sin ↑θ = ↑(Real.sin θ) := by rw [← ofReal_sin]
    rw [h]
    rfl

lemma complex_boost_z_maps_to_cone (θ : ℝ) (hθ_sin : Real.sin θ > 0) (w : Fin 4 → ℝ)
  (h_spacelike : minkowskiInner w w < 0) (h_z : w 3 > |w 0|) :
  (fun k => -((complex_boost_z θ).mulVec (fun i => (w i : ℂ)) k).im) ∈ forward_light_cone := by
  have hy_eq : (fun k => -((complex_boost_z θ).mulVec (fun i => (w i : ℂ)) k).im) =
               fun k => if k = 0 then (Real.sin θ) * w 3 else if k = 3 then (Real.sin θ) * w 0 else 0 :=
    complex_boost_z_action θ w
  have hy_k (k : Fin 4) : -((complex_boost_z θ).mulVec (fun i => (w i : ℂ)) k).im =
                          if k = 0 then (Real.sin θ) * w 3 else if k = 3 then (Real.sin θ) * w 0 else 0 :=
    congr_fun hy_eq k
  rw [forward_light_cone]
  simp only [Set.mem_setOf_eq]
  
  have h_y0 : (if (0 : Fin 4) = 0 then Real.sin θ * w 3 else if (0 : Fin 4) = 3 then Real.sin θ * w 0 else 0) = Real.sin θ * w 3 := by rfl
  have h_y1 : (if (1 : Fin 4) = 0 then Real.sin θ * w 3 else if (1 : Fin 4) = 3 then Real.sin θ * w 0 else 0) = 0 := by rfl
  have h_y2 : (if (2 : Fin 4) = 0 then Real.sin θ * w 3 else if (2 : Fin 4) = 3 then Real.sin θ * w 0 else 0) = 0 := by rfl
  have h_y3 : (if (3 : Fin 4) = 0 then Real.sin θ * w 3 else if (3 : Fin 4) = 3 then Real.sin θ * w 0 else 0) = Real.sin θ * w 0 := by rfl

  constructor
  · 
    simp only [hy_k]
    change (if (0 : Fin 4) = 0 then Real.sin θ * w 3 else if (0 : Fin 4) = 3 then Real.sin θ * w 0 else 0) > 0
    rw [h_y0]
    have hw3 : w 3 > 0 := by
      calc
        w 3 > |w 0| := h_z
        _ ≥ 0 := abs_nonneg (w 0)
    positivity
  · 
    simp only [hy_k]
    rw [minkowskiInner_explicit]
    rw [h_y0, h_y1, h_y2, h_y3]
    have : (Real.sin θ * w 3) * (Real.sin θ * w 3) - 0 * 0 - 0 * 0 - (Real.sin θ * w 0) * (Real.sin θ * w 0) =
         (Real.sin θ)^2 * ((w 3)^2 - (w 0)^2) := by ring
    rw [this]
    have hs : (Real.sin θ)^2 > 0 := sq_pos_of_pos hθ_sin
    have hw : (w 3)^2 > (w 0)^2 := by
      have h1 : w 3 > |w 0| := h_z
      have h2 : |w 0| ≥ 0 := abs_nonneg (w 0)
      have h3 : |w 0|^2 = (w 0)^2 := sq_abs (w 0)
      nlinarith
    positivity

lemma complex_boost_maps_to_tube (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hn : n > 1)
  (hx : x ∈ jost_points_n n)
  (u : Fin 4 → ℝ) (hu : ¬ is_spacelike u)
  (h_hull : ∀ w ∈ jost_convex_hull n x, minkowskiInner u w ≥ 0) :
  coeReal n x ∈ extended_tube_n n := by
  have hK_compact : IsCompact (jost_convex_hull n x) := jost_convex_hull_compact n x
  have hK_convex : Convex ℝ (jost_convex_hull n x) := convex_convexHull ℝ _
  have hK_space : ∀ w ∈ jost_convex_hull n x, is_spacelike w := hx
  obtain ⟨Λ_R, hΛ_lorentz, hΛ_det, hΛ_w⟩ := bhw_geometric_lemma _ hK_compact hK_convex hK_space u hu h_hull

  
  
  
  have h_theta : Real.sin (Real.pi / 2) > 0 := by norm_num

  
  let lift_matrix (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (A i j : ℂ)
  have h_lift_mul : ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ), lift_matrix (A * B) = lift_matrix A * lift_matrix B := by
    intro A B; ext i j
    simp [lift_matrix, Matrix.mul_apply, Fin.sum_univ_four]
  have h_lift_transpose : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ), (lift_matrix A)ᵀ = lift_matrix Aᵀ := by
    intro A; rfl
  have h_lift_det : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ), (lift_matrix A).det = (A.det : ℂ) := by
    intro A
    have h : lift_matrix A = (algebraMap ℝ ℂ).mapMatrix A := rfl
    rw [h]
    exact (RingHom.map_det (algebraMap ℝ ℂ) A).symm

  have real_lorentz_preserves_inner (Λ_val : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ_valᵀ * minkowskiMetricReal * Λ_val = minkowskiMetricReal) (v : Fin 4 → ℝ) :
    minkowskiInner (Λ_val *ᵥ v) (Λ_val *ᵥ v) = minkowskiInner v v := by
    dsimp [minkowskiInner]
    have h1 : dotProduct (Λ_val *ᵥ v) (minkowskiMetricReal *ᵥ (Λ_val *ᵥ v)) = dotProduct v (Λ_valᵀ *ᵥ (minkowskiMetricReal *ᵥ (Λ_val *ᵥ v))) := by
      dsimp [dotProduct, Matrix.mulVec]
      simp [Fin.sum_univ_four]
      ring
    rw [h1]
    have h2 : Λ_valᵀ *ᵥ (minkowskiMetricReal *ᵥ (Λ_val *ᵥ v)) = (Λ_valᵀ * minkowskiMetricReal * Λ_val) *ᵥ v := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h2, hΛ]

  have h_minkowskiMetric_sq : minkowskiMetric * minkowskiMetric = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four]

  have complex_lorentz_inv (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : Aᵀ * minkowskiMetric * A = minkowskiMetric) :
    A * (minkowskiMetric * Aᵀ * minkowskiMetric) = 1 ∧ (minkowskiMetric * Aᵀ * minkowskiMetric) * A = 1 := by
    have h_left : (minkowskiMetric * Aᵀ * minkowskiMetric) * A = 1 := by
      have h1 : (minkowskiMetric * Aᵀ * minkowskiMetric) * A = minkowskiMetric * (Aᵀ * minkowskiMetric * A) := by
        simp [Matrix.mul_assoc]
      rw [h1, hA, h_minkowskiMetric_sq]
    have h_right : A * (minkowskiMetric * Aᵀ * minkowskiMetric) = 1 := mul_eq_one_comm.mpr h_left
    exact ⟨h_right, h_left⟩

  have h_exists_Λ : ∃ (Λ : SpecialSpecialComplexLorentzGroup),
    ∃ (z : Fin n → Fin 4 → ℂ), z ∈ forward_tube_n n ∧ Λ • z = coeReal n x := by
    let Λ_C_val := lift_matrix Λ_R.val
    have h_Λ_C_lorentz : Λ_C_valᵀ * minkowskiMetric * Λ_C_val = minkowskiMetric := by
      have h1 : lift_matrix minkowskiMetricReal = minkowskiMetric := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [lift_matrix, minkowskiMetricReal, minkowskiMetric]
      have h2 := congrArg lift_matrix hΛ_lorentz
      rw [h_lift_mul, h_lift_mul, ← h_lift_transpose, h1] at h2
      exact h2
    let Λ_C_GL : Matrix.GeneralLinearGroup (Fin 4) ℂ :=
      { val := Λ_C_val,
        inv := minkowskiMetric * Λ_C_valᵀ * minkowskiMetric,
        val_inv := (complex_lorentz_inv _ h_Λ_C_lorentz).1,
        inv_val := (complex_lorentz_inv _ h_Λ_C_lorentz).2 }

    have h_Λ_C_det : Λ_C_GL.val.det = 1 := by
      change (lift_matrix Λ_R.val).det = 1
      rw [h_lift_det]
      change (Λ_R.val.det : ℂ) = 1
      rw [hΛ_det]
      simp

    let Λ_C : SpecialSpecialComplexLorentzGroup := ⟨Λ_C_GL, h_Λ_C_lorentz, h_Λ_C_det⟩

    let B_val := complex_boost_z (Real.pi / 2)
    have h_B_lorentz : B_valᵀ * minkowskiMetric * B_val = minkowskiMetric := complex_boost_z_is_lorentz _
    let B_GL : Matrix.GeneralLinearGroup (Fin 4) ℂ :=
      { val := B_val,
        inv := minkowskiMetric * B_valᵀ * minkowskiMetric,
        val_inv := (complex_lorentz_inv _ h_B_lorentz).1,
        inv_val := (complex_lorentz_inv _ h_B_lorentz).2 }
    have h_B_det : B_GL.val.det = 1 := complex_boost_z_det _
    let B_C : SpecialSpecialComplexLorentzGroup := ⟨B_GL, h_B_lorentz, h_B_det⟩

    let Λ := Λ_C⁻¹ * B_C⁻¹
    let z := fun i j => Matrix.mulVec B_val (Matrix.mulVec Λ_C_val (fun k => (x i k : ℂ))) j
    use Λ
    use z
    constructor
    · 
      dsimp [forward_tube_n]
      intro i hi
      let w : Fin 4 → ℝ := fun k => (Λ_R.val *ᵥ fun j => (x i j - x ⟨i.val + 1, hi⟩ j)) k
      have hw_hull : (fun k => x i k - x ⟨i.val + 1, hi⟩ k) ∈ jost_convex_hull n x := by
        apply subset_convexHull
        simp only [jost_differences_n, Set.mem_setOf_eq]
        use i
        use hi
        ext k
        rfl
      have h_w_wedge : |w 0| < w 3 := hΛ_w _ hw_hull
      have h_w_space : minkowskiInner w w < 0 := by
        have hw_diff_space : minkowskiInner (fun k => x i k - x ⟨i.val + 1, hi⟩ k) (fun k => x i k - x ⟨i.val + 1, hi⟩ k) < 0 :=
          hK_space _ hw_hull
        have h_w_eq_inner : minkowskiInner w w = minkowskiInner (fun k => x i k - x ⟨i.val + 1, hi⟩ k) (fun k => x i k - x ⟨i.val + 1, hi⟩ k) := by
          have hw_def : w = Λ_R.val *ᵥ (fun j => (x i j - x ⟨i.val + 1, hi⟩ j)) := rfl
          rw [hw_def]
          exact real_lorentz_preserves_inner Λ_R.val hΛ_lorentz _
        rw [h_w_eq_inner]
        exact hw_diff_space
      have h_im : (fun k => -((B_val *ᵥ (fun k => (w k : ℂ))) k).im) ∈ forward_light_cone := by
        apply complex_boost_z_maps_to_cone (Real.pi / 2)
        · norm_num
        · exact h_w_space
        · exact h_w_wedge
      have h_z_diff : (fun k => (z i k - z ⟨i.val + 1, hi⟩ k)) = fun k => (B_val *ᵥ (fun k => (w k : ℂ))) k := by
        ext k
        dsimp [z, w, B_val, Λ_C_val, lift_matrix, Matrix.mulVec, dotProduct]
        simp [Fin.sum_univ_four]
        push_cast
        ring
      have h_eq : (fun k => -((z i k).im - (z ⟨i.val + 1, hi⟩ k).im)) = (fun k => -((B_val *ᵥ (fun k => (w k : ℂ))) k).im) := by
        ext k
        have h_z_diff_k : (z i k - z ⟨i.val + 1, hi⟩ k) = (B_val *ᵥ (fun k => (w k : ℂ))) k := congr_fun h_z_diff k
        have h_im_diff : (z i k - z ⟨i.val + 1, hi⟩ k).im = (z i k).im - (z ⟨i.val + 1, hi⟩ k).im := rfl
        rw [← h_im_diff, h_z_diff_k]
      rw [h_eq]
      exact h_im
    · 
      ext i j
      have h1 : B_GL.inv * B_val = 1 := B_GL.inv_val
      have h2 : Λ_C_GL.inv * Λ_C_val = 1 := Λ_C_GL.inv_val
      have h_Λ_val : (Λ.val : Matrix (Fin 4) (Fin 4) ℂ) = Λ_C_GL.inv * B_GL.inv := rfl
      have h_z_val : z i = B_val *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)) := rfl
      have hd : (Λ • z) i = Λ.val *ᵥ (z i) := rfl
      have hd_j : (Λ • z) i j = (Λ.val *ᵥ (z i)) j := rfl
      rw [hd_j, h_Λ_val, h_z_val]
      have h_assoc1 : ((Λ_C_GL.inv * B_GL.inv) *ᵥ (B_val *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)))) =
                      Λ_C_GL.inv *ᵥ (B_GL.inv *ᵥ (B_val *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)))) :=
        by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have h_assoc2 : B_GL.inv *ᵥ (B_val *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ))) =
                      (B_GL.inv * B_val) *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)) :=
        by simp only [←Matrix.mulVec_mulVec]
      have h_assoc3 : Λ_C_GL.inv *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)) =
                      (Λ_C_GL.inv * Λ_C_val) *ᵥ fun k => (x i k : ℂ) :=
        by simp only [←Matrix.mulVec_mulVec]
      have h_full : ((Λ_C_GL.inv * B_GL.inv) *ᵥ (B_val *ᵥ (Λ_C_val *ᵥ fun k => (x i k : ℂ)))) j = (x i j : ℂ) := by
        rw [h_assoc1, h_assoc2, h1, Matrix.one_mulVec, h_assoc3, h2, Matrix.one_mulVec]
      exact h_full

  rw [extended_tube_n]
  simp only [Set.mem_iUnion, Set.mem_image]
  exact h_exists_Λ

noncomputable def minkowskiInnerC (z w : Fin 4 → ℂ) : ℂ :=
  z 0 * w 0 - z 1 * w 1 - z 2 * w 2 - z 3 * w 3

lemma dotProduct_mulVec_left (M : Matrix (Fin 4) (Fin 4) ℂ) (v w : Fin 4 → ℂ) :
  dotProduct (M.mulVec v) w = dotProduct v (Mᵀ.mulVec w) := by
  dsimp [dotProduct, Matrix.mulVec, Matrix.transpose]
  simp [Fin.sum_univ_four]
  ring

noncomputable def minkowskiInnerC_alt (z w : Fin 4 → ℂ) : ℂ :=
  dotProduct z (minkowskiMetric.mulVec w)

lemma minkowskiInnerC_eq_alt (z w : Fin 4 → ℂ) :
  minkowskiInnerC z w = minkowskiInnerC_alt z w := by
  dsimp [minkowskiInnerC, minkowskiInnerC_alt, dotProduct, Matrix.mulVec, minkowskiMetric]
  simp [Fin.sum_univ_four]
  ring

lemma complex_lorentz_preserves_inner_alt (Λ : SpecialSpecialComplexLorentzGroup) (z : Fin 4 → ℂ) :
  minkowskiInnerC_alt ((Λ.val.val).mulVec z) ((Λ.val.val).mulVec z) = minkowskiInnerC_alt z z := by
  dsimp [minkowskiInnerC_alt]
  have h_lorentz : (Λ.val.val)ᵀ * minkowskiMetric * (Λ.val.val) = minkowskiMetric := Λ.property.1
  have h1 : dotProduct ((Λ.val.val).mulVec z) (minkowskiMetric.mulVec ((Λ.val.val).mulVec z)) =
            dotProduct z (((Λ.val.val)ᵀ * minkowskiMetric * (Λ.val.val)).mulVec z) := by
    rw [dotProduct_mulVec_left]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec]
  rw [h1, h_lorentz]

lemma complex_lorentz_preserves_inner (Λ : SpecialSpecialComplexLorentzGroup) (z : Fin 4 → ℂ) :
  minkowskiInnerC ((Λ.val.val).mulVec z) ((Λ.val.val).mulVec z) = minkowskiInnerC z z := by
  rw [minkowskiInnerC_eq_alt, minkowskiInnerC_eq_alt, complex_lorentz_preserves_inner_alt Λ z]

lemma minkowskiInner_eq (x y : Fin 4 → ℝ) :
  minkowskiInner x y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  dsimp [minkowskiInner, minkowskiMetricReal, dotProduct, Matrix.mulVec]
  simp [Fin.sum_univ_four]
  ring

lemma minkowskiInnerC_real_im (u v : Fin 4 → ℝ) :
  minkowskiInnerC (fun i => u i - I * v i) (fun i => u i - I * v i) =
  (minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ) := by
  dsimp [minkowskiInnerC]
  rw [minkowskiInner_eq u u, minkowskiInner_eq v v, minkowskiInner_eq u v]
  push_cast
  have hI : I ^ 2 = -1 := I_sq
  calc
    (u 0 - I * v 0) * (u 0 - I * v 0) - (u 1 - I * v 1) * (u 1 - I * v 1) - (u 2 - I * v 2) * (u 2 - I * v 2) - (u 3 - I * v 3) * (u 3 - I * v 3)
    _ = (u 0 * u 0 - u 1 * u 1 - u 2 * u 2 - u 3 * u 3)
        - (v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3)
        - 2 * I * (u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3) := by
          linear_combination (v 0^2 - v 1^2 - v 2^2 - v 3^2) * hI

lemma orthogonal_to_timelike_is_spacelike (u v : Fin 4 → ℝ) (hv : minkowskiInner v v > 0)
  (h_ortho : minkowskiInner u v = 0) : minkowskiInner u u ≤ 0 := by
  rw [minkowskiInner_eq] at *
  have hv1 : v 0 ^ 2 > v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by linarith [hv]
  have hv_pos : v 0 ^ 2 > 0 := by
    have hsq : 0 ≤ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by positivity
    linarith
  have ho : u 0 * v 0 = u 1 * v 1 + u 2 * v 2 + u 3 * v 3 := by linarith [h_ortho]
  have ho2 : (u 0 * v 0) ^ 2 = (u 1 * v 1 + u 2 * v 2 + u 3 * v 3) ^ 2 := by rw [ho]
  have cs : (u 1 * v 1 + u 2 * v 2 + u 3 * v 3) ^ 2 ≤ (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
    have id : (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) - (u 1 * v 1 + u 2 * v 2 + u 3 * v 3) ^ 2 =
      (u 1 * v 2 - u 2 * v 1) ^ 2 + (u 1 * v 3 - u 3 * v 1) ^ 2 + (u 2 * v 3 - u 3 * v 2) ^ 2 := by ring
    linarith [sq_nonneg (u 1 * v 2 - u 2 * v 1), sq_nonneg (u 1 * v 3 - u 3 * v 1), sq_nonneg (u 2 * v 3 - u 3 * v 2)]
  have h_bound : u 0 ^ 2 * v 0 ^ 2 ≤ (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
    calc u 0 ^ 2 * v 0 ^ 2 = (u 0 * v 0) ^ 2 := by ring
         _ = (u 1 * v 1 + u 2 * v 2 + u 3 * v 3) ^ 2 := ho2
         _ ≤ (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := cs
  have h_pos_u : 0 ≤ u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by positivity
  have h_bound2 : (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) ≤ (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * v 0 ^ 2 := by
    nlinarith
  have h_final : u 0 ^ 2 * v 0 ^ 2 ≤ (u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) * v 0 ^ 2 := by linarith
  have h_div : u 0 ^ 2 ≤ u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
    nlinarith
  linarith

lemma jost_backward_invariant_core (z : Fin 4 → ℂ) (h_tube : (fun i => -(z i).im) ∈ forward_light_cone)
  (Λ : SpecialSpecialComplexLorentzGroup)
  (h_real : ∀ i, ((Λ.val.val).mulVec z i).im = 0) :
  is_spacelike (fun i => ((Λ.val.val).mulVec z i).re) := by
  have h_v_pos : minkowskiInner (fun i => -(z i).im) (fun i => -(z i).im) > 0 := h_tube.2
  have h_pres : minkowskiInnerC ((Λ.val.val).mulVec z) ((Λ.val.val).mulVec z) = minkowskiInnerC z z :=
    complex_lorentz_preserves_inner Λ z

  set W := (Λ.val.val).mulVec z
  have hW_im : ∀ i, (W i).im = 0 := h_real
  have hW_eq : W = fun i => ((W i).re : ℂ) := by
    ext i
    apply Complex.ext
    · simp
    · simp [hW_im i]

  have h_W_sq : minkowskiInnerC W W = (minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ) := by
    rw [hW_eq, minkowskiInner_eq]
    dsimp [minkowskiInnerC]
    push_cast
    ring

  set u := fun i => (z i).re
  set v := fun i => -(z i).im
  have hz_eq : z = fun i => (u i : ℂ) - I * (v i : ℂ) := by
    ext i
    apply Complex.ext
    · simp [u, v]
    · simp [u, v]

  have hz_sq : minkowskiInnerC z z = (minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ) := by
    calc minkowskiInnerC z z = minkowskiInnerC (fun i => (u i : ℂ) - I * (v i : ℂ)) (fun i => (u i : ℂ) - I * (v i : ℂ)) := by rw [hz_eq]
         _ = (minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ) := minkowskiInnerC_real_im u v

  have h_eq : (minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ) =
              (minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ) := by
    rw [← h_W_sq, ← hz_sq, h_pres]

  have h_im : ((minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ)).im =
              ((minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ)).im := by
    rw [h_eq]

  have h_im_LHS : ((minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ)).im = 0 := by
    simp

  have h_im_RHS : ((minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ)).im =
                  -2 * (minkowskiInner u v) := by
    simp

  rw [h_im_LHS, h_im_RHS] at h_im
  have h_ortho : minkowskiInner u v = 0 := by linarith

  have h_u_space : minkowskiInner u u ≤ 0 := orthogonal_to_timelike_is_spacelike u v h_v_pos h_ortho

  have h_re : ((minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ)).re =
              ((minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ)).re := by
    rw [h_eq]

  have h_re_LHS : ((minkowskiInner (fun i => (W i).re) (fun i => (W i).re) : ℂ)).re =
                  minkowskiInner (fun i => (W i).re) (fun i => (W i).re) := by
    simp

  have h_re_RHS : ((minkowskiInner u u : ℂ) - (minkowskiInner v v : ℂ) - 2 * I * (minkowskiInner u v : ℂ)).re =
                  minkowskiInner u u - minkowskiInner v v := by
    simp

  rw [h_re_LHS, h_re_RHS] at h_re

  dsimp [is_spacelike]
  linarith

lemma jost_backward_invariant (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hn : n > 1)
  (h_ext : coeReal n x ∈ extended_tube_n n) :
  x ∈ jost_points_n n := by
  dsimp [extended_tube_n] at h_ext
  rw [Set.mem_iUnion] at h_ext
  rcases h_ext with ⟨Λ, h_ext⟩
  rw [Set.mem_image] at h_ext
  rcases h_ext with ⟨z, hz_tube, hz_eq⟩

  dsimp [jost_points_n]
  intro v hv

  dsimp [jost_convex_hull] at hv
  rw [mem_convexHull_iff_exists_fintype] at hv
  rcases hv with ⟨ι, h_fintype, w, v_i, hw_nonneg, hw_sum, hv_in, hv_eq⟩

  have h_exists : ∀ i : ι, ∃ (j : Fin n) (hj : j.val + 1 < n), v_i i = x j - x ⟨j.val + 1, hj⟩ := by
    intro i
    exact hv_in i

  choose j hj h_vi using h_exists

  set Z_i : ι → Fin 4 → ℂ := fun i => z (j i) - z ⟨(j i).val + 1, hj i⟩
  set Z := ∑ i, w i • Z_i i

  have h_tube_Z : (fun k => -(Z k).im) ∈ forward_light_cone := by
    have h_im_sum : (fun k => -(Z k).im) = ∑ i, w i • (fun k => -(Z_i i k).im) := by
      ext k
      dsimp [Z]
      have : ((∑ i, w i • Z_i i) k).im = ∑ i, w i * (Z_i i k).im := by
        have h1 : ((∑ i, w i • Z_i i) k) = ∑ i, (w i : ℂ) * (Z_i i k) := by simp
        rw [h1]
        simp
      rw [this]
      simp [Finset.sum_neg_distrib]
    rw [h_im_sum]
    apply Convex.sum_mem forward_light_cone_convex
    · intro i _
      exact hw_nonneg i
    · exact hw_sum
    · intro i _
      exact hz_tube (j i) (hj i)

  have h_Lam_Z_i : ∀ i, (Λ.val.val).mulVec (Z_i i) = fun k => (v_i i k : ℂ) := by
    intro i
    have hz1 : (Λ.val.val).mulVec (z (j i)) = fun k => (x (j i) k : ℂ) := by
      have := congr_fun hz_eq (j i)
      exact this
    have hz2 : (Λ.val.val).mulVec (z ⟨(j i).val + 1, hj i⟩) = fun k => (x ⟨(j i).val + 1, hj i⟩ k : ℂ) := by
      have := congr_fun hz_eq ⟨(j i).val + 1, hj i⟩
      exact this
    ext k
    dsimp [Z_i]
    have : ((Λ.val.val).mulVec (z (j i) - z ⟨(j i).val + 1, hj i⟩)) k =
           ((Λ.val.val).mulVec (z (j i))) k - ((Λ.val.val).mulVec (z ⟨(j i).val + 1, hj i⟩)) k := by
      simp [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [this, hz1, hz2, h_vi i]
    simp

  have h_Lam_Z : (Λ.val.val).mulVec Z = fun k => (v k : ℂ) := by
    dsimp [Z]
    have : (Λ.val.val).mulVec (∑ i, w i • Z_i i) = ∑ i, w i • ((Λ.val.val).mulVec (Z_i i)) := by
      ext k
      simp [mulVec, dotProduct]
      have h1 : (∑ j_1 : Fin 4, (Λ.val.val) k j_1 * ∑ i : ι, ↑(w i) * Z_i i j_1) =
                ∑ j_1 : Fin 4, ∑ i : ι, (Λ.val.val) k j_1 * (↑(w i) * Z_i i j_1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      have h2 : (∑ i : ι, ↑(w i) * ∑ j_1 : Fin 4, (Λ.val.val) k j_1 * Z_i i j_1) =
                ∑ i : ι, ∑ j_1 : Fin 4, ↑(w i) * ((Λ.val.val) k j_1 * Z_i i j_1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      rw [h1, h2, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this]
    ext k
    have h_v_k : (v k : ℂ) = ((∑ i, w i • v_i i) k : ℂ) := by rw [hv_eq]
    rw [h_v_k]
    simp [h_Lam_Z_i]

  have h_real_Z : ∀ k, ((Λ.val.val).mulVec Z k).im = 0 := by
    intro k
    rw [h_Lam_Z]
    simp

  have h_v_eq : v = fun k => ((Λ.val.val).mulVec Z k).re := by
    ext k
    rw [h_Lam_Z]
    simp

  have h_core := jost_backward_invariant_core Z h_tube_Z Λ h_real_Z
  rw [← h_v_eq] at h_core
  exact h_core


theorem jost_theorem (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hn : n > 1) :
  x ∈ jost_points_n n ↔ coeReal n x ∈ extended_tube_n n := by
  constructor
  · intro hx
    have ⟨f, s, h_cone, h_hull⟩ := jost_separation n x hx
    have ⟨u, hu_riesz⟩ := minkowski_riesz f
    have h_cone' : ∀ v ∈ forward_light_cone, minkowskiInner u v < s := by
      intro v hv
      rw [←hu_riesz v]
      exact h_cone v hv
    have h_time := separating_vector_is_timelike u s h_cone'
    have h_hull' : ∀ w ∈ jost_convex_hull n x, minkowskiInner u w ≥ 0 := by
      intro w hw
      have h_f : f w = minkowskiInner u w := hu_riesz w
      have h_s_nonneg : s ≥ 0 := separating_hyperplane_pos f s h_cone
      have h_s_w : s ≤ f w := h_hull w hw
      linarith
    exact complex_boost_maps_to_tube n x hn hx u h_time h_hull'
  · intro h_ext
    exact jost_backward_invariant n x hn h_ext


end Geometry
