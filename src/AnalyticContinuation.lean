import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Matrix.Normed
import OsterwalderSchrader
import Minkowski
import Wightman
import Lightcone
import Spinor
import SL2CManifold
import PolarDecomposition
import SCVAnalysis
namespace QFT

open Matrix
open scoped InnerProductSpace
open scoped NNReal
open Complex
open Filter
open Topology
open SchwartzMap
open Geometry

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedAddCommGroup
noncomputable local instance : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Pi.normedSpace


variable {StateSpace : Type} [NormedAddCommGroup StateSpace] [InnerProductSpace ℂ StateSpace]

structure TubeDomainContinuation (StateSpace : Type) [NormedAddCommGroup StateSpace] [InnerProductSpace ℂ StateSpace] where

  schwinger : ℝ → (Fin 3 → ℝ) → ℂ

  wightman : ℝ → (Fin 3 → ℝ) → ℂ

  tube_function : ℂ → (Fin 3 → ℝ) → ℂ

  is_analytic : ∀ (x : Fin 3 → ℝ), AnalyticOn ℂ (fun z => tube_function z x) {z : ℂ | z.im < 0}

  boundary_limit : ∀ (t : ℝ) (x : Fin 3 → ℝ),
    Tendsto (fun (τ : ℝ) => tube_function (t - τ * I) x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (wightman t x))

  schwinger_relation : ∀ (τ : ℝ) (x : Fin 3 → ℝ), τ > 0 →
    tube_function (-τ * I) x = schwinger τ x

structure MultivariateTubeDomainContinuationN (n : ℕ) where

  schwinger : TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ

  wightman : TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ

  tube_function : (Fin n → Fin 4 → ℂ) → ℂ

  is_analytic : AnalyticOn ℂ tube_function (extended_tube_n n)


  tube_smeared : (Fin n → Fin 4 → ℝ) → SchwartzMap (Fin n → Fin 4 → ℝ) ℂ → ℂ



  boundary_limit : ∀ (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    Tendsto (fun (η : Fin n → Fin 4 → ℝ) => tube_smeared η f)
    (nhdsWithin 0 { η | ∀ i, η i ∈ forward_light_cone }) (nhds (wightman f))

  schwinger_relation : Prop

theorem analytic_continuation_spectral_gap_preservation
    (os : OsterwalderSchrader StateSpace)
    (Δ : ℝ)
    (h_spectral_gap : Δ > 0 ∧
    ∀ (Ψ : StateSpace), ⟪os.vacuum, Ψ⟫_ℂ = 0 →
      ∀ (t : NNReal), t > 0 →
        (⟪Ψ, os.timeEvolution.toFun t Ψ⟫_ℂ).re ≤ Real.exp (-Δ * (t : ℝ)) * (⟪Ψ, Ψ⟫_ℂ).re) :
    Δ > 0 ∧
    ∀ (Ψ : StateSpace), ⟪os.vacuum, Ψ⟫_ℂ = 0 →
      ∀ (t : NNReal), t > 0 →
        (⟪Ψ, os.timeEvolution.toFun t Ψ⟫_ℂ).re ≤ Real.exp (-Δ * (t : ℝ)) * (⟪Ψ, Ψ⟫_ℂ).re :=
  h_spectral_gap


def complex_lorentz_action (A B Z : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * Z * Bᵀ

noncomputable def matrix_lorentz_bilin (Z0 : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => LinearMap.toContinuousLinearMap {
      toFun := fun B => A * Z0 * Bᵀ
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add]
      map_smul' := fun c x => by simp [Matrix.transpose_smul]
    }
    map_add' := fun x y => by
      ext B i j
      dsimp
      simp [Matrix.add_mul]
    map_smul' := fun c x => by
      ext B i j
      dsimp
      simp
  }

noncomputable def local_orbit_map (Z0 : Matrix (Fin 2) (Fin 2) ℂ) (ab : (Fin 3 → ℂ) × (Fin 3 → ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  matrix_lorentz_bilin Z0 (sl2c_chart_at_id ab.1) (sl2c_chart_at_id ab.2)

lemma AnalyticAt.comp_of_eq {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : F → G} {f : E → F} {y : F} {x : E}
    (hg : AnalyticAt 𝕜 g y) (hf : AnalyticAt 𝕜 f x) (h : f x = y) :
    AnalyticAt 𝕜 (g ∘ f) x := by
  subst h
  exact hg.comp hf

lemma AnalyticAt.congr_fun_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {x : E}
    (hf : AnalyticAt 𝕜 f x) (h : ∀ y, f y = g y) : AnalyticAt 𝕜 g x := by
  have H : f = g := funext h
  subst H
  exact hf

lemma HasFDerivAt.comp_of_eq {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : F → G} {g' : F →L[𝕜] G} {f : E → F} {f' : E →L[𝕜] F} {x : E} {y : F}
    (hg : HasFDerivAt g g' y) (hf : HasFDerivAt f f' x) (h : f x = y) :
    HasFDerivAt (g ∘ f) (g'.comp f') x := by
  subst h
  exact hg.comp x hf

lemma local_orbit_map_analytic (Z0 : Matrix (Fin 2) (Fin 2) ℂ) :
    AnalyticAt ℂ (local_orbit_map Z0) (0, 0) := by
  have h1 : AnalyticAt ℂ (fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.1) (0, 0) := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.2) (0, 0) := analyticAt_snd

  have h3_1 : AnalyticAt ℂ sl2c_chart_at_id 0 := sl2c_chart_at_id_analytic 0 (by norm_num)
  have h3_2 : AnalyticAt ℂ sl2c_chart_at_id 0 := sl2c_chart_at_id_analytic 0 (by norm_num)

  have hA_comp := AnalyticAt.comp_of_eq h3_1 h1 rfl
  have hB_comp := AnalyticAt.comp_of_eq h3_2 h2 rfl

  have hProd := hA_comp.prod hB_comp

  have H : AnalyticAt ℂ (fun p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ => matrix_lorentz_bilin Z0 p.1 p.2) (sl2c_chart_at_id 0, sl2c_chart_at_id 0) :=
    ContinuousLinearMap.analyticAt_bilinear (matrix_lorentz_bilin Z0) (sl2c_chart_at_id 0, sl2c_chart_at_id 0)

  have h_final := AnalyticAt.comp_of_eq H hProd rfl
  apply AnalyticAt.congr_fun_eq h_final
  intro ab
  rfl

noncomputable def local_orbit_fderiv_at_zero (Z0 : Matrix (Fin 2) (Fin 2) ℂ) :
    ((Fin 3 → ℂ) × (Fin 3 → ℂ)) →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun uv => pauli_map_lin uv.1 * Z0 + Z0 * (pauli_map_lin uv.2)ᵀ
    map_add' := fun x y => by
      dsimp
      have h1 : pauli_map_lin (x.1 + y.1) = pauli_map_lin x.1 + pauli_map_lin y.1 := map_add pauli_map_lin x.1 y.1
      have h2 : pauli_map_lin (x.2 + y.2) = pauli_map_lin x.2 + pauli_map_lin y.2 := map_add pauli_map_lin x.2 y.2
      rw [h1, h2]
      rw [Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add]
      
      exact add_add_add_comm (pauli_map_lin x.1 * Z0) (pauli_map_lin y.1 * Z0) (Z0 * (pauli_map_lin x.2)ᵀ) (Z0 * (pauli_map_lin y.2)ᵀ)
    map_smul' := fun c x => by
      dsimp
      have h1 : pauli_map_lin (c • x.1) = c • pauli_map_lin x.1 := map_smul pauli_map_lin c x.1
      have h2 : pauli_map_lin (c • x.2) = c • pauli_map_lin x.2 := map_smul pauli_map_lin c x.2
      rw [h1, h2]
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  }

lemma hasFDerivAt_local_orbit_map_zero (Z0 : Matrix (Fin 2) (Fin 2) ℂ) :
    HasFDerivAt (local_orbit_map Z0) (local_orbit_fderiv_at_zero Z0) (0, 0) := by
  have h1 : HasFDerivAt (fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.1) (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ)) (0, 0) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.2) (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ)) (0, 0) := hasFDerivAt_snd

  have h3_1 : HasFDerivAt sl2c_chart_at_id pauli_map_lin 0 := hasFDerivAt_sl2c_chart_at_id_zero
  have h3_2 : HasFDerivAt sl2c_chart_at_id pauli_map_lin 0 := hasFDerivAt_sl2c_chart_at_id_zero

  have hA_comp := HasFDerivAt.comp_of_eq h3_1 h1 rfl
  have hB_comp := HasFDerivAt.comp_of_eq h3_2 h2 rfl

  have h_final := (matrix_lorentz_bilin Z0).hasFDerivAt_of_bilinear hA_comp hB_comp

  change HasFDerivAt (local_orbit_map Z0) _ (0,0) at h_final
  exact h_final.congr_fderiv (by
    apply ContinuousLinearMap.ext
    rintro ⟨ab1, ab2⟩
    have h_chart_0 : sl2c_chart_at_id 0 = 1 := by
      ext u v
      dsimp [sl2c_chart_at_id]
      fin_cases u <;> fin_cases v <;> norm_num
    have h01 : (sl2c_chart_at_id ∘ fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.1) (0, 0) = 1 := h_chart_0
    have h02 : (sl2c_chart_at_id ∘ fun ab : (Fin 3 → ℂ) × (Fin 3 → ℂ) => ab.2) (0, 0) = 1 := h_chart_0
    rw [h01, h02]
    change 1 * Z0 * (pauli_map_lin ab2)ᵀ + pauli_map_lin ab1 * Z0 * 1ᵀ = pauli_map_lin ab1 * Z0 + Z0 * (pauli_map_lin ab2)ᵀ
    simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
    exact add_comm _ _
  )

def mass_shell_trace_map (Z0 : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun := fun W => Matrix.trace (Z0.adjugate * W)
  map_add' := fun x y => by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' := fun c x => by simp [Matrix.trace_smul]


def mass_shell_tangent_space (Z0 : Matrix (Fin 2) (Fin 2) ℂ) : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  LinearMap.ker (mass_shell_trace_map Z0)

lemma pauli_map_lin_trace_zero (x : Fin 3 → ℂ) : (pauli_map_lin x).trace = 0 := by
  dsimp [pauli_map_lin]
  rw [Matrix.trace_fin_two]
  simp [sigma_1, sigma_2, sigma_3]


lemma local_orbit_fderiv_maps_to_tangent (Z0 : Matrix (Fin 2) (Fin 2) ℂ) (uv : (Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    local_orbit_fderiv_at_zero Z0 uv ∈ mass_shell_tangent_space Z0 := by
  change Matrix.trace (Z0.adjugate * (pauli_map_lin uv.1 * Z0 + Z0 * (pauli_map_lin uv.2)ᵀ)) = 0
  rw [Matrix.mul_add, Matrix.trace_add]

  have h1 : Matrix.trace (Z0.adjugate * (pauli_map_lin uv.1 * Z0)) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rw [Matrix.one_mul, pauli_map_lin_trace_zero]
    simp

  have h2 : Matrix.trace (Z0.adjugate * (Z0 * (pauli_map_lin uv.2)ᵀ)) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rw [Matrix.one_mul, Matrix.trace_transpose, pauli_map_lin_trace_zero]
    simp
  rw [h1, h2, add_zero]

lemma pauli_map_lin_surjective (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U.trace = 0) : ∃ u, pauli_map_lin u = U := by
  use fun i => if i = 0 then (U 0 1 + U 1 0) / 2 else if i = 1 then (U 0 1 - U 1 0) * I / 2 else U 0 0
  ext i j
  fin_cases i
  · fin_cases j
    · dsimp [pauli_map_lin, sigma_1, sigma_2, sigma_3]
      simp
    · dsimp [pauli_map_lin, sigma_1, sigma_2, sigma_3]
      simp
      ring_nf
      simp [I_sq]
      ring
  · fin_cases j
    · dsimp [pauli_map_lin, sigma_1, sigma_2, sigma_3]
      simp
      ring_nf
      simp [I_sq]
      ring
    · dsimp [pauli_map_lin, sigma_1, sigma_2, sigma_3]
      simp
      have h : U 0 0 + U 1 1 = 0 := by
        have h_trace : U.trace = 0 := hU
        rw [Matrix.trace_fin_two] at h_trace
        exact h_trace
      calc
        -U 0 0 = -U 0 0 + 0 := by ring
        _      = -U 0 0 + (U 0 0 + U 1 1) := by rw [h]
        _      = (-U 0 0 + U 0 0) + U 1 1 := by ring
        _      = U 1 1 := by ring


lemma local_orbit_fderiv_surjective (Z0 : Matrix (Fin 2) (Fin 2) ℂ) (hZ0 : Z0.det ≠ 0) :
    ∀ W ∈ mass_shell_tangent_space Z0, ∃ uv, local_orbit_fderiv_at_zero Z0 uv = W := by
  intro W hW
  change Matrix.trace (Z0.adjugate * W) = 0 at hW
  let U := W * (Z0.det⁻¹ • Z0.adjugate)
  have hU_trace : U.trace = 0 := by
    dsimp [U]
    rw [Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.trace_smul]
    rw [hW, smul_zero]
  rcases pauli_map_lin_surjective U hU_trace with ⟨u, hu⟩
  use (u, 0)
  dsimp [local_orbit_fderiv_at_zero]
  have h0 : pauli_map_lin 0 = 0 := map_zero pauli_map_lin
  rw [h0]
  rw [Matrix.transpose_zero, Matrix.mul_zero, add_zero]
  rw [hu]
  dsimp [U]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul]
  rw [Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hZ0, one_smul]








lemma complex_multilinear_zero_of_real_zero (n : ℕ) (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ)
    (h : ∀ x : Fin n → ℝ, p (fun i => ofRealCLM (x i)) = 0) : p = 0 := by
  have hz : p (fun _ => 1) = 0 := by
    have h' := h (fun _ => 1)
    simp only [ofRealCLM_apply, ofReal_one] at h'
    exact h'
  have heq : p = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (p (fun _ => 1)) := p.mkPiRing_apply_one_eq_self.symm
  rw [hz] at heq
  have hzero : ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (0 : ℂ) = 0 := by
    ext
    simp
  rw [hzero] at heq
  exact heq


lemma analytic_eq_of_real_eq_on_interval {U : Set ℂ}
    (hU_open : IsOpen U) (hU_conn : IsConnected U)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (a : ℝ) (ha : (a : ℂ) ∈ U)
    (h_real : ∀ᶠ t : ℝ in 𝓝 a, f ↑t = g ↑t) :
    Set.EqOn f g U := by
  have h_sub : ∀ᶠ t : ℝ in 𝓝 a, (f - g) ↑t = 0 := by
    filter_upwards [h_real] with t ht
    simp [ht]

  have hfg : AnalyticOnNhd ℂ (f - g) U := hf.sub hg
  have h_an_at : AnalyticAt ℂ (f - g) (a : ℂ) := hfg (a : ℂ) ha
  rcases h_an_at with ⟨p, r, hp⟩

  have ha_eq : (a : ℂ) = ofRealCLM a := by rfl
  have hp_res : HasFPowerSeriesOnBall (f - g) (p.restrictScalars ℝ) (a : ℂ) r := hp.restrictScalars
  rw [ha_eq] at hp_res

  have hp_real := hp_res.compContinuousLinearMap (u := ofRealCLM)
  have hp_real_zero : (p.restrictScalars ℝ).compContinuousLinearMap ofRealCLM = 0 := by
    apply hp_real.hasFPowerSeriesAt.locally_zero_iff.mp
    exact h_sub

  have hp_zero : p = 0 := by
    apply FormalMultilinearSeries.ext_iff.mpr
    intro n
    have h_n_zero : ((p.restrictScalars ℝ).compContinuousLinearMap ofRealCLM) n = 0 := by
      rw [hp_real_zero]
      rfl
    have h_eval : ∀ x : Fin n → ℝ, p n (fun i => ofRealCLM (x i)) = 0 := by
      intro x
      have heval2 := ContinuousMultilinearMap.ext_iff.mp h_n_zero x
      exact heval2
    exact complex_multilinear_zero_of_real_zero n (p n) h_eval

  have h_f_eq_g_near : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), (f - g) z = 0 := by
    apply hp.hasFPowerSeriesAt.locally_zero_iff.mpr hp_zero

  have h_eq_zero : Set.EqOn (f - g) 0 U :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hfg hU_conn.isPreconnected ha h_f_eq_g_near

  intro z hz
  have hz0 := h_eq_zero hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hz0
  exact hz0





lemma scv_identity_theorem (n : ℕ) (U : Set (Fin n → Fin 4 → ℂ)) (hU_open : IsOpen U) (hU_conn : IsConnected U)
  (f g : (Fin n → Fin 4 → ℂ) → ℂ) (hf : AnalyticOn ℂ f U) (hg : AnalyticOn ℂ g U)
  (V : Set (Fin n → Fin 4 → ℂ)) (hV_open : IsOpen V) (hV_nonempty : V.Nonempty) (hV_sub : V ⊆ U)
  (h_eq : ∀ z ∈ V, f z = g z) :
  ∀ z ∈ U, f z = g z := by
  
  have hf_nhd : AnalyticOnNhd ℂ f U := hU_open.analyticOn_iff_analyticOnNhd.mp hf
  have hg_nhd : AnalyticOnNhd ℂ g U := hU_open.analyticOn_iff_analyticOnNhd.mp hg
  rcases hV_nonempty with ⟨v₀, hv₀⟩
  have h_nhd_V : V ∈ 𝓝 v₀ := hV_open.mem_nhds hv₀
  have h_eventual : f =ᶠ[𝓝 v₀] g := by
    filter_upwards [h_nhd_V] with z hz using h_eq z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf_nhd hg_nhd hU_conn.isPreconnected (hV_sub hv₀) h_eventual






lemma forward_tube_n_nonempty (n : ℕ) : (forward_tube_n n).Nonempty := by
  let v : Fin 4 → ℝ := fun k => if k = 0 then 1 else 0
  have hv : v ∈ forward_light_cone := by
    dsimp [v, forward_light_cone]
    constructor
    · norm_num
    · rw [minkowskiInner_explicit]
      simp
  let z : Fin n → Fin 4 → ℂ := fun i k => (i : ℝ) * (v k : ℂ) * I
  use z
  intro i hi
  have h_eq : (fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) = v := by
    funext k
    have h_eval : (z i - z ⟨i.val + 1, hi⟩) k = z i k - z ⟨i.val + 1, hi⟩ k := rfl
    rw [h_eval]
    have h2 : z i k - z ⟨i.val + 1, hi⟩ k = - (v k : ℂ) * I := by
      dsimp [z]
      push_cast
      ring
    rw [h2]
    simp
  rw [h_eq]
  exact hv



lemma forward_tube_n_convex (n : ℕ) : Convex ℝ (forward_tube_n n) := by
  intro z hz w hw a b ha hb hab i hi
  have hz_cone := hz i hi
  have hw_cone := hw i hi
  have h_cone := forward_light_cone_convex hz_cone hw_cone ha hb hab
  have h_eq : (fun k => -(((a • z + b • w) i - (a • z + b • w) ⟨i.val + 1, hi⟩) k).im) =
    a • (fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) + b • (fun k => -((w i - w ⟨i.val + 1, hi⟩) k).im) := by
    funext k
    dsimp
    have h1 : (((a : ℂ) * z i k + (b : ℂ) * w i k) - ((a : ℂ) * z ⟨i.val + 1, hi⟩ k + (b : ℂ) * w ⟨i.val + 1, hi⟩ k)) =
      (a : ℂ) * (z i k - z ⟨i.val + 1, hi⟩ k) + (b : ℂ) * (w i k - w ⟨i.val + 1, hi⟩ k) := by ring
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h_eq]
  exact h_cone

lemma forward_tube_is_connected (n : ℕ) : IsConnected (forward_tube_n n) :=
  (forward_tube_n_convex n).isConnected (forward_tube_n_nonempty n)


lemma lorentz_action_continuous (n : ℕ) : Continuous (fun (p : SpecialSpecialComplexLorentzGroup × (Fin n → Fin 4 → ℂ)) => p.1 • p.2) := by


  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h_eq : (fun (p : SpecialSpecialComplexLorentzGroup × (Fin n → Fin 4 → ℂ)) => (p.1 • p.2) i j) =
    (fun p => ∑ k : Fin 4, (p.1.val.val j k) * p.2 i k) := by
    ext p
    rfl
  rw [h_eq]
  apply continuous_finsetSum
  intro k _
  apply Continuous.mul
  · have h_val : Continuous (fun (M : Matrix.GeneralLinearGroup (Fin 4) ℂ) => (M.val : Matrix (Fin 4) (Fin 4) ℂ)) := Units.continuous_val
    have h_elem : Continuous (fun (M : Matrix.GeneralLinearGroup (Fin 4) ℂ) => M.val j k) := (continuous_apply k).comp ((continuous_apply j).comp h_val)
    exact h_elem.comp (continuous_subtype_val.comp continuous_fst)
  · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_snd)




lemma complex_lorentz_connected : IsConnected (Set.univ : Set SpecialSpecialComplexLorentzGroup) := by
  have h_conn_sl2c : IsConnected (Set.univ : Set (Matrix.SpecialLinearGroup (Fin 2) ℂ)) := Geometry.SpinorTopology.sl2c_isConnected
  have h_conn_prod : IsConnected (Set.univ : Set (Matrix.SpecialLinearGroup (Fin 2) ℂ × Matrix.SpecialLinearGroup (Fin 2) ℂ)) := by
    rw [← Set.univ_prod_univ]
    exact h_conn_sl2c.prod h_conn_sl2c
  have h_cont : Continuous Geometry.spinorPhi := Geometry.continuous_spinorPhi
  have h_surj : Function.Surjective Geometry.spinorPhi := Geometry.spinorPhi_surjective
  have h_image : Geometry.spinorPhi '' Set.univ = Set.univ := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_univ, iff_true]
    exact h_surj x
  rw [← h_image]
  exact h_conn_prod.image _ h_cont.continuousOn


lemma extended_tube_is_connected (n : ℕ) : IsConnected (extended_tube_n n) := by
  have h1 : IsConnected (Set.univ : Set SpecialSpecialComplexLorentzGroup) := complex_lorentz_connected
  have h2 : IsConnected (forward_tube_n n) := forward_tube_is_connected n
  have h3 : Continuous (fun (p : SpecialSpecialComplexLorentzGroup × (Fin n → Fin 4 → ℂ)) => p.1 • p.2) := lorentz_action_continuous n
  have h4 := (h1.prod h2).image _ h3.continuousOn
  have h_eq : (fun (p : SpecialSpecialComplexLorentzGroup × (Fin n → Fin 4 → ℂ)) => p.1 • p.2) '' (Set.univ ×ˢ forward_tube_n n) = extended_tube_n n := by
    ext w
    simp only [extended_tube_n, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨Λ, z⟩, hz, rfl⟩
      exact ⟨Λ, z, hz, rfl⟩
    · rintro ⟨Λ, z, hz, rfl⟩
      exact ⟨(Λ, z), hz, rfl⟩
  rw [←h_eq]
  exact h4

lemma forward_tube_n_isOpen (n : ℕ) : IsOpen (forward_tube_n n) := by
  dsimp [forward_tube_n]
  simp_rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro hi
  apply IsOpen.preimage
  · apply continuous_pi
    intro k
    apply Continuous.neg
    apply Continuous.sub
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (continuous_apply i))
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (continuous_apply (⟨i.val + 1, hi⟩ : Fin n)))
  · exact forward_light_cone_isOpen

lemma extended_tube_is_open (n : ℕ) : IsOpen (extended_tube_n n) := by
  dsimp [extended_tube_n]
  apply isOpen_iUnion
  intro Λ
  have h_eq : (fun z => Λ • z) '' forward_tube_n n = (fun z => Λ⁻¹ • z) ⁻¹' forward_tube_n n := by
    ext w
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (congrArg (· ∈ forward_tube_n n) (inv_smul_smul Λ z)).mpr hz
    · intro hw
      use Λ⁻¹ • w
      refine ⟨hw, ?_⟩
      exact smul_inv_smul Λ w
  rw [h_eq]
  apply IsOpen.preimage
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have h_eq_sum : (fun (z : Fin n → Fin 4 → ℂ) => (Λ⁻¹ • z) i j) = fun z => ∑ k, (Λ⁻¹.val) j k * z i k := by
      ext z
      dsimp [lorentz_action_n, MulAction.compHom, Matrix.mulVec, dotProduct]
      rfl
    rw [h_eq_sum]
    apply continuous_finsetSum
    intro k _
    apply Continuous.mul continuous_const
    exact (continuous_apply k).comp (continuous_apply i)
  · exact forward_tube_n_isOpen n





noncomputable def W_ext_val (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  haveI := Classical.propDecidable (z ∈ forward_tube_n n)
  haveI := Classical.propDecidable (z ∈ extended_tube_n n)
  if hz : z ∈ forward_tube_n n then
    W z
  else if hz : z ∈ extended_tube_n n then
    let h_exists_Lambda := Set.mem_iUnion.mp hz
    let Λ := Classical.choose h_exists_Lambda
    let h_exists_z' := Classical.choose_spec h_exists_Lambda
    let z_in_tube := Classical.choose h_exists_z'
    W z_in_tube
  else
    0



lemma is_connected_orbit_domain (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
  IsConnected (orbit_domain n z) := by
  
  exact IsPathConnected.isConnected (Geometry.PolarDecomposition.orbit_domain_path_connected n z hz)

lemma orbit_domain_isOpen (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
  IsOpen (orbit_domain n z) := by
  have h_cont : Continuous (fun Λ : SpecialSpecialComplexLorentzGroup => Λ • z) :=
    (lorentz_action_continuous n).comp (continuous_id.prodMk continuous_const)
  exact (forward_tube_n_isOpen n).preimage h_cont

noncomputable def local_chart (x : Fin 6 → ℂ) : SpecialSpecialComplexLorentzGroup :=
  let a : Fin 3 → ℂ := fun i => x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩
  let b : Fin 3 → ℂ := fun i => if i.val = 1 then -x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩ else x ⟨i.val, by omega⟩ - I * x ⟨i.val + 3, by omega⟩
  let A := sl2c_chart_invFun a
  let B := sl2c_chart_invFun b
  spinorPhi (A, B)

lemma sl2c_chart_invFun_analytic : AnalyticAt ℂ (fun a => (sl2c_chart_invFun a).1) 0 := by
  have h_ne : (0 : Fin 3 → ℂ) 2 ≠ 1 := by norm_num
  have h_open : IsOpen { a : Fin 3 → ℂ | a 2 ≠ 1 } := by
    exact IsOpen.preimage (continuous_apply 2) isOpen_ne
  have h_eq : ∀ᶠ a in 𝓝 0, sl2c_chart_at_id a = (sl2c_chart_invFun a).1 := by
    apply Filter.eventually_of_mem (h_open.mem_nhds h_ne)
    intro a ha
    exact (sl2c_chart_invFun_eq ha).symm
  exact (sl2c_chart_at_id_analytic 0 h_ne).congr h_eq

attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

lemma analyticAt_matrix_elem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E} (hf : AnalyticAt ℂ f x) (i j : Fin 2) :
  AnalyticAt ℂ (fun e => f e i j) x :=
  analyticAt_matrix_proj i j _ |>.comp hf

lemma analyticAt_matrix_proj4 (i j : Fin 4) (M₀ : Matrix (Fin 4) (Fin 4) ℂ) :
  AnalyticAt ℂ (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) M₀ := by
  let P_i : Matrix (Fin 4) (Fin 4) ℂ →L[ℂ] (Fin 4 → ℂ) := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 4) i
  let P_j : (Fin 4 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (ι := Fin 4) j
  let L := P_j.comp P_i
  have h_eq : (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) = ⇑L := rfl
  rw [h_eq]
  exact L.analyticAt M₀

lemma analyticAt_matrix_elem4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → Matrix (Fin 4) (Fin 4) ℂ} {x : E} (hf : AnalyticAt ℂ f x) (i j : Fin 4) :
  AnalyticAt ℂ (fun e => f e i j) x :=
  analyticAt_matrix_proj4 i j _ |>.comp hf

lemma analyticAt_matrix_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
  AnalyticAt ℂ (fun e => (f e)ᵀ) x := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  exact analyticAt_matrix_elem hf j i

lemma spinor_action_matrix_analytic (A B : (Fin 6 → ℂ) → SpecialLinearGroup (Fin 2) ℂ)
  (hA : AnalyticAt ℂ (fun x => (A x).1) 0) (hB : AnalyticAt ℂ (fun x => (B x).1) 0) (v : Fin 4 → ℂ) :
  AnalyticAt ℂ (fun x => ((A x).1 * vec_to_spinor v) * ((B x).1)ᵀ) 0 := by
  have hB_trans : AnalyticAt ℂ (fun x => ((B x).1)ᵀ) 0 := analyticAt_matrix_transpose hB
  have h_const : AnalyticAt ℂ (fun (_ : Fin 6 → ℂ) => vec_to_spinor v) 0 := analyticAt_const
  have hA_mul : AnalyticAt ℂ (fun x => (A x).1 * vec_to_spinor v) 0 := analyticAt_matrix_mul hA h_const
  exact analyticAt_matrix_mul hA_mul hB_trans

lemma spinorPhi_matrix_analytic (A B : (Fin 6 → ℂ) → SpecialLinearGroup (Fin 2) ℂ)
  (hA : AnalyticAt ℂ (fun x => (A x).1) 0) (hB : AnalyticAt ℂ (fun x => (B x).1) 0) :
  AnalyticAt ℂ (fun x => spinorPhi_matrix (A x) (B x)) 0 := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  have hM := spinor_action_matrix_analytic A B hA hB (Pi.single j 1)
  have hM00 : AnalyticAt ℂ (fun x => (((A x).1 * vec_to_spinor (Pi.single j 1)) * ((B x).1)ᵀ) 0 0) 0 := analyticAt_matrix_elem hM 0 0
  have hM01 : AnalyticAt ℂ (fun x => (((A x).1 * vec_to_spinor (Pi.single j 1)) * ((B x).1)ᵀ) 0 1) 0 := analyticAt_matrix_elem hM 0 1
  have hM10 : AnalyticAt ℂ (fun x => (((A x).1 * vec_to_spinor (Pi.single j 1)) * ((B x).1)ᵀ) 1 0) 0 := analyticAt_matrix_elem hM 1 0
  have hM11 : AnalyticAt ℂ (fun x => (((A x).1 * vec_to_spinor (Pi.single j 1)) * ((B x).1)ᵀ) 1 1) 0 := analyticAt_matrix_elem hM 1 1
  have H : (fun x => spinorPhi_matrix (A x) (B x) i j) = fun x => spinor_to_vec (((A x).1 * vec_to_spinor (Pi.single j 1)) * ((B x).1)ᵀ) i := by
    ext x
    dsimp [spinorPhi_matrix, spinor_action_linear, spinor_action]
  rw [H]
  fin_cases i
  · apply AnalyticAt.div (AnalyticAt.add hM00 hM11) analyticAt_const (by norm_num)
  · apply AnalyticAt.div (AnalyticAt.add hM01 hM10) analyticAt_const (by norm_num)
  · apply AnalyticAt.div (AnalyticAt.mul (AnalyticAt.sub hM01 hM10) analyticAt_const) analyticAt_const (by norm_num)
  · apply AnalyticAt.div (AnalyticAt.sub hM00 hM11) analyticAt_const (by norm_num)

lemma star_sl2c_chart_at_id (a : Fin 3 → ℂ) :
  star (sl2c_chart_at_id a) = sl2c_chart_at_id (fun i => star (a i)) := by
  dsimp [sl2c_chart_at_id]
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [sl2c_chart_at_id]
    simp only [sq]
    apply Complex.ext <;> simp
  · dsimp [sl2c_chart_at_id]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    · ring
    · ring
  · dsimp [sl2c_chart_at_id]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  · dsimp [sl2c_chart_at_id]
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]

lemma local_chart_B_eq_map_conj (x : Fin 6 → ℝ) :
  let a : Fin 3 → ℂ := fun i => x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩
  let b : Fin 3 → ℂ := fun i => if i.val = 1 then -x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩ else x ⟨i.val, by omega⟩ - I * x ⟨i.val + 3, by omega⟩
  let A := sl2c_chart_invFun a
  let B := sl2c_chart_invFun b
  (B.1 : Matrix (Fin 2) (Fin 2) ℂ) = (A.1 : Matrix (Fin 2) (Fin 2) ℂ).map star := by
  intro a b A B
  have ha2_iff : (x ⟨2, by omega⟩ + I * x ⟨5, by omega⟩ : ℂ) = 1 ↔
    (x ⟨2, by omega⟩ - I * x ⟨5, by omega⟩ : ℂ) = 1 := by
    constructor <;> intro h
    · have h_re : (x ⟨2, by omega⟩ + I * x ⟨5, by omega⟩ : ℂ).re = 1 := by rw [h]; rfl
      have h_im : (x ⟨2, by omega⟩ + I * x ⟨5, by omega⟩ : ℂ).im = 0 := by rw [h]; rfl
      have h_re' : x 2 = 1 := by exact (add_re _ _).symm ▸ h_re |> (fun H => by simpa using H)
      have h_im' : x 5 = 0 := by exact (add_im _ _).symm ▸ h_im |> (fun H => by simpa using H)
      apply Complex.ext <;> simp [h_re', h_im']
    · have h_re : (x ⟨2, by omega⟩ - I * x ⟨5, by omega⟩ : ℂ).re = 1 := by rw [h]; rfl
      have h_im : (x ⟨2, by omega⟩ - I * x ⟨5, by omega⟩ : ℂ).im = 0 := by rw [h]; rfl
      have h_re' : x 2 = 1 := by exact (sub_re _ _).symm ▸ h_re |> (fun H => by simpa using H)
      have h_im' : x 5 = 0 := by exact (sub_im _ _).symm ▸ h_im |> (fun H => by simpa using H)
      apply Complex.ext <;> simp [h_re', h_im']
  dsimp [A, B, sl2c_chart_invFun]
  have h_b_2 : b 2 = (x ⟨2, by omega⟩ - I * x ⟨5, by omega⟩ : ℂ) := rfl
  have h_a_2 : a 2 = (x ⟨2, by omega⟩ + I * x ⟨5, by omega⟩ : ℂ) := rfl
  by_cases h_b : b 2 = 1
  · rw [dif_pos h_b]
    have h_a : a 2 = 1 := by
      rw [h_a_2, ha2_iff, ← h_b_2]
      exact h_b
    rw [dif_pos h_a]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  · rw [dif_neg h_b]
    have h_a : a 2 ≠ 1 := by
      rw [h_a_2]
      intro h
      apply h_b
      rw [h_b_2]
      exact ha2_iff.mp h
    rw [dif_neg h_a]
    change sl2c_chart_at_id b = (sl2c_chart_at_id a).map star
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp [sl2c_chart_at_id, a, b]
      apply Complex.ext <;> simp <;> ring
    · dsimp [sl2c_chart_at_id, a, b]
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
    · dsimp [sl2c_chart_at_id, a, b]
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
    · dsimp [sl2c_chart_at_id, a, b]
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring


lemma spinorPhi_real_of_B_eq_map_conj (A B : SpecialLinearGroup (Fin 2) ℂ)
  (h_eq : (B.1 : Matrix (Fin 2) (Fin 2) ℂ) = (A.1 : Matrix (Fin 2) (Fin 2) ℂ).map star) :
  ∃ Λ : Geometry.ProperOrthochronousLorentzGroup, spinorPhi (A, B) = real_to_complex_lorentz Λ := by
  have him : ∀ i j, (Geometry.spinorPhi_matrix A B i j).im = 0 := by
    intro i j
    exact Geometry.spinorPhi_matrix_im_zero A B h_eq i j

  have h_eq_inv : ((B⁻¹ : SpecialLinearGroup (Fin 2) ℂ).1 : Matrix (Fin 2) (Fin 2) ℂ) = ((A⁻¹ : SpecialLinearGroup (Fin 2) ℂ).1 : Matrix (Fin 2) (Fin 2) ℂ).map star := by
    change B.1.adjugate = (A.1.adjugate).map star
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.adjugate_fin_two, h_eq, Matrix.map_apply]
    · simp [Matrix.adjugate_fin_two, h_eq, Matrix.map_apply]
    · simp [Matrix.adjugate_fin_two, h_eq, Matrix.map_apply]
    · simp [Matrix.adjugate_fin_two, h_eq, Matrix.map_apply]
  have him_inv : ∀ i j, (Geometry.spinorPhi_matrix A⁻¹ B⁻¹ i j).im = 0 := by
    intro i j
    exact Geometry.spinorPhi_matrix_im_zero A⁻¹ B⁻¹ h_eq_inv i j

  let Λ_R_val : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (Geometry.spinorPhi_matrix A B i j).re
  let Λ_R_inv : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (Geometry.spinorPhi_matrix A⁻¹ B⁻¹ i j).re

  have H_val_eq : (Geometry.spinorPhi_matrix A B) = Λ_R_val.map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    dsimp [Λ_R_val, Matrix.map]
    have h1 := him i j
    exact Complex.ext (by simp) (by simp [h1])

  have H_inv_eq : (Geometry.spinorPhi_matrix A⁻¹ B⁻¹) = Λ_R_inv.map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    dsimp [Λ_R_inv, Matrix.map]
    have h1 := him_inv i j
    exact Complex.ext (by simp) (by simp [h1])

  have H_mul_1 : Λ_R_val * Λ_R_inv = 1 := by
    have h_c := Geometry.spinorPhi_matrix_inv A B
    rw [H_val_eq, H_inv_eq] at h_c
    have H_map_mul : Λ_R_val.map (fun x : ℝ => (x : ℂ)) * Λ_R_inv.map (fun x : ℝ => (x : ℂ)) = (Λ_R_val * Λ_R_inv).map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.map_apply]
    rw [H_map_mul] at h_c
    have H_map_one : (1 : Matrix (Fin 4) (Fin 4) ℂ) = (1 : Matrix (Fin 4) (Fin 4) ℝ).map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      by_cases h : i = j
      · simp [h, Matrix.one_apply]
      · simp [h]
    rw [H_map_one] at h_c
    ext i j
    have H_ext := congr_fun (congr_fun h_c i) j
    simp [Matrix.map_apply] at H_ext
    exact H_ext

  have H_mul_2 : Λ_R_inv * Λ_R_val = 1 := by
    have h_c := Geometry.spinorPhi_matrix_inv' A B
    rw [H_val_eq, H_inv_eq] at h_c
    have H_map_mul : Λ_R_inv.map (fun x : ℝ => (x : ℂ)) * Λ_R_val.map (fun x : ℝ => (x : ℂ)) = (Λ_R_inv * Λ_R_val).map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.map_apply]
    rw [H_map_mul] at h_c
    have H_map_one : (1 : Matrix (Fin 4) (Fin 4) ℂ) = (1 : Matrix (Fin 4) (Fin 4) ℝ).map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      by_cases h : i = j
      · simp [h, Matrix.one_apply]
      · simp [h]
    rw [H_map_one] at h_c
    ext i j
    have H_ext := congr_fun (congr_fun h_c i) j
    simp [Matrix.map_apply] at H_ext
    exact H_ext

  let Λ_GL : Matrix.GeneralLinearGroup (Fin 4) ℝ :=
    { val := Λ_R_val,
      inv := Λ_R_inv,
      val_inv := H_mul_1,
      inv_val := H_mul_2 }

  have h_lorentz : Λ_GL.valᵀ * Geometry.minkowskiMetricReal * Λ_GL.val = Geometry.minkowskiMetricReal := by
    have h_c := Geometry.spinorPhi_is_lorentz A B
    have H_map_metric : Geometry.minkowskiMetric = Geometry.minkowskiMetricReal.map (fun x : ℝ => (x : ℂ)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Geometry.minkowskiMetric, Geometry.minkowskiMetricReal]
    rw [H_map_metric] at h_c
    rw [H_val_eq] at h_c
    have H_map_mul1 : (Λ_R_val.map (fun x : ℝ => (x : ℂ)))ᵀ * Geometry.minkowskiMetricReal.map (fun x : ℝ => (x : ℂ)) = (Λ_R_valᵀ * Geometry.minkowskiMetricReal).map (fun x : ℝ => (x : ℂ)) := by
      ext i j; simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    have H_map_mul2 : (Λ_R_valᵀ * Geometry.minkowskiMetricReal).map (fun x : ℝ => (x : ℂ)) * Λ_R_val.map (fun x : ℝ => (x : ℂ)) = (Λ_R_valᵀ * Geometry.minkowskiMetricReal * Λ_R_val).map (fun x : ℝ => (x : ℂ)) := by
      ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
    rw [H_map_mul1, H_map_mul2] at h_c
    ext i j
    have H_ext := congr_fun (congr_fun h_c i) j
    simp [Matrix.map_apply] at H_ext
    exact H_ext

  have h_det : Λ_GL.val.det = 1 := by
    have h_c_det := Geometry.spinorPhi_matrix_det A B
    rw [H_val_eq] at h_c_det
    have h_det_map : (Λ_R_val.map (fun x : ℝ => (x : ℂ))).det = (Λ_R_val.det : ℂ) := by
      exact (RingHom.map_det Complex.ofRealHom Λ_R_val).symm
    rw [h_det_map] at h_c_det
    exact Complex.ofReal_inj.mp h_c_det

  have h_ortho : Λ_GL.val 0 0 > 0 := by
    have h1 : Geometry.spinorPhi_matrix A B 0 0 =
      (A.1 0 0 * star (A.1 0 0) + A.1 0 1 * star (A.1 0 1) + A.1 1 0 * star (A.1 1 0) + A.1 1 1 * star (A.1 1 1)) / 2 := by
      dsimp [Geometry.spinorPhi_matrix, Geometry.spinor_action_linear, Geometry.spinor_action, Geometry.vec_to_spinor, Geometry.spinor_to_vec, Geometry.sigma_0, Geometry.sigma_1, Geometry.sigma_2, Geometry.sigma_3]
      rw [h_eq]
      simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    have hre : (Geometry.spinorPhi_matrix A B 0 0).re =
      (normSq (A.1 0 0) + normSq (A.1 0 1) + normSq (A.1 1 0) + normSq (A.1 1 1)) / 2 := by
      rw [h1]
      simp [Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have h_det_A : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
      have hd := A.2
      simp only [Matrix.det_fin_two] at hd
      exact hd
    have h_pos : 0 < normSq (A.1 0 0) + normSq (A.1 0 1) + normSq (A.1 1 0) + normSq (A.1 1 1) := by
      by_contra! h
      have hn1 : normSq (A.1 0 0) = 0 := by linarith [normSq_nonneg (A.1 0 0), normSq_nonneg (A.1 0 1), normSq_nonneg (A.1 1 0), normSq_nonneg (A.1 1 1)]
      have hn2 : normSq (A.1 0 1) = 0 := by linarith [normSq_nonneg (A.1 0 0), normSq_nonneg (A.1 0 1), normSq_nonneg (A.1 1 0), normSq_nonneg (A.1 1 1)]
      have hn3 : normSq (A.1 1 0) = 0 := by linarith [normSq_nonneg (A.1 0 0), normSq_nonneg (A.1 0 1), normSq_nonneg (A.1 1 0), normSq_nonneg (A.1 1 1)]
      have hn4 : normSq (A.1 1 1) = 0 := by linarith [normSq_nonneg (A.1 0 0), normSq_nonneg (A.1 0 1), normSq_nonneg (A.1 1 0), normSq_nonneg (A.1 1 1)]
      have hz1 : A.1 0 0 = 0 := normSq_eq_zero.mp hn1
      have hz2 : A.1 0 1 = 0 := normSq_eq_zero.mp hn2
      have hz3 : A.1 1 0 = 0 := normSq_eq_zero.mp hn3
      have hz4 : A.1 1 1 = 0 := normSq_eq_zero.mp hn4
      rw [hz1, hz2, hz3, hz4] at h_det_A
      norm_num at h_det_A
    change Λ_R_val 0 0 > 0
    dsimp [Λ_R_val]
    rw [hre]
    linarith

  use ⟨Λ_GL, h_lorentz, h_det, h_ortho⟩
  ext i j
  dsimp [real_to_complex_lorentz, spinorPhi]
  rw [H_val_eq]
  rfl

lemma local_chart_real (x : Fin 6 → ℝ) :
  ∃ Λ : ProperOrthochronousLorentzGroup, local_chart (fun i => (x i : ℂ)) = real_to_complex_lorentz Λ := by
  have h_eq := local_chart_B_eq_map_conj x
  exact spinorPhi_real_of_B_eq_map_conj _ _ h_eq

lemma sl2c_chart_at_id_zero : sl2c_chart_at_id (fun _ => 0) = 1 := by
  dsimp [sl2c_chart_at_id]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma sl2c_chart_invFun_zero : sl2c_chart_invFun (fun _ => 0) = 1 := by
  have h_ne : (fun _ : Fin 3 => (0 : ℂ)) 2 ≠ 1 := by norm_num
  have h_eq := sl2c_chart_invFun_eq (a := fun _ => 0) h_ne
  ext i j
  rw [h_eq, sl2c_chart_at_id_zero]
  rfl

lemma local_chart_zero :
  local_chart 0 = 1 := by
  dsimp [local_chart]
  have h_a : (fun _ : Fin 3 => (0 : ℂ) + I * 0) = (fun _ => 0) := by ext i; simp
  have h_b : (fun i : Fin 3 => if i.val = 1 then -(0 : ℂ) + I * 0 else 0 - I * 0) = (fun _ => 0) := by
    ext i
    split
    · simp
    · simp
  rw [h_a, h_b]
  rw [sl2c_chart_invFun_zero]
  exact map_one spinorPhi

noncomputable def local_chart_e : (Fin 6 → ℂ) ≃ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)) := {
    toFun := fun x => (
      (fun i => x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩),
      (fun i => if i.val = 1 then -x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩ else x ⟨i.val, by omega⟩ - I * x ⟨i.val + 3, by omega⟩)
    )
    map_add' := by
      intro x y
      ext i
      · simp
        ring
      · dsimp
        split
        · ring
        · ring
    map_smul' := by
      intro c x
      ext i
      · simp [mul_add]
        ring
      · dsimp
        split
        · ring
        · ring
    invFun := fun p => fun i =>
      if h : i.val < 3 then
        if i.val = 1 then (p.1 ⟨i.val, by omega⟩ - p.2 ⟨i.val, by omega⟩) / 2
        else (p.1 ⟨i.val, by omega⟩ + p.2 ⟨i.val, by omega⟩) / 2
      else
        if i.val - 3 = 1 then (p.1 ⟨i.val - 3, by omega⟩ + p.2 ⟨i.val - 3, by omega⟩) / (2 * I)
        else (p.1 ⟨i.val - 3, by omega⟩ - p.2 ⟨i.val - 3, by omega⟩) / (2 * I)
    left_inv := by
      intro x
      ext i
      dsimp
      split <;> rename_i h
      · split <;> rename_i h1
        · have h_div : ∀ (A B : ℂ), (A + I * B - (-A + I * B)) / 2 = A := by intro A B; ring
          exact h_div _ _
        · have h_div : ∀ (A B : ℂ), (A + I * B + (A - I * B)) / 2 = A := by intro A B; ring
          exact h_div _ _
      · split <;> rename_i h1
        · have h_div : ∀ (A B : ℂ), (A + I * B + (-A + I * B)) / (2 * I) = B := by
            intro A B
            have h1 : A + I * B + (-A + I * B) = B * (2 * I) := by ring
            rw [h1, mul_div_cancel_right₀ _ (by norm_num [Complex.I_ne_zero])]
          rw [h_div]
          have hx : ∀ (h : i.val - 3 + 3 < 6), x ⟨i.val - 3 + 3, h⟩ = x i := fun h => congrArg x (Fin.ext (Nat.sub_add_cancel (by omega)))
          exact hx _
        · have h_div : ∀ (A B : ℂ), (A + I * B - (A - I * B)) / (2 * I) = B := by
            intro A B
            have h1 : A + I * B - (A - I * B) = B * (2 * I) := by ring
            rw [h1, mul_div_cancel_right₀ _ (by norm_num [Complex.I_ne_zero])]
          rw [h_div]
          have hx : ∀ (h : i.val - 3 + 3 < 6), x ⟨i.val - 3 + 3, h⟩ = x i := fun h => congrArg x (Fin.ext (Nat.sub_add_cancel (by omega)))
          exact hx _
    right_inv := by
      intro p
      ext i <;> dsimp
      · have h_pos : (⟨i.val, by omega⟩ : Fin 6).val < 3 := by show i.val < 3; exact i.isLt
        have h_neg : ¬((⟨i.val + 3, by omega⟩ : Fin 6).val < 3) := by show ¬(i.val + 3 < 3); omega
        simp only [dif_pos h_pos]
        have h_p1 : ∀ (h : i.val + 3 - 3 < 3), p.1 ⟨i.val + 3 - 3, h⟩ = p.1 i := fun h => congrArg p.1 (Fin.ext (Nat.add_sub_cancel i.val 3))
        have h_p2 : ∀ (h : i.val + 3 - 3 < 3), p.2 ⟨i.val + 3 - 3, h⟩ = p.2 i := fun h => congrArg p.2 (Fin.ext (Nat.add_sub_cancel i.val 3))
        have h_p1_0 : ∀ (h : i.val < 3), p.1 ⟨i.val, h⟩ = p.1 i := fun h => congrArg p.1 (Fin.ext rfl)
        have h_p2_0 : ∀ (h : i.val < 3), p.2 ⟨i.val, h⟩ = p.2 i := fun h => congrArg p.2 (Fin.ext rfl)
        rw [h_p1, h_p2, h_p1_0, h_p2_0]
        have hi_simp : (i.val + 3 - 3 = 1) ↔ (i.val = 1) := by
          have h_sub : i.val + 3 - 3 = i.val := Nat.add_sub_cancel i.val 3
          rw [h_sub]
        simp only [hi_simp]
        split <;> rename_i h1
        · have h_div : ∀ (A B : ℂ), (A - B) / 2 + I * ((A + B) / (2 * I)) = A := by
            intro A B
            calc (A - B) / 2 + I * ((A + B) / (2 * I)) = (A - B) / 2 + I * (A + B) / (2 * I) := by ring
              _ = (A - B) / 2 + (A + B) * I / (2 * I) := by ring
              _ = (A - B) / 2 + (A + B) / 2 := by rw [mul_div_mul_right (A + B) 2 (by norm_num [Complex.I_ne_zero])]
              _ = A := by ring
          exact h_div (p.1 i) (p.2 i)
        · have h_div : ∀ (A B : ℂ), (A + B) / 2 + I * ((A - B) / (2 * I)) = A := by
            intro A B
            calc (A + B) / 2 + I * ((A - B) / (2 * I)) = (A + B) / 2 + I * (A - B) / (2 * I) := by ring
              _ = (A + B) / 2 + (A - B) * I / (2 * I) := by ring
              _ = (A + B) / 2 + (A - B) / 2 := by rw [mul_div_mul_right (A - B) 2 (by norm_num [Complex.I_ne_zero])]
              _ = A := by ring
          exact h_div (p.1 i) (p.2 i)
      · have h_pos : (⟨i.val, by omega⟩ : Fin 6).val < 3 := by show i.val < 3; exact i.isLt
        have h_neg : ¬((⟨i.val + 3, by omega⟩ : Fin 6).val < 3) := by show ¬(i.val + 3 < 3); omega
        simp only [dif_pos h_pos]
        have h_p1 : ∀ (h : i.val + 3 - 3 < 3), p.1 ⟨i.val + 3 - 3, h⟩ = p.1 i := fun h => congrArg p.1 (Fin.ext (Nat.add_sub_cancel i.val 3))
        have h_p2 : ∀ (h : i.val + 3 - 3 < 3), p.2 ⟨i.val + 3 - 3, h⟩ = p.2 i := fun h => congrArg p.2 (Fin.ext (Nat.add_sub_cancel i.val 3))
        have h_p1_0 : ∀ (h : i.val < 3), p.1 ⟨i.val, h⟩ = p.1 i := fun h => congrArg p.1 (Fin.ext rfl)
        have h_p2_0 : ∀ (h : i.val < 3), p.2 ⟨i.val, h⟩ = p.2 i := fun h => congrArg p.2 (Fin.ext rfl)
        rw [h_p1, h_p2, h_p1_0, h_p2_0]
        have hi_simp : (i.val + 3 - 3 = 1) ↔ (i.val = 1) := by
          have h_sub : i.val + 3 - 3 = i.val := Nat.add_sub_cancel i.val 3
          rw [h_sub]
        simp only [hi_simp]
        split <;> rename_i h1
        · have h_div : ∀ (A B : ℂ), -((A - B) / 2) + I * ((A + B) / (2 * I)) = B := by
            intro A B
            calc -((A - B) / 2) + I * ((A + B) / (2 * I)) = -((A - B) / 2) + I * (A + B) / (2 * I) := by ring
              _ = -((A - B) / 2) + (A + B) * I / (2 * I) := by ring
              _ = -((A - B) / 2) + (A + B) / 2 := by rw [mul_div_mul_right (A + B) 2 (by norm_num [Complex.I_ne_zero])]
              _ = B := by ring
          exact h_div (p.1 i) (p.2 i)
        · have h_div : ∀ (A B : ℂ), (A + B) / 2 - I * ((A - B) / (2 * I)) = B := by
            intro A B
            calc (A + B) / 2 - I * ((A - B) / (2 * I)) = (A + B) / 2 - I * (A - B) / (2 * I) := by ring
              _ = (A + B) / 2 - (A - B) * I / (2 * I) := by ring
              _ = (A + B) / 2 - (A - B) / 2 := by rw [mul_div_mul_right (A - B) 2 (by norm_num [Complex.I_ne_zero])]
              _ = B := by ring
          exact h_div (p.1 i) (p.2 i)
}

lemma local_chart_linear_equiv :
  ∃ e : (Fin 6 → ℂ) ≃L[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)),
    ∀ x, e x = (
      (fun i => x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩),
      (fun i => if i.val = 1 then -x ⟨i.val, by omega⟩ + I * x ⟨i.val + 3, by omega⟩ else x ⟨i.val, by omega⟩ - I * x ⟨i.val + 3, by omega⟩)
    ) := by
  use local_chart_e.toContinuousLinearEquiv
  intro x
  rfl

lemma local_chart_matrix_analytic : AnalyticAt ℂ (fun x : Fin 6 → ℂ => (local_chart x).1.1) 0 := by
  have H : (fun x : Fin 6 → ℂ => (local_chart x).1.1) =
    fun x => spinorPhi_matrix
      (sl2c_chart_invFun (local_chart_e x).1)
      (sl2c_chart_invFun (local_chart_e x).2) := by
    ext x
    rfl
  rw [H]
  apply spinorPhi_matrix_analytic
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).1) 0 :=
      ContinuousLinearMap.analyticAt (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).1 = 0 := by ext i; simp [local_chart_e]
    exact AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1) (f := fun x => (local_chart_e x).1) (h0 ▸ h2) h1
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).2) 0 :=
      ContinuousLinearMap.analyticAt (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).2 = 0 := by ext i; simp [local_chart_e]
    exact AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1) (f := fun x => (local_chart_e x).2) (h0 ▸ h2) h1

lemma local_chart_analytic (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ) (z : Fin n → Fin 4 → ℂ)
  (hW_analytic : AnalyticAt ℂ W z) :
  AnalyticAt ℂ (fun x => W ((local_chart x) • z)) 0 := by
  have h_act_an : AnalyticAt ℂ (fun x => (local_chart x) • z) 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    have H2 : (fun x => ((local_chart x) • z) i j) = fun x => ∑ k : Fin 4, (local_chart x).1.1 j k * z i k := by
      ext x
      rfl
    rw [H2]

    have H_sum : (fun x => ∑ k : Fin 4, (local_chart x).1.1 j k * z i k) = fun x => (local_chart x).1.1 j 0 * z i 0 + (local_chart x).1.1 j 1 * z i 1 + (local_chart x).1.1 j 2 * z i 2 + (local_chart x).1.1 j 3 * z i 3 := by
      ext x
      simp [Fin.sum_univ_four]
    rw [H_sum]
    apply AnalyticAt.add
    · apply AnalyticAt.add
      · apply AnalyticAt.add
        · exact AnalyticAt.mul (analyticAt_matrix_elem4 local_chart_matrix_analytic j 0) analyticAt_const
        · exact AnalyticAt.mul (analyticAt_matrix_elem4 local_chart_matrix_analytic j 1) analyticAt_const
      · exact AnalyticAt.mul (analyticAt_matrix_elem4 local_chart_matrix_analytic j 2) analyticAt_const
    · exact AnalyticAt.mul (analyticAt_matrix_elem4 local_chart_matrix_analytic j 3) analyticAt_const
  have hz : (local_chart 0) • z = z := by
    have h1 : local_chart 0 = 1 := local_chart_zero
    rw [h1]
    exact one_smul _ z
  have hW_comp := AnalyticAt.comp (𝕜 := ℂ) (g := W) (f := fun x => (local_chart x) • z) (x := (0 : Fin 6 → ℂ))
  have hW_comp2 : AnalyticAt ℂ W ((local_chart 0) • z) := by
    rw [hz]
    exact hW_analytic
  exact hW_comp hW_comp2 h_act_an


instance instSigmaCompactMatrix2 : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → ℂ))

instance instLocallyCompactMatrix2 : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))

instance : SigmaCompactSpace (SpecialLinearGroup (Fin 2) ℂ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.sigmaCompactSpace

instance instLocallyCompactSL2C : LocallyCompactSpace (SpecialLinearGroup (Fin 2) ℂ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance : BaireSpace (SpecialLinearGroup (Fin 2) ℂ) :=
  BaireSpace.of_t2Space_locallyCompactSpace

instance instLocallyCompactMatrix4 : LocallyCompactSpace (Matrix (Fin 4) (Fin 4) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 4 → Fin 4 → ℂ))

instance instLocallyCompactGL : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 4) ℂ) :=
  inferInstance

lemma sscl_isClosed_in_GL : IsClosed (SpecialSpecialComplexLorentzGroup : Set (Matrix.GeneralLinearGroup (Fin 4) ℂ)) := by
  have h1 : Continuous (fun (Λ : Matrix.GeneralLinearGroup (Fin 4) ℂ) => (Λ.val)ᵀ * minkowskiMetric * Λ.val) := by
    exact Continuous.matrix_mul (Continuous.matrix_mul (Continuous.matrix_transpose Units.continuous_val) continuous_const) Units.continuous_val
  have h2 : Continuous (fun (Λ : Matrix.GeneralLinearGroup (Fin 4) ℂ) => (Λ.val).det) := by
    fun_prop
  have eq1 : IsClosed { Λ : Matrix.GeneralLinearGroup (Fin 4) ℂ | (Λ.val)ᵀ * minkowskiMetric * Λ.val = minkowskiMetric } :=
    isClosed_eq h1 continuous_const
  have eq2 : IsClosed { Λ : Matrix.GeneralLinearGroup (Fin 4) ℂ | (Λ.val).det = 1 } :=
    isClosed_eq h2 continuous_const
  exact IsClosed.inter eq1 eq2

instance instLocallyCompactSSCL : LocallyCompactSpace SpecialSpecialComplexLorentzGroup :=
  sscl_isClosed_in_GL.locallyCompactSpace

instance : SigmaCompactSpace SpecialSpecialComplexLorentzGroup := by
  have h_surj := spinorPhi_surjective
  have h_cont := continuous_spinorPhi
  have h_sigma := isSigmaCompact_range h_cont
  rw [Set.range_eq_univ.mpr h_surj] at h_sigma
  exact isSigmaCompact_univ_iff.mp h_sigma

instance : BaireSpace SpecialSpecialComplexLorentzGroup :=
  BaireSpace.of_t2Space_locallyCompactSpace

lemma spinorPhi_one : spinorPhi (1, 1) = 1 := by exact MonoidHom.map_one _

lemma spinorPhi_isOpenMap : IsOpenMap (fun p : SpecialLinearGroup (Fin 2) ℂ × SpecialLinearGroup (Fin 2) ℂ => spinorPhi p) := by
  apply MonoidHom.isOpenMap_of_sigmaCompact
  · exact spinorPhi_surjective
  · exact continuous_spinorPhi

lemma sl2c_chart_invFun_isOpenMap_at_zero (U : Set (Fin 3 → ℂ)) (hU : U ∈ 𝓝 0) :
    sl2c_chart_invFun '' U ∈ 𝓝 (1 : SpecialLinearGroup (Fin 2) ℂ) := by
  have h_open : IsOpen sl2c_chart_at_id_open_homeomorph.target := sl2c_chart_at_id_open_homeomorph.open_target
  have h0_mem : (0 : Fin 3 → ℂ) ∈ sl2c_chart_at_id_open_homeomorph.target := by
    dsimp [sl2c_chart_at_id_open_homeomorph]; norm_num
  rcases mem_nhds_iff.mp hU with ⟨V, hV_sub, hV_open, h0_V⟩
  let W := V ∩ sl2c_chart_at_id_open_homeomorph.target
  have hW_open : IsOpen W := IsOpen.inter hV_open h_open
  have h0_W : 0 ∈ W := ⟨h0_V, h0_mem⟩
  let H := sl2c_chart_at_id_open_homeomorph.symm
  have h_img_open : IsOpen (H '' W) := by
    exact H.isOpen_image_of_subset_source hW_open Set.inter_subset_right
  have h1_img : (1 : SpecialLinearGroup (Fin 2) ℂ) ∈ H '' W := by
    use 0; refine ⟨h0_W, ?_⟩
    change sl2c_chart_invFun 0 = 1
    exact sl2c_chart_invFun_zero
  have h_img_sub : H '' W ⊆ sl2c_chart_invFun '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hV_sub hx.1, rfl⟩
  exact mem_nhds_iff.mpr ⟨H '' W, h_img_sub, h_img_open, h1_img⟩
lemma local_chart_e_map_nhds_zero : Filter.map local_chart_e (𝓝 0) = 𝓝 0 := by
  have h0 : local_chart_e 0 = 0 := map_zero local_chart_e
  rw [← h0]
  exact Homeomorph.map_nhds_eq (ContinuousLinearEquiv.toHomeomorph local_chart_e.toContinuousLinearEquiv) 0
lemma local_chart_isOpenMap_at_zero_aux1 (U : Set (Fin 6 → ℂ)) (hU : U ∈ 𝓝 0) :
    local_chart_e '' U ∈ 𝓝 (0 : (Fin 3 → ℂ) × (Fin 3 → ℂ)) := by
  rw [← local_chart_e_map_nhds_zero]
  exact Filter.image_mem_map hU

lemma local_chart_isOpenMap_at_zero_aux2
    (UA UB : Set (Fin 3 → ℂ)) (hUA : UA ∈ 𝓝 0) (hUB : UB ∈ 𝓝 0) :
    spinorPhi '' ((sl2c_chart_invFun '' UA) ×ˢ (sl2c_chart_invFun '' UB)) ∈ 𝓝 (1 : SpecialSpecialComplexLorentzGroup) := by
  have hA := sl2c_chart_invFun_isOpenMap_at_zero UA hUA
  have hB := sl2c_chart_invFun_isOpenMap_at_zero UB hUB
  have h_prod : (sl2c_chart_invFun '' UA) ×ˢ (sl2c_chart_invFun '' UB) ∈ 𝓝 (1, 1) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hA hB
  have h_img := spinorPhi_isOpenMap.image_mem_nhds h_prod
  have hone : spinorPhi (1, 1) = 1 := spinorPhi_one
  rw [hone] at h_img
  exact h_img
lemma local_chart_isOpenMap_at_zero :
  ∀ U ∈ 𝓝 (0 : Fin 6 → ℂ), local_chart '' U ∈ 𝓝 (1 : SpecialSpecialComplexLorentzGroup) := by
  intro U hU
  have hU2_mem := local_chart_isOpenMap_at_zero_aux1 U hU
  rw [nhds_prod_eq] at hU2_mem
  rcases Filter.mem_prod_iff.mp hU2_mem with ⟨UA, hUA, UB, hUB, h_prod⟩
  have h_img := local_chart_isOpenMap_at_zero_aux2 UA UB hUA hUB
  have h_sub : spinorPhi '' ((sl2c_chart_invFun '' UA) ×ˢ (sl2c_chart_invFun '' UB)) ⊆ local_chart '' U := by
    rintro _ ⟨⟨A, B⟩, ⟨⟨a, ha, hA⟩, ⟨b, hb, hB⟩⟩, rfl⟩
    use local_chart_e.symm (a, b)
    have hab_mem : (a, b) ∈ local_chart_e '' U := h_prod ⟨ha, hb⟩
    rcases hab_mem with ⟨u, hu, hu_eq⟩
    rw [← hu_eq]
    rw [LinearEquiv.symm_apply_apply]
    refine ⟨hu, ?_⟩
    dsimp [local_chart]
    have h_a_eq : (fun i => u ⟨i.val, by omega⟩ + I * u ⟨i.val + 3, by omega⟩) = (local_chart_e u).1 := rfl
    have h_b_eq : (fun i => if i.val = 1 then -u ⟨i.val, by omega⟩ + I * u ⟨i.val + 3, by omega⟩ else u ⟨i.val, by omega⟩ - I * u ⟨i.val + 3, by omega⟩) = (local_chart_e u).2 := rfl
    rw [h_a_eq, h_b_eq, hu_eq]
    dsimp only at hA hB ⊢
    rw [hA, hB]
  exact Filter.mem_of_superset h_img h_sub

lemma local_orbit_identity (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
  ∀ᶠ Λ in 𝓝 (1 : SpecialSpecialComplexLorentzGroup), W (Λ • z) = W z := by
  have hW_an_z : AnalyticAt ℂ W z := hW_analytic.analyticAt ((forward_tube_n_isOpen n).mem_nhds hz)
  have hF_analytic : AnalyticAt ℂ (fun x => W (local_chart x • z)) 0 := local_chart_analytic n W z hW_an_z
  have hG_analytic : AnalyticAt ℂ (fun _ : Fin 6 → ℂ => W z) 0 := analyticAt_const

  have h_real_eq : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, W (local_chart (fun i => (x i : ℂ)) • z) = W z := by
    apply Eventually.of_forall
    intro x
    have ⟨Λ_R, hΛ_R⟩ := local_chart_real x
    rw [hΛ_R]
    exact hW_inv Λ_R z

  let my_ofRealN : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℂ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj i))
  have h_ofReal : ∀ x : Fin 6 → ℝ, my_ofRealN x = (fun i => (x i : ℂ)) := fun _ => rfl
  have h_eq_nhds := Analysis.analytic_nhds_eq_of_real_eq_N (fun x => W (local_chart x • z)) (fun _ => W z) 0 my_ofRealN h_ofReal hF_analytic hG_analytic h_real_eq

  rcases eventually_iff_exists_mem.mp h_eq_nhds with ⟨U, hU_nhds, hU_eq⟩
  have h_img_nhds := local_chart_isOpenMap_at_zero U hU_nhds

  apply eventually_iff_exists_mem.mpr
  use local_chart '' U
  constructor
  · exact h_img_nhds
  · intro Λ hΛ
    rcases hΛ with ⟨x, hx, hx_eq⟩
    rw [← hx_eq]
    exact hU_eq x hx



lemma complex_lorentz_identity_theorem (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
  ∀ Λ : SpecialSpecialComplexLorentzGroup, Λ • z ∈ forward_tube_n n → W (Λ • z) = W z := by
  intro Λ hΛ
  let D := orbit_domain n z
  have hD_conn : IsConnected D := is_connected_orbit_domain n z hz
  have hD_open : IsOpen D := orbit_domain_isOpen n z
  let u := { Λ' ∈ D | W (Λ' • z) = W z }
  let v := { Λ' ∈ D | W (Λ' • z) ≠ W z }

  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro Λ0 hΛ0
    have hz0 : Λ0 • z ∈ forward_tube_n n := hΛ0.1
    have hW_eq : W (Λ0 • z) = W z := hΛ0.2
    have h_loc := local_orbit_identity n W hW_inv hW_analytic (Λ0 • z) hz0
    have h_mult_cont : Continuous (fun Λ' : SpecialSpecialComplexLorentzGroup => Λ' * Λ0⁻¹) :=
      continuous_mul_const Λ0⁻¹
    have h_tendsto : Tendsto (fun Λ' => Λ' * Λ0⁻¹) (𝓝 Λ0) (𝓝 1) := by
      have h1 : Λ0 * Λ0⁻¹ = 1 := mul_inv_cancel _
      rw [← h1]
      exact h_mult_cont.tendsto Λ0
    have h_nhds := h_tendsto h_loc
    have h_D_nhds : D ∈ 𝓝 Λ0 := hD_open.mem_nhds hΛ0.1
    filter_upwards [h_nhds, h_D_nhds] with Λ' hΛ' hD'
    dsimp at hΛ'
    have h_act : (Λ' * Λ0⁻¹) • (Λ0 • z) = Λ' • z := by
      calc (Λ' * Λ0⁻¹) • (Λ0 • z) = ((Λ' * Λ0⁻¹) * Λ0) • z := (mul_smul _ _ _).symm
        _ = Λ' • z := by rw [inv_mul_cancel_right]
    rw [h_act] at hΛ'
    exact ⟨hD', by rw [hΛ', hW_eq]⟩

  have hv_open : IsOpen v := by
    have h_f_cont : Continuous (fun Λ' : SpecialSpecialComplexLorentzGroup => Λ' • z) := by
      exact (lorentz_action_continuous n).comp (continuous_id.prodMk continuous_const)
    have h_W_cont : ContinuousOn W (forward_tube_n n) := hW_analytic.continuousOn
    have h_comp_cont : ContinuousOn (fun Λ' => W (Λ' • z)) D := by
      apply ContinuousOn.comp h_W_cont h_f_cont.continuousOn
      intro Λ' hΛ'
      exact hΛ'
    have h_v_eq : v = D ∩ (fun Λ' => W (Λ' • z)) ⁻¹' {W z}ᶜ := by
      ext Λ'
      simp [v]
    rw [h_v_eq]
    have h_open_set : IsOpen {W z}ᶜ := isOpen_compl_singleton
    exact ContinuousOn.isOpen_inter_preimage h_comp_cont hD_open h_open_set

  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    intro Λ' hΛ'
    exact hΛ'.2.2 (hΛ'.1.2)

  have h_union : D ⊆ u ∪ v := by
    intro Λ' hΛ'
    by_cases h_eq : W (Λ' • z) = W z
    · left; exact ⟨hΛ', h_eq⟩
    · right; exact ⟨hΛ', h_eq⟩

  have h_nonempty : (D ∩ u).Nonempty := by
    use 1
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := by
      change (1 : SpecialSpecialComplexLorentzGroup) • z ∈ forward_tube_n n
      have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
      exact (congrArg (· ∈ forward_tube_n n) e).mpr hz
    have h2 : (1 : SpecialSpecialComplexLorentzGroup) ∈ u := ⟨h1, congrArg W (one_smul _ z)⟩
    exact ⟨h1, h2⟩

  have h_subset : D ⊆ u := hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have h_in_u : Λ ∈ u := h_subset hΛ
  exact h_in_u.2

lemma bhw_uniqueness_of_orbits (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (Λ : SpecialSpecialComplexLorentzGroup)
  (z1 z2 : Fin n → Fin 4 → ℂ)
  (hz1 : z1 ∈ forward_tube_n n) (hz2 : z2 ∈ forward_tube_n n)
  (h_eq : z2 = Λ • z1) :
  W z2 = W z1 := by
  rw [h_eq]
  have hz_Λ : Λ • z1 ∈ forward_tube_n n := by
    rw [← h_eq]
    exact hz2
  exact complex_lorentz_identity_theorem n W hW_inv hW_analytic z1 hz1 Λ hz_Λ

lemma W_ext_val_eq_of_mem_orbit (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (Λ : SpecialSpecialComplexLorentzGroup)
  (z z_in : Fin n → Fin 4 → ℂ)
  (hz_in : z_in ∈ forward_tube_n n)
  (h_eq : z = Λ • z_in) :
  W_ext_val n W hW_inv z = W z_in := by
  dsimp [W_ext_val]
  have hz : z ∈ extended_tube_n n := by
    dsimp [extended_tube_n]
    simp only [Set.mem_iUnion]
    use Λ
    simp only [Set.mem_image]
    use z_in
    exact ⟨hz_in, h_eq.symm⟩
  rw [dif_pos hz]
  let h_exists_Lambda := Set.mem_iUnion.mp hz
  let Λ_c := Classical.choose h_exists_Lambda
  let h_exists_z' := Classical.choose_spec h_exists_Lambda
  let z_c := Classical.choose h_exists_z'
  have hz_c_in : z_c ∈ forward_tube_n n := (Classical.choose_spec h_exists_z').1
  have hz_c_eq : z = Λ_c • z_c := (Classical.choose_spec h_exists_z').2.symm
  have h_eq2 : Λ_c • z_c = Λ • z_in := by rw [← hz_c_eq, h_eq]
  have h_z_c : z_c = (Λ_c⁻¹ * Λ) • z_in := by
    calc z_c = Λ_c⁻¹ • (Λ_c • z_c) := (inv_smul_smul Λ_c z_c).symm
      _ = Λ_c⁻¹ • (Λ • z_in) := by rw [h_eq2]
      _ = (Λ_c⁻¹ * Λ) • z_in := (mul_smul _ _ _).symm
  have h_W_eq : W z_c = W z_in := bhw_uniqueness_of_orbits n W hW_inv hW_analytic (Λ_c⁻¹ * Λ) z_in z_c hz_in hz_c_in h_z_c
  by_cases hz_fwd : z ∈ forward_tube_n n
  · rw [if_pos hz_fwd]


    exact bhw_uniqueness_of_orbits n W hW_inv hW_analytic Λ z_in z hz_in hz_fwd h_eq
  · rw [if_neg hz_fwd]
    exact h_W_eq


lemma W_ext_val_analytic (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n)) :
  AnalyticOn ℂ (W_ext_val n W hW_inv) (extended_tube_n n) := by
  intro z hz
  let h_exists_Lambda := Set.mem_iUnion.mp hz
  let Λ := Classical.choose h_exists_Lambda
  let h_exists_z' := Classical.choose_spec h_exists_Lambda
  let z_in := Classical.choose h_exists_z'
  have hz_in : z_in ∈ forward_tube_n n := (Classical.choose_spec h_exists_z').1
  have hz_eq : z = Λ • z_in := (Classical.choose_spec h_exists_z').2.symm


  let F : (Fin n → Fin 4 → ℂ) → ℂ := fun w => W (Λ⁻¹ • w)
  have hF_analytic : AnalyticAt ℂ F z := by
    have hz_inv : Λ⁻¹ • z = z_in := by
      calc Λ⁻¹ • z = Λ⁻¹ • (Λ • z_in) := by rw [hz_eq]
        _ = (Λ⁻¹ * Λ) • z_in := (mul_smul _ _ _).symm
        _ = (1 : SpecialSpecialComplexLorentzGroup) • z_in := by rw [inv_mul_cancel]
        _ = z_in := one_smul _ _
    have h_an_W : AnalyticAt ℂ W (Λ⁻¹ • z) := by
      rw [hz_inv]
      have h_nhds : forward_tube_n n ∈ 𝓝 z_in := (forward_tube_n_isOpen n).mem_nhds hz_in
      exact hW_analytic.analyticAt h_nhds
    let L : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun w => Λ⁻¹ • w
          map_add' := fun x y => smul_add _ _ _
          map_smul' := fun c x => by
            simp only [RingHom.id_apply]
            exact smul_comm _ _ _ }
    exact AnalyticAt.compContinuousLinearMap (u := L) (x := z) h_an_W



  have h_eq_near : ∀ᶠ w in 𝓝 z, F w = W_ext_val n W hW_inv w := by
    let L : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun w => Λ⁻¹ • w
          map_add' := fun x y => smul_add _ _ _
          map_smul' := fun c x => by
            simp only [RingHom.id_apply]
            exact smul_comm _ _ _ }
    have h_cont_L : Continuous L := L.continuous
    have h_open_inv : L ⁻¹' (forward_tube_n n) ∈ 𝓝 z := by
      apply Continuous.tendsto h_cont_L
      have h_L_z : L z = z_in := by
        calc L z = Λ⁻¹ • z := rfl
          _ = Λ⁻¹ • (Λ • z_in) := by rw [hz_eq]
          _ = (Λ⁻¹ * Λ) • z_in := (mul_smul _ _ _).symm
          _ = (1 : SpecialSpecialComplexLorentzGroup) • z_in := by rw [inv_mul_cancel]
          _ = z_in := one_smul _ _
      rw [h_L_z]
      exact (forward_tube_n_isOpen n).mem_nhds hz_in
    filter_upwards [h_open_inv] with w hw
    have hw_in : Λ⁻¹ • w ∈ forward_tube_n n := hw
    have hw_eq : w = Λ • (Λ⁻¹ • w) := by
      calc w = (1 : SpecialSpecialComplexLorentzGroup) • w := (one_smul _ w).symm
        _ = (Λ * Λ⁻¹) • w := by rw [mul_inv_cancel]
        _ = Λ • (Λ⁻¹ • w) := mul_smul _ _ _
    have h_val := W_ext_val_eq_of_mem_orbit n W hW_inv hW_analytic Λ w (Λ⁻¹ • w) hw_in hw_eq
    exact h_val.symm

  exact (hF_analytic.congr h_eq_near).analyticWithinAt




lemma bhw_uniqueness (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (W_ext1 W_ext2 : (Fin n → Fin 4 → ℂ) → ℂ)
  (h1_analytic : AnalyticOn ℂ W_ext1 (extended_tube_n n))
  (h1_eq : ∀ z ∈ forward_tube_n n, W_ext1 z = W z)
  (h2_analytic : AnalyticOn ℂ W_ext2 (extended_tube_n n))
  (h2_eq : ∀ z ∈ forward_tube_n n, W_ext2 z = W z) :
  Set.EqOn W_ext1 W_ext2 (extended_tube_n n) := by
  refine scv_identity_theorem n (extended_tube_n n) (extended_tube_is_open n) (extended_tube_is_connected n) W_ext1 W_ext2 h1_analytic h2_analytic (forward_tube_n n) (forward_tube_n_isOpen n) ?_ ?_ ?_
  · exact forward_tube_n_nonempty n
  · intro z hz
    dsimp [extended_tube_n]
    simp only [Set.mem_iUnion]
    use 1
    simp only [Set.mem_image]
    use z
    exact ⟨hz, one_smul _ _⟩
  · intro z hz
    rw [h1_eq z hz, h2_eq z hz]

lemma W_ext_val_eq_on_forward_tube (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W) :
  ∀ z ∈ forward_tube_n n, (W_ext_val n W hW_inv) z = W z := by
  intro z hz
  dsimp [W_ext_val]
  rw [if_pos hz]

lemma W_ext_val_is_complex_lorentz_invariant (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_inv : is_real_lorentz_invariant_n n W)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n)) :
  is_complex_lorentz_invariant_n n (W_ext_val n W hW_inv) := by
  intro Λ z
  by_cases hz : z ∈ extended_tube_n n
  · have hz_copy := hz
    dsimp [extended_tube_n] at hz_copy
    simp only [Set.mem_iUnion] at hz_copy
    rcases hz_copy with ⟨Λ_z, hz_in⟩
    simp only [Set.mem_image] at hz_in
    rcases hz_in with ⟨z_in, hz_in, hz_eq⟩

    have h1 : W_ext_val n W hW_inv z = W z_in := W_ext_val_eq_of_mem_orbit n W hW_inv hW_analytic Λ_z z z_in hz_in hz_eq.symm
    have h2 : W_ext_val n W hW_inv (Λ • z) = W z_in := by
      have hz_eq2 : Λ • z = (Λ * Λ_z) • z_in := by rw [← hz_eq]; exact (mul_smul Λ Λ_z z_in).symm
      exact W_ext_val_eq_of_mem_orbit n W hW_inv hW_analytic (Λ * Λ_z) (Λ • z) z_in hz_in hz_eq2
    exact h2.trans h1.symm
  · have h_Lambda_z_not : Λ • z ∉ extended_tube_n n := by
      intro h
      apply hz
      dsimp [extended_tube_n] at h ⊢
      simp only [Set.mem_iUnion] at h ⊢
      rcases h with ⟨Λ_z, hz_in⟩
      simp only [Set.mem_image] at hz_in ⊢
      rcases hz_in with ⟨z_in, hz_in, hz_eq⟩
      use Λ⁻¹ * Λ_z
      use z_in
      refine ⟨hz_in, ?_⟩
      calc (Λ⁻¹ * Λ_z) • z_in = Λ⁻¹ • (Λ_z • z_in) := mul_smul _ _ _
        _ = Λ⁻¹ • (Λ • z) := by rw [hz_eq]
        _ = z := inv_smul_smul Λ z
    have hz_fwd : z ∉ forward_tube_n n := fun h => hz (by
      dsimp [extended_tube_n]
      rw [Set.mem_iUnion]
      use (1 : SpecialSpecialComplexLorentzGroup)
      rw [Set.mem_image]
      use z
      exact ⟨h, one_smul _ _⟩
    )
    have hz_Lambda_fwd : Λ • z ∉ forward_tube_n n := fun h => h_Lambda_z_not (by
      dsimp [extended_tube_n]
      rw [Set.mem_iUnion]
      use (1 : SpecialSpecialComplexLorentzGroup)
      rw [Set.mem_image]
      use Λ • z
      exact ⟨h, one_smul _ _⟩
    )
    have h1 : W_ext_val n W hW_inv z = 0 := by
      dsimp [W_ext_val]
      rw [if_neg hz_fwd, dif_neg hz]
    have h2 : W_ext_val n W hW_inv (Λ • z) = 0 := by
      dsimp [W_ext_val]
      rw [if_neg hz_Lambda_fwd, dif_neg h_Lambda_z_not]
    exact h2.trans h1.symm





theorem bhw_theorem (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (hW_inv : is_real_lorentz_invariant_n n W) :
  ∃! (W_ext : (Fin n → Fin 4 → ℂ) → ℂ),
    AnalyticOn ℂ W_ext (extended_tube_n n) ∧
    is_complex_lorentz_invariant_n n W_ext ∧
    (∀ z ∈ forward_tube_n n, W_ext z = W z) ∧
    (∀ z ∉ extended_tube_n n, W_ext z = 0) := by
  use (W_ext_val n W hW_inv)
  constructor
  · 
    refine ⟨W_ext_val_analytic n W hW_inv hW_analytic,
            W_ext_val_is_complex_lorentz_invariant n W hW_inv hW_analytic,
            W_ext_val_eq_on_forward_tube n W hW_inv, ?_⟩
    intro z hz
    dsimp [W_ext_val]
    have hz_fwd : z ∉ forward_tube_n n := by
      intro h
      apply hz
      dsimp [extended_tube_n]
      simp only [Set.mem_iUnion]
      use 1
      simp only [Set.mem_image]
      use z
      exact ⟨h, one_smul _ _⟩
    rw [if_neg hz_fwd, dif_neg hz]
  · 
    intro W_ext2 h2
    ext z
    by_cases hz : z ∈ extended_tube_n n
    · have h1_analytic : AnalyticOn ℂ (W_ext_val n W hW_inv) (extended_tube_n n) := W_ext_val_analytic n W hW_inv hW_analytic
      have h1_eq : ∀ z ∈ forward_tube_n n, (W_ext_val n W hW_inv) z = W z := W_ext_val_eq_on_forward_tube n W hW_inv
      exact (bhw_uniqueness n W (W_ext_val n W hW_inv) W_ext2 h1_analytic h1_eq h2.1 h2.2.2.1 hz).symm
    · have h1_out : (W_ext_val n W hW_inv) z = 0 := by
        dsimp [W_ext_val]
        have hz_fwd : z ∉ forward_tube_n n := by
          intro h
          apply hz
          dsimp [extended_tube_n]
          simp only [Set.mem_iUnion]
          use 1
          simp only [Set.mem_image]
          use z
          exact ⟨h, one_smul _ _⟩
        rw [if_neg hz_fwd, dif_neg hz]
      rw [h1_out, h2.2.2.2 z hz]



theorem bhw_theorem_on_tube (n : ℕ) (W : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_analytic : AnalyticOn ℂ W (forward_tube_n n))
  (hW_inv : is_real_lorentz_invariant_n n W) :
  ∃ W_ext : (Fin n → Fin 4 → ℂ) → ℂ,
    AnalyticOn ℂ W_ext (extended_tube_n n) ∧
    (∀ (Λ : SpecialSpecialComplexLorentzGroup), ∀ z ∈ extended_tube_n n, W_ext (Λ • z) = W_ext z) ∧
    (∀ z ∈ forward_tube_n n, W_ext z = W z) ∧
    (∀ W' : (Fin n → Fin 4 → ℂ) → ℂ,
      AnalyticOn ℂ W' (extended_tube_n n) →
      (∀ z ∈ forward_tube_n n, W' z = W z) →
      Set.EqOn W_ext W' (extended_tube_n n)) := by
  refine ⟨W_ext_val n W hW_inv, W_ext_val_analytic n W hW_inv hW_analytic,
    fun Λ z _ => W_ext_val_is_complex_lorentz_invariant n W hW_inv hW_analytic Λ z,
    W_ext_val_eq_on_forward_tube n W hW_inv, ?_⟩
  intro W' h_an h_eq z hz
  exact bhw_uniqueness n W (W_ext_val n W hW_inv) W' (W_ext_val_analytic n W hW_inv hW_analytic)
    (W_ext_val_eq_on_forward_tube n W hW_inv) h_an h_eq hz







theorem wightman_analytic_at_jost_points (n : ℕ) (hn : n > 1)
  (W_ext : (Fin n → Fin 4 → ℂ) → ℂ)
  (hW_ext_analytic : AnalyticOn ℂ W_ext (extended_tube_n n))
  (x : Fin n → Fin 4 → ℝ) (hx_jost : x ∈ jost_points_n n) :
  
  ∃ U : Set (Fin n → Fin 4 → ℂ), IsOpen U ∧ (coeReal n x ∈ U) ∧ AnalyticOn ℂ W_ext U := by
  
  
  
  
  use extended_tube_n n
  refine ⟨extended_tube_is_open n, ?_, hW_ext_analytic⟩
  exact (jost_theorem n x hn).mp hx_jost


end QFT
